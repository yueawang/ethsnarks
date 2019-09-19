/*
 This ceremony constructs the "powers of tau" for Jens Groth's 2016 zk-SNARK proving
 system using the BLS12-381 pairing-friendly elliptic curve construction.

 # Overview

 Participants of the ceremony receive a "challenge" file containing:

 * the BLAKE2b hash of the last file entered into the transcript
 * an `Accumulator` (with curve points encoded in uncompressed form for fast deserialization)

 The participant runs a tool which generates a random keypair (`PublicKey`, `PrivateKey`)
 used for modifying the `Accumulator` from the "challenge" file. The keypair is then used to
 transform the `Accumulator`, and a "response" file is generated containing:

 * the BLAKE2b hash of the "challenge" file (thus forming a hash chain over the entire transcript)
 * an `Accumulator` (with curve points encoded in compressed form for fast uploading)
 * the `PublicKey`

 This "challenge" file is entered into the protocol transcript. A given transcript is valid
 if the transformations between consecutive `Accumulator`s verify with their respective
 `PublicKey`s. Participants (and the public) can ensure that their contribution to the
 `Accumulator` was accepted by ensuring the transcript contains their "response" file, ideally
 by comparison of the BLAKE2b hash of the "response" file.

 After some time has elapsed for participants to contribute to the ceremony, a participant is
 simulated with a randomness beacon. The resulting `Accumulator` contains partial zk-SNARK
 public parameters for all circuits within a bounded size.
*/


#define _FILE_OFFSET_BITS 64

#include <unistd.h>
#include <stdint.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include "ethsnarks.hpp"
#include "crypto/blake2b.h"
#include "crypto/chacharng.hpp"


using ethsnarks::G1T;
using ethsnarks::G2T;
using ethsnarks::FqT;
using ethsnarks::Fq2T;
using ethsnarks::ppT;
using ethsnarks::FqT_size_bytes;
using libff::bigint;


constexpr size_t HASH_SIZE = 64;

// TODO: use std::array
typedef uint8_t digest_t[64];


template<long N>
static void hash(blake2b_ctx &ctx, const bigint<N> &bi )
{
    mpz_t x;
    mpz_init(x);
    bi.to_mpz(x);

    // XXX: Conversion to big-endian form
    constexpr size_t count = sizeof(mp_limb_t) * N;
    uint8_t output[count];
    mpz_export(
        output,             // rop
        NULL,               // countp
        1,                  // order
        sizeof(mp_limb_t),  // size
        1,                  // endian
        0,                  // nails
        x);                 // op

    blake2b_update(&ctx, output, count);
}


template<typename H>
static void hash(H &ctx, const FqT &field)
{
    hash(ctx, field.as_bigint());
}


template<typename H>
static void hash(H &ctx, const Fq2T &field)
{
    hash(ctx, field.c0);
    hash(ctx, field.c1);
}


template<typename H, typename T>
static void hash_uncompressed(H &ctx, const T& point)
{
    T point_copy;
    point_copy.to_affine_coordinates();
    hash(ctx, point.X);
    hash(ctx, point.Y);
}


template<long N>
static int cmp( const bigint<N> &a, const bigint<N> &b )
{
    return mpn_cmp( a.data, b.data, N );
}


static int cmp( const FqT &a, const FqT &b )
{
    const auto a_bi = a.as_bigint();
    const auto b_bi = b.as_bigint();
    return cmp(a_bi, b_bi);
}


/** `Fq2` elements are ordered lexicographically. */
static int cmp( const Fq2T &a, const Fq2T &b )
{
    auto res = cmp(a.c1, b.c1);
    if( res == 0 ) {
        return cmp(a.c0, b.c0);
    }
    return res;
}



template<long N>
static bool test_and_clear_bit( bigint<N> &bi, int bitno )
{
    if( bitno >= (N * GMP_NUMB_BITS) ) {
        return false;
    }
    const mp_limb_t one = 1;
    const size_t part = bitno/GMP_NUMB_BITS;
    const size_t bit = bitno - (GMP_NUMB_BITS*part);
    const size_t mask = (one<<bit);
    const bool flag = (bi.data[part] & mask) != 0;
    if( flag ) {
        bi.data[part] ^= mask;
    }
    return flag;
}


template<typename R, long N>
static void rand_bigint( R &rng, bigint<N> &bi )
{
    for( int i = 0; i < N; i++ ) {
        bi.data[i] = rng.next_u64();            
    }
}


/** Computes a uniformly random element (in montgomery form) using rejection sampling. */
template<typename R>
static void rand_field( R &rng, FqT &out )
{
    // Load random data directly into montgomery form, no reduction
    while( 1 )
    {
        rand_bigint(rng, out.mont_repr);

        const size_t REPR_SHAVE_BITS = (FqT::mod.max_bits() - FqT::mod.num_bits());
        const mp_limb_t one = 1;
        out.mont_repr.data[FqT::num_limbs-1] &= ((one<<(GMP_NUMB_BITS-REPR_SHAVE_BITS))-1);

        // Reject samples if they >= modulus
        // XXX: comparing the montgomery form with the modulus (in non-montgomery form)
        const auto cmp_result = mpn_cmp( out.mont_repr.data, FqT::mod.data, FqT::num_limbs );
        if( cmp_result < 0 ) {
            break;
        }
    }
}


template<typename R>
static void rand_field( R &rng, Fq2T &out )
{
    rand_field(rng, out.c0);
    rand_field(rng, out.c1);
}


/** Norm of Fp2 over Fp: Norm(a) = a.x^2 - beta * a.y^2 */
static FqT norm( const Fq2T &a )
{
    const auto t0 = a.c0.squared();
    const auto t1 = a.c1.squared();
    return -(Fq2T::non_residue * t1) + t0;
}


static int legendre( const FqT &a )
{
    // s = self^((MODULUS - 1) // 2)
    const auto s = a^FqT::euler;
    if( s.is_zero() ) {
        return 0;
    }
    else if( s == FqT::one() ) {
        return 1;
    }
    return -1;
}


static int legendre( const Fq2T &a ) {
    return legendre(norm(a));
}


template<typename T>
static bool is_quadratic_residue( const T &x )
{
    return legendre(x) != -1;
}


/** Determine if the intended y coordinate must be greater lexicographically. */
template<typename T>
static T conditional_flip( const T &Y, bool choose_greatest )
{
    const auto negY = -Y;
    if( choose_greatest == (cmp(Y, negY) >= 0) ) {
        return Y;
    }
    return negY;
}


static FqT ysq_from_x( const FqT& X )
{
    return (X.squared()*X) + libff::alt_bn128_coeff_b;   
}


static Fq2T ysq_from_x( const Fq2T& X )
{
    return (X.squared()*X) + libff::alt_bn128_twist_coeff_b;   
}


template<typename T>
static bool has_valid_y( const T &X )
{
    return is_quadratic_residue(ysq_from_x(X));
}


template<typename T>
static bool recover_y_from_x( const T &X, T &Y )
{
    const auto Y2 = ysq_from_x(X);
    if( is_quadratic_residue(Y2) ) {
        Y = Y2.sqrt();
        return true;
    }
    return false;
}


template<typename T>
static bool recover_y_from_x( const T &X, T &Y, const bool choose_greatest )
{
    if( recover_y_from_x(X, Y) ) {
        Y = conditional_flip(Y, choose_greatest);
        return true;
    }
    return false;
}


static void scale_by_cofactor( G1T &point ) {
    // G1 has no cofactor
}


static void scale_by_cofactor( libff::alt_bn128_G2 &point ) {
    // cofactor for Fp2 = (2*q) - r
    // XXX: need N+1 limbs for cofactor?
    static const decltype(Fq2T::euler) cofactor("21888242871839275222246405745257275088844257914179612981679871602714643921549");
    point = cofactor * point;
}


template<typename R, typename T>
static void rand_point( R &rng, T &point )
{
    point.Z = decltype(point.Z)::one();
    while( 1 )
    {
        rand_field(rng, point.X);
        const auto greatest = rng.next_bit();
        if( recover_y_from_x( point.X, point.Y, greatest ) ) {
            scale_by_cofactor(point);
            break;
        }
    }
}


// TODO: specify size of data
ChaChaRng<20> rng_from_seed( const uint8_t *data )
{
    // hash_to_g2 in Rust parses seed as sequence of big-endian uint32_t ¯\_(ツ)_/¯
    mpz_t rop;
    mpz_init(rop);
    mpz_import(rop, 8, 1, sizeof(uint32_t), 1, 0, data);
    // mpz parses into 64bit words... unparse into 32-bit words...
    // this matches the same order as the Rust code
    uint32_t seed[8];
    assert( sizeof(mp_limb_t) == sizeof(uint64_t) );
    for( int i = 0; i < 4; i++ ) {
        seed[(2*i)] = (rop->_mp_d[3-i] >> 32);
        seed[(2*i)+1] = (rop->_mp_d[3-i] & 0xFFFFFFFF);
    }

    return ChaChaRng<20>(seed);
}


// TODO: specify size of data
static void hash_to_g2(const uint8_t *data, G2T &point)
{
    auto rng = rng_from_seed(data);
    rand_point(rng, point);
    point.to_affine_coordinates();
}


/** Reads an n-limb big integer, in its standard form (without montgomery reduction) */
template<long N>
static const uint8_t* parse_bigint( const uint8_t *data, bigint<N> &bi )
{
    assert( data != nullptr );
    if( data != nullptr ) {
        // XXX: slow conversion from big-endian form to little-end
        mpz_t rop;
        mpz_init(rop);
        mpz_import(rop, N, 1, sizeof(mp_limb_t), 1, 0, data);
        bi = bigint<N>(rop);
        return &data[FqT_size_bytes];
    }
    return nullptr;
}


/** Parses a field element in its n-limb big integer form
Then converts into montgomery form
Field element is in big-endian form, so must be parsed using mpz_import */
static const uint8_t* parse_field( const uint8_t *data, FqT &field )
{
    assert( data != nullptr );
    if( data != nullptr )
    {
        bigint<FqT::num_limbs> x;
        data = parse_bigint(data, x);
        field = FqT(x); // XXX: slow conversion to montgomery form
    }
    return data;
}


/** Parses a field element (converts into montgomery form)
Coefficients are in big-endian form (c1, then c0) */
static const uint8_t* parse_field( const uint8_t *data, Fq2T &field )
{
    assert( data != nullptr );
    if( data != nullptr )
    {
        data = parse_field(data, field.c1);
        return parse_field(data, field.c0);
    }
    return nullptr;
}


/** Parses an uncompressd G1 point (from its byte-representation in from memory) */
template<typename T>
static const uint8_t* parse_point_uncompressed( const uint8_t *data, T &point )
{
    assert( data != nullptr );
    if( data != nullptr )
    {
        data = parse_field(data, point.X);
        data = parse_field(data, point.Y);
        point.Z = decltype(point.Z)::one();
    }
    return data;
}


/** Parses a compressd G1 point (from its byte-representation in from memory) */
static const uint8_t* parse_point_compressed( const uint8_t *data, G1T &point )
{
    assert( data != nullptr );
    if( data == nullptr )
        return nullptr;

    bigint<FqT::num_limbs> bi;
    data = parse_bigint(data, bi);
    assert( data != nullptr );
    if( data == nullptr ) {
        return nullptr;
    }

    const bool is_zero = test_and_clear_bit(bi, 254);
    const bool greatest = test_and_clear_bit(bi, 255);
    if( is_zero ) {
        // Verify the remaining data is all zeros
        for( int i = 0; i < FqT::num_limbs; i++ ) {
            assert( bi.data[i] == 0 );
        }
        point = G1T::zero();
        return data;
    }

    point.X = FqT(bi);  // XXX: slow conversion to montgomery form
    if( ! recover_y_from_x(point.X, point.Y, greatest) ) {
        return nullptr;
    }
    point.Z = decltype(point.Z)::one();

    return data;
}


/** Parses an compressd G2 point (from its byte-representation in from memory) */
static const uint8_t* parse_point_compressed( const uint8_t *data, G2T &point )
{
    assert( data != nullptr );
    if( data == nullptr ) {
        return nullptr;
    }

    bigint<FqT::num_limbs> c1;
    bigint<FqT::num_limbs> c0;
    data = parse_bigint(data, c1);
    data = parse_bigint(data, c0);

    const bool is_zero = test_and_clear_bit(c1, 254);
    const bool greatest = test_and_clear_bit(c1, 255);

    if( is_zero ) {
        // Verify the remaining data is all zeros
        for( int i = 0; i < FqT::num_limbs; i++ ) {
            assert( c1.data[i] == 0 );
            assert( c0.data[i] == 0 );
        }
        point = G2T::zero();
    }
    else {
        const Fq2T X(c0, c1);   // XXX: slow conversion to montgomery form for each co-efficient
        if( ! recover_y_from_x(X, point.Y, greatest) ) {
            return nullptr;
        }
        point.X = X;
        point.Z = decltype(point.Z)::one();
    }

    return data;
}


/**
Checks if pairs have the same ratio.
Under the hood uses pairing to check
x1/x2 = y1/y2 => x1*y2 = x2*y1
*/
bool same_ratio( const G1T& x1, const G1T& x2, const G2T& y1, const G2T& y2 )
{
    // g1.0.pairing_with(&g2.1) == g1.1.pairing_with(&g2.0)
    const auto a = ppT::pairing(x1, y2);
    const auto b = ppT::pairing(-x2, y1);
    const auto c = a*b;
    printf("a:");
    a.print();
    printf("\n");
    printf("b:");
    b.print();
    printf("\n");
    printf("c:");
    c.print();
    printf("\n");
    return a == b;

}


/** Wrapper around memory-mapped files, with auto-close and easy writeable flag */
class MappedFile {
protected:
    const std::string m_filename;
    bool m_writeable;
    bool m_is_open {false};
    void *m_data {nullptr};
    int m_fd {-1};
    struct stat m_statbuf {0};

public:
    MappedFile(const char *filename, bool writeable = false)
    :
        m_filename(filename),
        m_writeable(writeable)
    {
        assert( filename != nullptr );
    }

    ~MappedFile()
    {
        if ( m_is_open ) {
            this->close();
        }
    }

    size_t size () const
    {
        assert( m_is_open == true );
        if ( m_is_open ) {
            return (size_t)m_statbuf.st_size;
        }
        return 0;
    }

    bool is_open () const
    {
        return m_is_open;
    }

    bool close ()
    {
        assert( m_is_open == true );
        if ( m_is_open )
        {
            if ( ::munmap(m_data, this->size()) != 0 ) {
                ::perror("Could not unmap challenge file");
            }
            ::close(m_fd);
            m_data = nullptr;
            m_is_open = false;
            m_fd = -1;
            return true;
        }
        return false;
    }

    uint8_t* data (size_t offset = 0) const
    {
        assert( m_is_open == true );
        if ( m_is_open )
        {
            assert( offset < this->size() );
            uint8_t *data = (uint8_t*)m_data;
            return &data[offset];
        }
        return nullptr;
    }

    bool open (size_t expected_size = 0)
    {
        assert( m_is_open == false );

        if ( ! m_is_open )
        {
            int flags = m_writeable ? (O_RDWR|O_CREAT|O_TRUNC) : O_RDONLY;
            int fd = ::open(m_filename.c_str(), O_RDONLY);
            if ( fd == -1 ) {
                ::perror("Could not open challenge file");
                return false;
            }

            if ( expected_size != 0 ) {
                if( -1 == ftruncate(fd, expected_size) ) {
                    ::perror("Could not extend file to expected size!");
                    ::close(fd);
                    return false;
                }
            }

            if ( ::fstat(fd, &m_statbuf) == -1 ) {
                ::perror("Could not stat challenge file");
                ::close(fd);
                return false;
            }

            size_t file_size = (size_t)m_statbuf.st_size;
            int prot = PROT_READ;
            if( m_writeable ) {
                prot |= PROT_WRITE;
            }
            void *data = ::mmap(NULL, file_size, prot, MAP_SHARED, fd, 0);
            if ( data == (void*)-1 ) {
                ::perror("Could not mmap challenge file");
                ::close(fd);
                return false;
            }

            m_data = data;
            m_fd = fd;
            m_is_open = true;

            // Eager sequential reading...
            if ( ::madvise(m_data, file_size, MADV_SEQUENTIAL|MADV_WILLNEED) == -1 ) {
                ::perror("Could not run madvise");
            }
        }

        return true;
    }
};


static const size_t G1_UNCOMPRESSED_BYTE_SIZE = (FqT_size_bytes * 2);  // X and Y coordinates
static const size_t G2_UNCOMPRESSED_BYTE_SIZE = (FqT_size_bytes * 4);  // X[0,1] and Y[0,1] coordinates
static const size_t G1_COMPRESSED_BYTE_SIZE = FqT_size_bytes;          // Y coordinate is a sign bit
static const size_t G2_COMPRESSED_BYTE_SIZE = (FqT_size_bytes * 2);    // 


enum ElementType {
    TauG1,
    TauG2,
    AlphaG1,
    BetaG1,
    BetaG2
};


template<size_t N>
const G2T compute_g2_s(const uint8_t (&digest)[N], const G1T &g1_s, const G1T &g1_s_x, const uint8_t personalization)
{
    blake2b_ctx ctx;
    if( blake2b_init(&ctx, N, NULL, 0) != 0 ) {
        assert(false);
        return G2T::zero();
    }

    blake2b_update(&ctx, &personalization, 1);
    blake2b_update(&ctx, digest, N);

    hash_uncompressed(ctx, g1_s);
    hash_uncompressed(ctx, g1_s_x);

    uint8_t output[N];
    blake2b_final(&ctx, output);

    G2T result;
    hash_to_g2(output, result);
    return result;
}


/** Displays a nicely formatted and easily readable hash */
template<size_t N=HASH_SIZE>
static void print_hash(uint8_t *data, const char *line_prefix = "\t")
{
    assert( N % 16 == 0 );
    for ( size_t i = 0; i < N; i += 16 )
    {
        printf("%s", line_prefix);
        for ( size_t j = i; j < (i+16); j++)
        {
            if ( j != i && (j%4) == 0 ) {
                printf(" ");
            }
            printf("%02x", data[j]);
        }
        printf("\n");
    }
}


void print(const G2T &p)
{
    // XXX: make affine?
    const auto p_x_c0 = p.X.c0.as_bigint();
    const auto p_x_c1 = p.X.c1.as_bigint();
    const auto p_y_c0 = p.Y.c0.as_bigint();
    const auto p_y_c1 = p.Y.c1.as_bigint();

    gmp_printf("G2(x=Fq2(Fq(0x%064Nx) + Fq(0x%064Nx) * u), y=Fq2(Fq(0x%064Nx) + Fq(0x%064Nx) * u))",
        p_x_c0.data, FqT::num_limbs,
        p_x_c1.data, FqT::num_limbs,
        p_y_c0.data, FqT::num_limbs,
        p_y_c1.data, FqT::num_limbs);
}


void print(const G1T &p)
{
    // XXX: make affine?
    const auto p_x = p.X.as_bigint();
    const auto p_y = p.Y.as_bigint();
    gmp_printf("G1(Fq(0x%064Nx), Fq(0x%064Nx))", p_x.data, FqT::num_limbs, p_y.data, FqT::num_limbs);
}


void _require( const char *filename, int line, const bool x, const char *msg = nullptr )
{
    assert( x );
    if( ! x ) {
        printf("Requirement failed on %s:%d\n", filename, line);
        if( msg != nullptr ) {
            printf("\t%s", msg);
        }
    }
}


#define REQUIRE(...) _require(__FILE__, __LINE__, __VA_ARGS__)


class KeyRelation {
public:
    G1T g1_s;
    G1T g1_s_x;
    G2T g2_s_x;

    /** Check proof of knowledge */
    // g1^s / g1^(s*x) = g2^s / g2^(s*x)
    template<size_t N>
    bool verify( const uint8_t (&digest)[N], const uint8_t personalization )
    {
        const auto g2_s = compute_g2_s(digest, g1_s, g1_s_x, personalization);
        return same_ratio(g1_s, g1_s_x, g2_s, g2_s_x);
    }
};


class PublicKey {
public:
    KeyRelation tau;
    KeyRelation alpha;
    KeyRelation beta;

    static size_t size() {
        return (G1_UNCOMPRESSED_BYTE_SIZE*6) + (G2_UNCOMPRESSED_BYTE_SIZE*3);
    }

    static bool parse( const uint8_t *data, PublicKey &self )
    {
        data = parse_point_uncompressed(data, self.tau.g1_s);
        data = parse_point_uncompressed(data, self.tau.g1_s_x);
        data = parse_point_uncompressed(data, self.alpha.g1_s);
        data = parse_point_uncompressed(data, self.alpha.g1_s_x);
        data = parse_point_uncompressed(data, self.beta.g1_s);
        data = parse_point_uncompressed(data, self.beta.g1_s_x);
        data = parse_point_uncompressed(data, self.tau.g2_s_x);
        data = parse_point_uncompressed(data, self.alpha.g2_s_x);
        data = parse_point_uncompressed(data, self.beta.g2_s_x);
        assert( data != nullptr );
        return data != nullptr;
    }

    /** Re-compute the G2 components deterministially */
    template<size_t N>
    bool verify( const uint8_t (&digest)[N] )
    {
        if( ! tau.verify(digest, 0) ) {
            printf("Public Key Tau mismatch!\n");
            return false;
        }

        if( ! alpha.verify(digest, 1) ) {
            printf("Public Key Alpha mismatch!\n");
            return false;
        }

        if( ! beta.verify(digest, 2) ) {
            printf("Public Key Beta mismatch!\n");
            return false;
        }

        return true;
    }
};


static void print( const KeyRelation &key )
{
    printf("\tg1_s: ");
    print(key.g1_s);
    printf("\n");

    printf("\tg1_s_x: ");
    print(key.g1_s_x);
    printf("\n");

    printf("\tg2_s_x: ");
    print(key.g2_s_x);
    printf("\n\n");
}


static void print( const PublicKey &pk )
{
    printf("Tau:\n");
    print(pk.tau);

    printf("Alpha:\n");
    print(pk.alpha);

    printf("Beta:\n");
    print(pk.beta);
}


class AccumulatorFile {
public:
    int m_npowers;
    bool m_is_writeable;
    bool m_is_compressed;
    bool m_with_pubkey;
    MappedFile m_handle;

    size_t tau_powers_count;
    size_t tau_powers_g1_count;

    size_t hash_offset;
    size_t hash_end;
    size_t tau_powers_g1_offset;
    size_t tau_powers_g1_end;
    size_t tau_powers_g2_offset;
    size_t tau_powers_g2_end;
    size_t alpha_tau_powers_g1_offset;
    size_t alpha_tau_powers_g1_end;
    size_t beta_tau_powers_g1_offset;
    size_t beta_tau_powers_g1_end;
    size_t beta_g2_offset;
    size_t beta_g2_end;
    size_t pubkey_offset;
    size_t pubkey_size;
    size_t pubkey_end;

    AccumulatorFile(
        int npowers,
        const char *filename,
        bool writeable = false,
        bool compressed = false,
        bool with_pubkey = false
    ) :
        m_npowers(npowers),
        m_is_writeable(writeable),
        m_is_compressed(compressed),
        m_with_pubkey(with_pubkey),
        m_handle(filename, writeable),
        tau_powers_count(1<<npowers),
        tau_powers_g1_count((tau_powers_count<<1) - 1)
    {
        assert( npowers > 0 && npowers <= 28 );

        hash_offset = 0;
        hash_end = tau_powers_g1_offset = HASH_SIZE;
        tau_powers_g2_offset = tau_powers_g1_end = tau_powers_g1_offset + (g1_size() * tau_powers_g1_count);
        alpha_tau_powers_g1_offset = tau_powers_g2_end = tau_powers_g2_offset + (g2_size() * tau_powers_count);
        beta_tau_powers_g1_offset = alpha_tau_powers_g1_end = alpha_tau_powers_g1_offset + (g1_size() * tau_powers_count);
        beta_g2_offset = beta_tau_powers_g1_end = beta_tau_powers_g1_offset + (g1_size() * tau_powers_count);
        pubkey_offset = beta_g2_end = beta_g2_offset + g2_size();
        pubkey_size = PublicKey::size();
        pubkey_end = pubkey_offset + pubkey_size;
    }

    ~AccumulatorFile() {
        m_handle.close();
    }

    bool has_pubkey() const {
        return m_with_pubkey;
    }

    template<size_t N>
    const bool hash_to( uint8_t (&result)[N] ) const
    {
        assert( this->is_open() );
        if( this->is_open() ) {
            blake2b_ctx ctx;
            if( blake2b_init(&ctx, N, NULL, 0) != 0 ) {
                assert(false);
                return false;
            }
            blake2b_update(&ctx, this->data(), this->m_handle.size());
            blake2b_final(&ctx, result);
            return true;
        }
        return false;
    }

    bool open()
    {
        if( m_handle.is_open() ) {
            return false;
        }

        size_t x = 0;
        if( m_is_writeable ) {
            // When writing, expand/truncate file to expected size
            x = this->expected_size();
        }

        if( ! m_handle.open(x) ) {
            return false;
        }

        if( m_handle.size() != this->expected_size() ) {
            fprintf(stderr, "Error: actual size doesn't match expected size\n");
            fprintf(stderr, "       actual size: %zu\n", m_handle.size());
            fprintf(stderr, "       expected size: %zu\n", this->expected_size());
            m_handle.close();
            return false;
        }

        return true;
    }

    bool is_open() const {
        return m_handle.is_open();
    }

    bool is_expected_size() const {
        assert( this->is_open() );
        return m_handle.size() == this->expected_size();
    }

    size_t expected_size() const {
        if( m_with_pubkey ) {
            return pubkey_end;
        }
        return beta_g2_end;
    }

    size_t size() const {
        assert( this->is_open() );
        return m_handle.size();
    }

    uint8_t* data() const {
        assert( this->is_open() );
        return m_handle.data();
    }

    size_t g1_size(const bool force_uncompressed = false) const {
        if( force_uncompressed ) {
            return G1_UNCOMPRESSED_BYTE_SIZE;
        }
        return m_is_compressed ? G1_COMPRESSED_BYTE_SIZE : G1_UNCOMPRESSED_BYTE_SIZE;
    }

    size_t g2_size(const bool force_uncompressed = false) const {
        if( force_uncompressed ) {
            return G2_UNCOMPRESSED_BYTE_SIZE;
        }
        return m_is_compressed ? G2_COMPRESSED_BYTE_SIZE : G2_UNCOMPRESSED_BYTE_SIZE;
    }

    template<typename T>
    bool _parse_point( const size_t offset, T &point, const bool force_uncompressed = false ) const
    {
        assert( this->is_open() );
        const uint8_t *data;
        if( ! force_uncompressed && this->m_is_compressed ) {
            data = parse_point_compressed(m_handle.data() + offset, point);
        }
        else {
            data = parse_point_uncompressed(m_handle.data() + offset, point);
        }
        assert( data != nullptr );
        return data != nullptr && point.is_well_formed();
    }

    bool get_element( const ElementType t, const size_t idx, G1T& p ) const
    {
        assert( t == ElementType::TauG1 || t == ElementType::AlphaG1 || t == ElementType::BetaG1 );
        switch( t ) {
        case ElementType::TauG1:
            return this->get_tauG1(idx, p);
        case ElementType::AlphaG1:
            return this->get_alphaG1(idx, p);
        case ElementType::BetaG1:
            return this->get_betaG1(idx, p);
        default:
            assert( false );
            return false;
        }
    }

    bool get_element( const ElementType t, const size_t idx, G2T& p ) const
    {
        assert( t == ElementType::TauG2 || t == ElementType::BetaG2 );
        switch( t ) {
        case ElementType::TauG2:
            return this->get_tauG2(idx, p);
        case ElementType::BetaG2:
            assert( idx == 0 );
            if( idx == 0 ) {
                return this->get_betaG2(p);
            }
            return false;
        default:
            assert( false );
            return false;
        }
    }

    uint8_t *get_hash_ptr() const
    {
        if( this->is_open() ) {
            return this->data();
        }
        return nullptr;
    }

    bool get_hash( uint8_t (&output)[HASH_SIZE] ) const
    {
        if( this->is_open() ) {
            memcpy(output, this->data(), HASH_SIZE);
            return true;
        }
        return false;
    }

    bool get_tauG1( const size_t idx, G1T &point ) const
    {
        assert( idx < tau_powers_g1_count );
        if( idx < tau_powers_g1_count ) {
            return _parse_point(tau_powers_g1_offset + (g1_size() * idx), point);
        }
        return false;
    }

    bool get_tauG2( const size_t idx, G2T &point ) const
    {
        assert( idx < tau_powers_count );
        if( idx < tau_powers_count ) {
            return _parse_point(tau_powers_g2_offset + (g2_size() * idx), point);
        }
        return false;
    }

    bool get_alphaG1( const size_t idx, G1T &point ) const
    {
        assert( idx < tau_powers_count );
        if( idx < tau_powers_count ) {
            return _parse_point(alpha_tau_powers_g1_offset + (g1_size() * idx), point);
        }
        return false;
    }

    bool get_betaG1( const size_t idx, G1T &point ) const
    {
        assert( idx < tau_powers_count );
        if( idx < tau_powers_count ) {
            return _parse_point(beta_tau_powers_g1_offset + (g1_size() * idx), point);
        }
        return false;
    }

    bool get_betaG2( G2T &point ) const {
        return _parse_point(beta_g2_offset, point);
    }

    bool get_pubkey( PublicKey &key ) const
    {
        if( this->is_open() && m_with_pubkey ) {
            const uint8_t *pkoffset = this->data() + this->pubkey_offset;
            return PublicKey::parse(pkoffset, key);
        }
        return false;
    }
};


template<typename T>
static void print_many_points( const ElementType t, const AccumulatorFile &acc, const size_t begin, const size_t end )
{
    T p;
    for( size_t i = begin; i < end; i++ ) {
        if( ! acc.get_element(t, i, p) ) {
            printf("Failed to read point %zu\n", i);
            continue;
        }
        printf("%zu = ", i);
        print(p);
        printf("\n");
    }
}


static int cmd_print_challenge ( int n_powers, int argc, char **argv )
{
    if ( argc < 1 ) {
        fprintf(stderr, "Usage: ... print-challenge <challenge>\n");
        return 1;
    }

    const char *challenge_filename = argv[0];
    printf("Challenge file: %s\n", challenge_filename);

    /*
    uint8_t challenge_hash[params.HASH_SIZE];
    printf("Challenge hash:\n");
    params.hash_challenge(challenge.data(), challenge_hash);
    print_hash<params.HASH_SIZE>(challenge_hash);
    */

    AccumulatorFile challenge(n_powers, challenge_filename, false, false, false);
    if ( ! challenge.open() ) {
        return 2;
    }

    printf("Previous challenge hash:\n");
    print_hash<HASH_SIZE>(challenge.data());
    printf("\n");

    printf("Tau G1\n");
    print_many_points<G1T>(TauG1, challenge, 0, 3);
    printf("\n");

    printf("Tau G2\n");
    print_many_points<G2T>(TauG2, challenge, 0, 3);
    printf("\n");

    printf("Alpha G1\n");
    print_many_points<G1T>(AlphaG1, challenge, 0, 3);
    printf("\n");

    printf("Beta G1\n");
    print_many_points<G1T>(BetaG1, challenge, 0, 3);
    printf("\n");

    printf("Beta G2\n");
    G2T point2;
    challenge.get_betaG2(point2);
    print(point2);
    printf("\n");

    return 0;
}


static int cmd_print_response ( int n_powers, int argc, char **argv )
{
    if ( argc < 1 ) {
        fprintf(stderr, "Usage: ... print-response <response>\n");
        return 1;
    }

    const char *response_filename = argv[0];
    printf("Response file: %s\n", response_filename);

    /*
    uint8_t challenge_hash[params.HASH_SIZE];
    printf("Challenge hash:\n");
    params.hash_challenge(challenge.data(), challenge_hash);
    print_hash<params.HASH_SIZE>(challenge_hash);
    */

    AccumulatorFile response(n_powers, response_filename, false, true, true);
    if ( ! response.open() ) {
        return 2;
    }

    printf("Previous challenge hash:\n");
    print_hash<HASH_SIZE>(response.data());
    printf("\n");

    printf("Tau G1\n");
    print_many_points<G1T>(TauG1, response, 0, 20);
    printf("\n");

    printf("Tau G2\n");
    print_many_points<G2T>(TauG2, response, 0, 20);
    printf("\n");

    printf("Alpha G1\n");
    print_many_points<G1T>(AlphaG1, response, 0, 20);
    printf("\n");

    printf("Beta G1\n");
    print_many_points<G1T>(BetaG1, response, 0, 20);
    printf("\n");

    printf("Beta G2\n");
    G2T point2;
    response.get_betaG2(point2);
    print(point2);
    printf("\n\n");

    if ( response.has_pubkey() )
    {
        printf("Public Key:\n");
        PublicKey pk;
        if( ! response.get_pubkey(pk) ) {
            printf("Error: while parsing public key!\n");
        }
        else {
            digest_t digest;
            response.get_hash(digest);
            if( ! pk.verify(digest) ) {
                printf("Error: public key G2 computation invalid!\n");
            }
            print(pk);
        }
    }

    return 0;
}


template<typename T>
static bool compare_elements( const AccumulatorFile *response, const AccumulatorFile *challenge, const ElementType t, size_t N )
{
    for( size_t i = 0; i < N; i++ )
    {
        T el_r;
        T el_c;

        if( ! response->get_element(t, i, el_r) ) {
            printf("Failed to retrieve response element %zu of type %d\n", i, t);
            return false;
        }

        if( ! challenge->get_element(t, i, el_c) ) {
            printf("Failed to retrieve challenge element %zu of type %d\n", i, t);
            return false;
        }

        if( el_r != el_c ) {
            printf("Inequality for element %zu of type %d\n", i, t);
            return false;
        }
    }
    return true;
}


/**
* Verify the transform from Response to Challenge
* The challenge is the same as the response
* However, the response includes the public key,
* and the response points are compressed.
* The points in the challenge are the uncompressed points
*/
static bool verify_challenge_from_response( const AccumulatorFile *prev_response, const AccumulatorFile *challenge )
{
    assert( prev_response->tau_powers_count == challenge->tau_powers_count );
    assert( prev_response->tau_powers_g1_count == challenge->tau_powers_g1_count );

    if( ! compare_elements<G1T>(prev_response, challenge, ElementType::TauG1, prev_response->tau_powers_g1_count) ) {
        printf("Error: Tau G1 comparison failed\n");
        return false;
    }

    if( ! compare_elements<G1T>(prev_response, challenge, ElementType::AlphaG1, prev_response->tau_powers_count) ) {
        printf("Error: Alpha G1 comparison failed\n");
        return false;
    }

    if( ! compare_elements<G1T>(prev_response, challenge, ElementType::BetaG1, prev_response->tau_powers_count) ) {
        printf("Error: Beta G1 comparison failed\n");
        return false;
    }

    if( ! compare_elements<G2T>(prev_response, challenge, ElementType::TauG2, prev_response->tau_powers_count) ) {
        printf("Error: Tau G2 comparison failed\n");
        return false;
    }

    if( ! compare_elements<G2T>(prev_response, challenge, ElementType::BetaG2, 1) ) {
        printf("Error: Beta G2 comparison failed\n");
        return false;
    }

    return true;
}


/**
* Verify a transform, with optional previous and next responses
*/
static bool verify_transform( const AccumulatorFile *prev_response, const AccumulatorFile *challenge, const AccumulatorFile *response )
{
    assert( challenge != nullptr );

    digest_t challenge_hash;
    digest_t response_hash;

    challenge->hash_to(challenge_hash);
    printf("Challenge hash:\n");
    print_hash(challenge_hash);

    printf("Previous response hash:\n");
    print_hash(challenge->get_hash_ptr());

    // If there is a previous response, verify continuity from it to the challenge
    if( prev_response )
    {
        digest_t prev_response_hash;
        prev_response->hash_to(prev_response_hash);
        if( memcmp(challenge->get_hash_ptr(), prev_response_hash, HASH_SIZE) != 0 ) {
            printf("Error: previous response hash doesn't match current challenge!");
            return false;
        }

        if( ! verify_challenge_from_response( prev_response, challenge ) ) {
            printf("Error: challenge does not match response\n");
            return false;
        }
    }

    // Verify that response matches previous challenge
    if( response != NULL )
    {
        response->hash_to(response_hash);
        printf("Response hash:\n");
        print_hash(response_hash);

        PublicKey pk;
        if( ! response->get_pubkey(pk) ) {
            printf("\tFailed to get public key!\n");
            return false;
        }
        print(pk);

        if( ! pk.verify(challenge_hash) ) {
            printf("\tFailed to verify response public key\n");
            //return false;
        }
    }

    return true;
}


static int cmd_verify_transform ( int n_powers, int argc, char **argv )
{
    if( argc < 2 ) {
        printf("Usage: ... verify-transform <challenge> <response> [challenge response [...]]\n");
        return 1;
    }

    AccumulatorFile *prev_response = nullptr;
    AccumulatorFile *response = nullptr;
    AccumulatorFile *challenge = nullptr;

    const int max_argc = argc + (argc%2);
    for( int i = 0; i < max_argc; i += 2 )
    {
        const char *challenge_filename = argv[i];
        const char *response_filename = argv[i+1];

        printf("Challenge file: %s\n", challenge_filename);

        if( (i+1) < argc ) {
            printf("Response file: %s\n", response_filename);
        }

        challenge = new AccumulatorFile(n_powers, challenge_filename, false, false, false);
        if( ! challenge->open() ) {
            printf("Error: unable to open challenge: %s\n", challenge_filename);
            break;
        }

        // Allow the last response to be omitted
        // This still verifies the challenge->response transform
        if( i < (argc-1) || (i==(argc-1) && (argc%2)==0 ) )
        {
            response = new AccumulatorFile(n_powers, response_filename, false, true, true);
            if( ! response->open() ) {
                printf("Error: unable to open response: %s\n", response_filename);
                break;
            }
        }

        if( ! verify_transform(prev_response, challenge, response) ) {
            printf("Error: Unable to verify transform for:\n");
            printf("       Challenge: %s\n", challenge_filename);
            printf("       Response: %s\n", response_filename);
            break;
        }

        printf("\n-------------------------------------------\n\n");

        delete challenge;
        challenge = nullptr;
        if( prev_response ) {
            delete prev_response;
        }
        prev_response = response;
        if( response != nullptr ) {
            response = nullptr;
        }
    }

    if( challenge ) {
        delete challenge;
        challenge = nullptr;
    }

    if( response ) {
        delete response;
        response = nullptr;
    }

    if( prev_response ) {
        delete prev_response;
        prev_response = nullptr;
    }

    return 0;
}


static int cmd_respond ( int n_powers, int argc, char **argv )
{
    // ....
    return 0;
}


static int cmd_test ( int n_powers, int argc, char **argv )
{
    static const uint8_t digest[32] = { 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32 };

    auto rng = rng_from_seed(digest);

    // Ensure seed is identical to rust implementation
    REQUIRE(rng.key_word(0) == 16909060);
    REQUIRE(rng.key_word(1) == 84281096);
    REQUIRE(rng.key_word(2) == 151653132);
    REQUIRE(rng.key_word(3) == 219025168);
    REQUIRE(rng.key_word(4) == 286397204);
    REQUIRE(rng.key_word(5) == 353769240);
    REQUIRE(rng.key_word(6) == 421141276);
    REQUIRE(rng.key_word(7) == 488513312);

    // Verify it generates bits in sequence
    REQUIRE( rng.next_bit() == 0 );
    REQUIRE( rng.next_bit() == 0 );
    REQUIRE( rng.next_bit() == 0 );
    REQUIRE( rng.next_bit() == 0 );
    REQUIRE( rng.next_bit() == 0 );
    REQUIRE( rng.next_bit() == 0 );
    REQUIRE( rng.next_bit() == 1 );
    REQUIRE( rng.next_bit() == 0 );
    REQUIRE( rng.next_bit() == 0 );
    REQUIRE( rng.next_bit() == 1 );

    // 10 random field elements (in montgomery form)
    for( int i = 0; i < 10; i++ ) {
        FqT f;
        rand_field(rng, f);
        gmp_printf("Fq %d = 0x%064Nx (mont)\n", i, f.mont_repr.data, FqT::num_limbs);
    }

    // 10 random big-integers (FqRepr)
    for( int i = 0; i < 10; i++ ) {
        bigint<FqT::num_limbs> bi;
        rand_bigint(rng, bi);
        gmp_printf("FqRepr %d = 0x%064Nx\n", i, bi.data, FqT::num_limbs);
    }

    // Display 10 random Fq2 elements
    for( int i = 0; i < 10; i++ ) {
        Fq2T p;
        rand_field(rng, p);
        printf("Fq2 %d = ", i);
        const auto c0 = p.c0.as_bigint();
        const auto c1 = p.c1.as_bigint();

        gmp_printf("Fq2(Fq(0x%064Nx) + Fq(0x%064Nx) * u)\n",
            c0.data, FqT::num_limbs,
            c1.data, FqT::num_limbs);
    }

    // Display 10 randomly chosen G1 points
    for( int i = 0; i < 10; i++ ) {
        G1T p;
        rand_point(rng, p);
        printf("p_%d = ", i);
        const auto p_x = p.X.as_bigint();
        const auto p_y = p.Y.as_bigint();
        gmp_printf("G1(Fq(0x%064Nx), Fq(0x%064Nx))\n", p_x.data, FqT::num_limbs, p_y.data, FqT::num_limbs);
    }

    // Display 10 randomly chosen G2 points
    for( int i = 0; i < 10; i++ ) {
        G2T p;
        rand_point(rng, p);
        p.to_affine_coordinates();

        printf("p2_%d = ", i);
        print(p);
        printf("\n");
    }

    // Confirm that hash_to_g2 matches the expected value
    {
        G2T p;
        printf("hash_to_g2: ");
        hash_to_g2(digest, p);
        print(p);
        printf("\n");
    }

    // Confirm compute_g2_s matches
    {
        G1T g1_s;
        G1T g1_s_x;
        rand_point(rng, g1_s);
        rand_point(rng, g1_s_x);
        printf("compute_g2_s g1_s: ");
        print(g1_s);
        printf("\n");
        printf("compute_g2_s g1_s_x: ");
        print(g1_s_x);
        printf("\n");
        uint8_t p = 1;
        G2T x = compute_g2_s<32>(digest, g1_s, g1_s_x, p);
        printf("compute_g2_s: ");
        print(x);
        printf("\n");
    }
    return 0;
}


int main( int argc, char **argv )
{
    ppT::init_public_params();

    if( argc < 3 ) {
        fprintf(stderr, "Usage: %s <n_powers> <command>\n", argv[0]);
        return 1;
    }

    const char *arg_n_powers = argv[1];
    const char *arg_cmd = argv[2];

    int n_powers = atoi(arg_n_powers);
    if ( n_powers < 1 || n_powers > 28 ) {
        fprintf(stderr, "Error: npowers invalid, must be between 1 and 28, not: %s\n", arg_n_powers);
        return 2;
    }

    int remaining_argc = argc - 3;
    char **remaining_argv = &argv[3];

    if ( 0 == strcmp(arg_cmd, "test") ) {
        return cmd_test(n_powers, remaining_argc, remaining_argv);
    }
    else if ( 0 == strcmp(arg_cmd, "print-challenge") ) {
        return cmd_print_challenge(n_powers, remaining_argc, remaining_argv);
    }
    else if ( 0 == strcmp(arg_cmd, "print-response") ) {
        return cmd_print_response(n_powers, remaining_argc, remaining_argv);
    }
    else if ( 0 == strcmp(arg_cmd, "verify-transform") ) {
        return cmd_verify_transform(n_powers, remaining_argc, remaining_argv);
    }
    else if ( 0 == strcmp(arg_cmd, "respond") ) {
        return cmd_respond(n_powers, remaining_argc, remaining_argv);
    }
    else {
        fprintf(stderr, "Unknown command: %s\n", arg_cmd);
        return 99;
    }

    return 0;
}
