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


static void hash_Fq(blake2b_ctx &ctx, const FqT &field)
{
    const auto bi = field.as_bigint();
    /*
    // Points are stored in montgomery form internally
    // Perform montgomery reduction before hashing
    FqT tmp;
    tmp.mont_repr.data[0] = 1;
    tmp.mul_reduce(field.mont_repr);
    */
    blake2b_update(&ctx, bi.data, sizeof(mp_limb_t) * FqT::num_limbs);
}


static void hash_Fq2(blake2b_ctx &ctx, const Fq2T &field)
{
    hash_Fq(ctx, field.c0);
    hash_Fq(ctx, field.c1);
}


static void hash_g1_uncompressed(blake2b_ctx &ctx, const G1T& point)
{
    G1T point_copy;
	point_copy.to_affine_coordinates();
	hash_Fq(ctx, point.X);
	hash_Fq(ctx, point.Y);
}


static void hash_g2_uncompressed(blake2b_ctx &ctx, const G2T& point)
{
    G2T point_copy(point);
    point_copy.to_affine_coordinates();
    hash_Fq2(ctx, point.X);
    hash_Fq2(ctx, point.Y);
}


template<long N>
static int cmp( const libff::bigint<N> &a, const libff::bigint<N> &b )
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
static bool test_and_clear_bit( libff::bigint<N> &bi, int bitno )
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


template<size_t R>
static void rand_bigint( ChaChaRng<R> &rng, libff::bigint<FqT::num_limbs> &bi )
{
    for( int i = 0; i < FqT::num_limbs; i++ ) {
        bi.data[i] = rng.next_u64();            
    }
}


/** Computes a uniformly random element (in montgomery form) using rejection sampling. */
template<size_t R>
static void rand_field( ChaChaRng<R> &rng, FqT &out )
{
    // Load random data directly into montgomery form, no reduction
    while( 1 ) {
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


template<size_t R>
static void rand_field( ChaChaRng<R> &rng, Fq2T &out )
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


static int legendre( const FqT &a ) {
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


static void scale_by_cofactor( G2T &point ) {
    // cofactor for Fp2 = (2*q) - r
    static const decltype(Fq2T::euler) cofactor("21888242871839275222246405745257275088844257914179612981679871602714643921549");
    point = cofactor * point;
}


template<size_t R, typename T>
static void rand_point( ChaChaRng<R> &rng, T &point )
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


ChaChaRng<20> rng_from_seed(const uint8_t *data)
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


static void hash_to_g2(const uint8_t *data, G2T &point)
{
    auto rng = rng_from_seed(data);
    rand_point(rng, point);
    point.to_affine_coordinates();
}


/** Reads an n-limb big integer, in its standard form (without montgomery reduction) */
template<long N>
static const uint8_t* parse_bigint( const uint8_t *data, libff::bigint<N> &bi )
{
    assert( data != nullptr );
    if( data != nullptr ) {
        // XXX: slow conversion from big-endian form to little-end montgomery form
        mpz_t rop;
        mpz_init(rop);
        mpz_import(rop, N, 1, sizeof(mp_limb_t), 1, 0, data);
        bi = decltype(bi)(rop);
        return &data[FqT_size_bytes];
    }
    return nullptr;
}


/** Parses a field element in its n-limb big integer form
Then converts into montgomery form
Field element is in big-endian form, so must be parsed using mpz_import */
static const uint8_t* parse_FqT( const uint8_t *data, FqT &field )
{
    assert( data != nullptr );
    if( data != nullptr ) {
        libff::bigint<FqT::num_limbs> x;
        data = parse_bigint(data, x);
        field = FqT(x);
    }
    return data;
}


/** Parses a field element (converts into montgomery form)
Coefficients are in big-endian form (c1, then c0) */
static const uint8_t* parse_Fq2T( const uint8_t *data, Fq2T &field )
{
    assert( data != nullptr );
    if( data != nullptr )
    {
        data = parse_FqT(data, field.c1);
        return parse_FqT(data, field.c0);
    }
    return nullptr;
}


/** Parses an uncompressd G1 point (from its byte-representation in from memory) */
static const uint8_t* parse_g1_uncompressed( const uint8_t *data, G1T &point )
{
    assert( data != nullptr );
    if( data != nullptr ) {
        data = parse_FqT(data, point.X);
        data = parse_FqT(data, point.Y);
        point.Z = FqT::one();
    }
    return data;
}


/** Parses an uncompressd G2 point (from its byte-representation in from memory) */
static const uint8_t* parse_g2_uncompressed( const uint8_t *data, G2T &point )
{
    assert( data != nullptr );
    if( data != nullptr )
    {
        data = parse_Fq2T(data, point.X);
        data = parse_Fq2T(data, point.Y);
        point.Z = Fq2T::one();
    }
    return data;
}


/** Parses a compressd G1 point (from its byte-representation in from memory) */
static const uint8_t* parse_g1_compressed( const uint8_t *data, G1T &point )
{
    assert( data != nullptr );
    if( data == nullptr )
        return nullptr;

    libff::bigint<FqT::num_limbs> bi;
    data = parse_bigint(data, bi);
    assert( data != nullptr );

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

    point.X = FqT(bi);
    if( ! recover_y_from_x(point.X, point.Y, greatest) )
        return nullptr;
    point.Z = FqT::one();

    return data;
}


/** Parses an compressd G2 point (from its byte-representation in from memory) */
static const uint8_t* parse_g2_compressed( const uint8_t *data, G2T &point )
{
    assert( data != nullptr );
    if( data != nullptr )
    {
        libff::bigint<FqT::num_limbs> c1;
        libff::bigint<FqT::num_limbs> c0;
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
            const Fq2T X(c0, c1);
            if( ! recover_y_from_x(X, point.Y, greatest) ) {
                return nullptr;
            }
            point.Z = Fq2T::one();
            point.X = X;
        }
    }

    return data;
}


/**
Checks if pairs have the same ratio.
Under the hood uses pairing to check
x1/x2 = y1/y2 => x1*y2 = x2*y1
*/
bool same_ratio(const G1T& a, const G1T& b, const G2T& c, const G2T& d)
{
    const auto e = ppT::pairing(a, d);
    const auto f = ppT::pairing(b, c);
    return e == f;
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
            int flags = m_writeable ? O_RDWR|O_CREAT|O_TRUNC : O_RDONLY;
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


template<size_t N>
const G2T compute_g2_s(const uint8_t digest[N], const G1T &g1_s, const G1T &g1_s_x, const uint8_t personalization)
{
    blake2b_ctx ctx;
    blake2b_init(&ctx, N, NULL, 0);

    blake2b_update(&ctx, &personalization, 1);
    blake2b_update(&ctx, digest, N);

    hash_g1_uncompressed(ctx, g1_s);
    hash_g1_uncompressed(ctx, g1_s_x);

    uint8_t output[N];
    blake2b_final(&ctx, output);

    return hash_to_g2(output);
}


class PublicKey {
public:
    G1T tau_g1[2];      // tau_g1_s, tau_g1_s_tau
    G1T alpha_g1[2];    // alpha_g1_s, alpha_g1_s_tau
    G1T beta_g1[2];     // beta_g1_s, beta_g1_s_tau
    G2T tau_g2;
    G2T alpha_g2;
    G2T beta_g2;

    static size_t size() {
        return (G1_UNCOMPRESSED_BYTE_SIZE*6) + (G2_UNCOMPRESSED_BYTE_SIZE*3);
    }

    static PublicKey parse(const uint8_t *data)
    {
        PublicKey self;
        data = parse_g1_compressed(data, self.tau_g1[0]);
        data = parse_g1_compressed(data, self.tau_g1[1]);
        data = parse_g1_compressed(data, self.alpha_g1[0]);
        data = parse_g1_compressed(data, self.alpha_g1[1]);
        data = parse_g1_compressed(data, self.beta_g1[0]);
        data = parse_g1_compressed(data, self.beta_g1[1]);
        data = parse_g2_uncompressed(data, self.tau_g2);
        data = parse_g2_uncompressed(data, self.alpha_g2);
        parse_g2_uncompressed(data, self.beta_g2);
        return self;
    }
};


class AccumulatorFile {
public:

    // Blake2b hash size
    static const size_t HASH_SIZE = 64;

protected:
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

public:
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

    const void hash(const uint8_t *challenge, uint8_t result[HASH_SIZE]) const
    {
        assert( this->is_open() );
        blake2b_ctx ctx;
        blake2b_init(&ctx, HASH_SIZE, NULL, 0);
        blake2b_update(&ctx, challenge, this->m_handle.size());
        blake2b_final(&ctx, result);
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

    size_t g1_size(bool force_uncompressed = false) const {
        if( force_uncompressed ) {
            return G1_UNCOMPRESSED_BYTE_SIZE;
        }
        return m_is_compressed ? G1_COMPRESSED_BYTE_SIZE : G1_UNCOMPRESSED_BYTE_SIZE;
    }

    size_t g2_size(bool force_uncompressed = false) const {
        if( force_uncompressed ) {
            return G2_UNCOMPRESSED_BYTE_SIZE;
        }
        return m_is_compressed ? G2_COMPRESSED_BYTE_SIZE : G2_UNCOMPRESSED_BYTE_SIZE;
    }

    bool _parse_g1(const size_t offset, G1T &point, bool force_uncompressed = false) const
    {
        assert( this->is_open() );
        if( ! force_uncompressed && this->m_is_compressed ) {
            parse_g1_compressed(m_handle.data() + offset, point);
        }
        else {
            parse_g1_uncompressed(m_handle.data() + offset, point);
        }
        return point.is_well_formed();
    }

    bool _parse_g2(const size_t offset, G2T &point, bool force_uncompressed = false) const
    {
        assert( this->is_open() );
        if( ! force_uncompressed && this->m_is_compressed ) {
            parse_g2_compressed(m_handle.data() + offset, point);
        }
        else {
            parse_g2_uncompressed(m_handle.data() + offset, point);
        }
        return point.is_well_formed();
    }

    bool tauG1(size_t idx, G1T &point) const
    {
        if( idx < tau_powers_g1_count ) {
            return _parse_g1(tau_powers_g1_offset + (g1_size() * idx), point);
        }
        return false;
    }

    bool tauG2(size_t idx, G2T &point) const
    {
        if( idx < tau_powers_count ) {
            return _parse_g2(tau_powers_g2_offset + (g2_size() * idx), point);
        }
        return false;
    }

    bool alphaG1(size_t idx, G1T &point) const
    {
        if( idx < tau_powers_count ) {
            return _parse_g1(alpha_tau_powers_g1_offset + (g1_size() * idx), point);
        }
        return false;
    }

    bool betaG1(size_t idx, G1T &point) const
    {
        if( idx < tau_powers_count ) {
            return _parse_g1(beta_tau_powers_g1_offset + (g1_size() * idx), point);
        }
        return false;
    }

    bool betaG2(G2T &point) const {
        return _parse_g2(beta_g2_offset, point);
    }
};


/** Displays a nicely formatted and easily readable hash */
template<size_t N>
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
    print_hash<challenge.HASH_SIZE>(challenge.data());
    printf("\n");

    printf("Tau G1\n");
    G1T point[3];
    for( int i = 0; i < 3; i++ ) {
        challenge.tauG1(i, point[i]);
        point[i].print();
        printf("... %s\n", point[i].is_well_formed() ? "well formed" : "invalid!" );
    }
    printf("\n");

    printf("Tau G2\n");
    G2T point2[3];
    for( int i = 0; i < 3; i++ ) {
        challenge.tauG2(i, point2[i]);
        point2[i].print();
        printf("... %s\n", point2[i].is_well_formed() ? "well formed" : "invalid!" );
    }
    printf("\n");

    printf("Alpha G1\n");
    for( int i = 0; i < 3; i++ ) {
        challenge.alphaG1(i, point[i]);
        point[i].print();
        printf("... %s\n", point[i].is_well_formed() ? "well formed" : "invalid!" );
    }
    printf("\n");

    printf("Beta G1\n");
    for( int i = 0; i < 3; i++ ) {
        challenge.betaG1(i, point[i]);
        point[i].print();
        printf("... %s\n", point[i].is_well_formed() ? "well formed" : "invalid!" );
    }
    printf("\n");

    printf("Beta G2\n");
    challenge.betaG2(point2[0]);
    point2[0].print();
    printf("... %s\n", point2[0].is_well_formed() ? "well formed" : "invalid!" );
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
    print_hash<response.HASH_SIZE>(response.data());
    printf("\n");

    printf("Tau G1\n");
    G1T point[20];
    for( int i = 0; i < 20; i++ ) {
        response.tauG1(i, point[i]);
        printf("%d:\n", i);
        point[i].print();
        printf("... %s\n", point[i].is_well_formed() ? "well formed" : "invalid!" );
    }
    printf("\n");

    printf("Tau G2\n");
    G2T point2[3];
    for( int i = 0; i < 3; i++ ) {
        response.tauG2(i, point2[i]);
        point2[i].print();
        printf("... %s\n", point2[i].is_well_formed() ? "well formed" : "invalid!" );
    }
    printf("\n");

    printf("Alpha G1\n");
    for( int i = 0; i < 3; i++ ) {
        response.alphaG1(i, point[i]);
        point[i].print();
        printf("... %s\n", point[i].is_well_formed() ? "well formed" : "invalid!" );
    }
    printf("\n");

    printf("Beta G1\n");
    for( int i = 0; i < 3; i++ ) {
        response.betaG1(i, point[i]);
        point[i].print();
        printf("... %s\n", point[i].is_well_formed() ? "well formed" : "invalid!" );
    }
    printf("\n");

    printf("Beta G2\n");
    response.betaG2(point2[0]);
    point2[0].print();
    printf("... %s\n", point2[0].is_well_formed() ? "well formed" : "invalid!" );
    printf("\n");

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
    assert(rng.key_word(0) == 16909060);
    assert(rng.key_word(1) == 84281096);
    assert(rng.key_word(2) == 151653132);
    assert(rng.key_word(3) == 219025168);
    assert(rng.key_word(4) == 286397204);
    assert(rng.key_word(5) == 353769240);
    assert(rng.key_word(6) == 421141276);
    assert(rng.key_word(7) == 488513312);

    // Verify it generates bits in sequence
    assert( rng.next_bit() == 0 );
    assert( rng.next_bit() == 0 );
    assert( rng.next_bit() == 0 );
    assert( rng.next_bit() == 0 );
    assert( rng.next_bit() == 0 );
    assert( rng.next_bit() == 0 );
    assert( rng.next_bit() == 1 );
    assert( rng.next_bit() == 0 );
    assert( rng.next_bit() == 0 );
    assert( rng.next_bit() == 1 );

    // 10 random field elements (in montgomery form)
    for( int i = 0; i < 10; i++ ) {
        FqT f;
        rand_field(rng, f);
        gmp_printf("Fq %d = 0x%064Nx (mont)\n", i, f.mont_repr.data, FqT::num_limbs);
    }

    // 10 random big-integers (FqRepr)
    for( int i = 0; i < 10; i++ ) {
        libff::bigint<FqT::num_limbs> bi;
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
        const auto p_x_c0 = p.X.c0.as_bigint();
        const auto p_x_c1 = p.X.c1.as_bigint();
        const auto p_y_c0 = p.Y.c0.as_bigint();
        const auto p_y_c1 = p.Y.c1.as_bigint();

        gmp_printf("G2(x=Fq2(Fq(0x%064Nx) + Fq(0x%064Nx) * u), y=Fq2(Fq(0x%064Nx) + Fq(0x%064Nx) * u))\n",
            p_x_c0.data, FqT::num_limbs,
            p_x_c1.data, FqT::num_limbs,
            p_y_c0.data, FqT::num_limbs,
            p_y_c1.data, FqT::num_limbs);
    }

    {
        G2T p;
        hash_to_g2(digest, p);
        const auto p_x_c0 = p.X.c0.as_bigint();
        const auto p_x_c1 = p.X.c1.as_bigint();
        const auto p_y_c0 = p.Y.c0.as_bigint();
        const auto p_y_c1 = p.Y.c1.as_bigint();

        gmp_printf("G2(x=Fq2(Fq(0x%064Nx) + Fq(0x%064Nx) * u), y=Fq2(Fq(0x%064Nx) + Fq(0x%064Nx) * u))\n",
                    p_x_c0.data, FqT::num_limbs,
                    p_x_c1.data, FqT::num_limbs,
                    p_y_c0.data, FqT::num_limbs,
                    p_y_c1.data, FqT::num_limbs);
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
    else if ( 0 == strcmp(arg_cmd, "respond") ) {
        return cmd_respond(n_powers, remaining_argc, remaining_argv);
    }
    else {
        fprintf(stderr, "Unknown command: %s\n", arg_cmd);
        return 99;
    }

    return 0;
}
