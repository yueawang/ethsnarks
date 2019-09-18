#ifndef CHACHARNG_HPP_
#define CHACHARNG_HPP_

// C++ port of Rust's ChaChaRng
// https://rust-num.github.io/num/src/rand/chacha.rs.html

#include <cstdint>


template<size_t nRounds>
class ChaChaRng {
public:
    static constexpr size_t KEY_WORDS = 8;
    static constexpr size_t KEY_BYTES = (KEY_WORDS * sizeof(uint32_t));
    static constexpr size_t STATE_WORDS = 16;
    static constexpr uint32_t ZERO_KEY[KEY_WORDS] = {0};

    uint32_t buffer[STATE_WORDS] {0};
    uint32_t state[STATE_WORDS] {0};
    uint32_t index {STATE_WORDS};

    ChaChaRng()
    {
        reseed(ZERO_KEY);
    }

    ChaChaRng( const uint32_t key[KEY_WORDS] )
    {
        reseed(key);
    }


    uint32_t key_word( size_t i )
    {
        assert( i < KEY_WORDS );
        return state[4+i];
    }


    /**
    Modified word layout is:
    ```text
    constant constant constant constant
    key      key      key      key
    key      key      key      key
    counter  counter  counter  counter
    ```
    */
    inline void reseed( const uint32_t key[KEY_WORDS] )
    {
        state[0] = 0x61707865;
        state[1] = 0x3320646E;
        state[2] = 0x79622D32;
        state[3] = 0x6B206574;

        for( size_t i = 0; i < KEY_WORDS; i++ ) {
            state[4+i] = key[i];
        }

        state[12] = 0;
        state[13] = 0;
        state[14] = 0;
        state[15] = 0;

        index = STATE_WORDS;
    }

    /** Refill the internal output buffer */
    inline void update()
    {
        core(buffer, state);

        index = 0;

        // Increment 128-bit counter, little-endian word order
        if( ++state[12] != 0 ) return;
        if( ++state[13] != 0 ) return;
        if( ++state[14] != 0 ) return;
        state[15] += 1;
    }

    /** Sets the internal 128-bit ChaCha counter */
    inline void set_counter( const uint64_t counter_low, const uint64_t counter_high )
    {
        state[12] = (counter_low) & 0xFFFFFFFF;
        state[13] = (counter_low >> 32) & 0xFFFFFFFF;
        state[14] = (counter_high) & 0xFFFFFFFF;
        state[15] = (counter_high >> 32) & 0xFFFFFFFF;
        index = STATE_WORDS;
    }

    inline void core( uint32_t output[STATE_WORDS], const uint32_t input[STATE_WORDS] )
    {
        #define CHACHA_ROTL32(x, n) (((x) << (n)) | ((x) >> (32 - (n))))

        #define CHACHA_QUARTERROUND(x, a, b, c, d) \
            x[a] = x[a] + x[b]; x[d] ^= x[a]; x[d] = CHACHA_ROTL32(x[d], 16); \
            x[c] = x[c] + x[d]; x[b] ^= x[c]; x[b] = CHACHA_ROTL32(x[b], 12); \
            x[a] = x[a] + x[b]; x[d] ^= x[a]; x[d] = CHACHA_ROTL32(x[d],  8); \
            x[c] = x[c] + x[d]; x[b] ^= x[c]; x[b] = CHACHA_ROTL32(x[b],  7)

        for( size_t i = 0; i < STATE_WORDS; i++ ) {
            output[i] = input[i];
        }

        for ( size_t i = 0; i < nRounds; i += 2 ) {
            // Column round
            CHACHA_QUARTERROUND(output, 0, 4,  8, 12);
            CHACHA_QUARTERROUND(output, 1, 5,  9, 13);
            CHACHA_QUARTERROUND(output, 2, 6, 10, 14);
            CHACHA_QUARTERROUND(output, 3, 7, 11, 15);
            // Diagonal round
            CHACHA_QUARTERROUND(output, 0, 5, 10, 15);
            CHACHA_QUARTERROUND(output, 1, 6, 11, 12);
            CHACHA_QUARTERROUND(output, 2, 7,  8, 13);
            CHACHA_QUARTERROUND(output, 3, 4,  9, 14);
        }

        #undef CHACHA_QUARTERROUND
        #undef CHACHA_ROTL32

        for( size_t i = 0; i < STATE_WORDS; i++ ) {
            output[i] += input[i];
        }
    }

    inline uint32_t next_u32()
    {
        if( index == STATE_WORDS ) {
            update();
        }
        return buffer[index++ % STATE_WORDS];
    }

    inline bool next_bit()
    {
        const auto i = next_u32();
        return i % 2 != 0;
    }

    inline uint64_t next_u64()
    {
        return ((uint64_t)next_u32() << 32) | next_u32();
    }
};


using ChaChaRng20 = ChaChaRng<20>;


// CHACHARNG_HPP_
#endif
