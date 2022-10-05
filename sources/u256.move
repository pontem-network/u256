/// The implementation of large numbers written in Move language.
/// Code derived from original work by Andrew Poelstra <apoelstra@wpsoftware.net>
///
/// Rust Bitcoin Library
/// Written in 2014 by
///	   Andrew Poelstra <apoelstra@wpsoftware.net>
///
/// To the extent possible under law, the author(s) have dedicated all
/// copyright and related and neighboring rights to this software to
/// the public domain worldwide. This software is distributed without
/// any warranty.
///
/// Simplified impl by Parity Team - https://github.com/paritytech/parity-common/blob/master/uint/src/uint.rs
///
/// Features:
///     * mul
///     * div
///     * add
///     * sub
///     * shift left
///     * shift right
///     * bitwise and, xor, or.
///     * compare
///     * if math overflows the contract crashes.
///
/// Would be nice to help with the following TODO list:
/// * pow() , sqrt().
/// * math funcs that don't abort on overflows, but just returns reminders.
/// * Export of low_u128 (see original implementation).
/// * Export of low_u64 (see original implementation).
/// * Gas Optimisation:
///     * We can optimize by replacing bytecode, as far as we know Move VM itself support slices, so probably
///       we can try to replace parts works with (`v0`,`v1`,`v2`,`v3` etc) works.
///     * More?
/// * More tests (see current tests and TODOs i left):
///     * u256_arithmetic_test - https://github.com/paritytech/bigint/blob/master/src/uint.rs#L1338
///     * More from - https://github.com/paritytech/bigint/blob/master/src/uint.rs
/// * Division:
///     * Could be improved with div_mod_small (current version probably would took a lot of resources for small numbers).
///     * Also could be improved with Knuth, TAOCP, Volume 2, section 4.3.1, Algorithm D (see link to Parity above).
module u256::u256 {
    // Errors.
    /// When can't cast `U256` to `u128` (e.g. number too large).
    const ECAST_OVERFLOW: u64 = 0;

    /// When trying to get or put word into U256 but it's out of index.
    const EWORDS_OVERFLOW: u64 = 1;

    /// When math overflows.
    const EOVERFLOW: u64 = 2;

    /// When attempted to divide by zero.
    const EDIV_BY_ZERO: u64 = 3;

    // Constants.

    /// Max `u64` value.
    const U64_MAX: u128 = 18446744073709551615;

    /// Max `u128` value.
    const U128_MAX: u128 = 340282366920938463463374607431768211455;

    /// Total words in `U256` (64 * 4 = 256).
    const WORDS: u64 = 4;

    /// When both `U256` equal.
    const EQUAL: u8 = 0;

    /// When `a` is less than `b`.
    const LESS_THAN: u8 = 1;

    /// When `b` is greater than `b`.
    const GREATER_THAN: u8 = 2;

    // Data structs.

    /// The `U256` resource.
    /// Contains 4 u64 numbers.
    struct U256 has copy, drop, store {
        v0: u64,
        v1: u64,
        v2: u64,
        v3: u64,
    }

    // Public functions.
    /// Adds two `U256` and returns sum.
    public fun add(a: U256, b: U256): U256 {
        let ret = zero();
        let carry;

        let (r, o) = overflowing_add(a.v0, b.v0);
        ret.v0 = r;
        carry = if (o) {
            1
        } else {
            0
        };

        let (r, o1) = overflowing_add(a.v1, b.v1);
        let (r, o2) = overflowing_add(r, carry);
        ret.v1 = r;

        carry = if (o1 && o2) {
            2
        } else if (o1 || o2) {
            1
        } else {
            0
        };

        let (r, o1) = overflowing_add(a.v2, b.v2);
        let (r, o2) = overflowing_add(r, carry);
        ret.v2 = r;

        carry = if (o1 && o2) {
            2
        } else if (o1 || o2) {
            1
        } else {
            0
        };

        let (r, o1) = overflowing_add(a.v3, b.v3);
        let (r, o2) = overflowing_add(r, carry);
        ret.v3 = r;

        assert!(!o1 && !o2, EOVERFLOW);

        ret
    }

    /// Convert `U256` to `u128` value if possible (otherwise it aborts).
    public fun as_u128(a: U256): u128 {
        assert!(a.v2 == 0 && a.v3 == 0, ECAST_OVERFLOW);
        ((a.v1 as u128) << 64) + (a.v0 as u128)
    }

    /// Convert `U256` to `u64` value if possible (otherwise it aborts).
    public fun as_u64(a: U256): u64 {
        assert!(a.v1 == 0 && a.v2 == 0 && a.v3 == 0, ECAST_OVERFLOW);
        a.v0
    }

    /// Compares two `U256` numbers.
    public fun compare(a: &U256, b: &U256): u8 {
        if (a.v3 < b.v3) {
            return LESS_THAN
        } else if (a.v3 > b.v3) {
            return GREATER_THAN
        };

        if (a.v2 < b.v2) {
            return LESS_THAN
        } else if (a.v2 > b.v2) {
            return GREATER_THAN
        };

        if (a.v1 < b.v1) {
            return LESS_THAN
        } else if (a.v1 > b.v1) {
            return GREATER_THAN
        };

        if (a.v0 < b.v0) {
            return LESS_THAN
        } else if (a.v0 > b.v0) {
            return GREATER_THAN
        };

        EQUAL
    }

    /// Returns a `U256` from `u64` value.
    public fun from_u64(val: u64): U256 {
        from_u128((val as u128))
    }

    /// Returns a `U256` from `u128` value.
    public fun from_u128(val: u128): U256 {
        let (a2, a1) = split_u128(val);

        U256 {
            v0: a1,
            v1: a2,
            v2: 0,
            v3: 0,
        }
    }


    /// Multiples two `U256`.
    public fun mul(a: U256, b: U256): U256 {
        let ret = zero();

        // swap if a < b so that a is always bigger than b
        if (compare(&a, &b) == LESS_THAN) {
            let temp = a;
            a = b;
            b = temp;
        };

        // check overflow operations first
        let a_zeroes = leading_zeros_u64_block(a);
        let b_zeroes = leading_zeros_u64_block(b);

        assert!(a_zeroes + b_zeroes >= 3, EOVERFLOW);

        // for b, we don't need to consider v2, v3 as it will be overflow

        if (b.v0 == 0) {
            return ret
        };

        let carry: u64;
        let overflow: u64;
        let (hi, low) = split_u128((a.v0 as u128) * (b.v0 as u128));
        ret.v0 = low;
        ret.v1 = hi;

        let (hi, low) = split_u128((a.v1 as u128) * (b.v0 as u128));
        let (low, o) = overflowing_add(ret.v1, low);
        ret.v1 = low;
        overflow = if (o) {
            1
        } else {
            0
        };
        let (low, o) = overflowing_add(hi, overflow);
        ret.v2 = low;
        carry = if (o) {
            1
        } else {
            0
        };

        let (hi, low) = split_u128((a.v2 as u128) * (b.v0 as u128));
        let (low, o) = overflowing_add(ret.v2, low);
        ret.v2 = low;
        overflow = if (o) {
            1
        } else {
            0
        };
        let (hi, o) = overflowing_add(hi, carry + overflow);
        ret.v3 = hi;
        assert!(!o, EOVERFLOW);

        let (hi, low) = split_u128((a.v3 as u128) * (b.v0 as u128));
        let (low, o) = overflowing_add(ret.v3, low);
        ret.v3 = low;
        assert!(hi == 0 && !o, EOVERFLOW);

        //////////////

        if (b.v1 == 0) {
            return ret
        };

        let (hi, low) = split_u128((a.v0 as u128) * (b.v1 as u128));
        let (low, o) = overflowing_add(ret.v1, low);
        ret.v1 = low;
        overflow = if (o) {
            1
        } else {
            0
        };
        let (hi, o1) = overflowing_add(hi, overflow);
        let (hi, o2) = overflowing_add(ret.v2, hi);
        ret.v2 = hi;
        carry = if (o1 || o2) {
            1
        } else {
            0
        };

        let (hi, low) = split_u128((a.v1 as u128) * (b.v1 as u128));
        let (low, o) = overflowing_add(ret.v2, low);
        ret.v2 = low;
        overflow = if (o) {
            1
        } else {
            0
        };
        let (hi, o1) = overflowing_add(hi, carry + overflow);
        let (hi, o2) = overflowing_add(ret.v3, hi);
        ret.v3 = hi;
        // if there is a carry out, it's overflow
        assert!(!o1 && !o2, EOVERFLOW);

        let (hi, low) = split_u128((a.v2 as u128) * (b.v1 as u128));
        let (low, o) = overflowing_add(ret.v3, low);
        ret.v3 = low;
        assert!(hi == 0 && !o, EOVERFLOW);

        // no need to calculate for a.v3 as it will be overflow
        assert!(a.v3 == 0, EOVERFLOW);

        ret
    }

    /// Subtracts two `U256`, returns result.
    public fun sub(a: U256, b: U256): U256 {
        let ret = zero();

        let carry: u64;

        let (r, o) = overflowing_sub(a.v0, b.v0);
        ret.v0 = r;
        carry = if (o) {
            1
        } else {
            0
        };

        let (r, o1) = overflowing_sub(a.v1, b.v1);
        let (r, o2) = overflowing_sub(r, carry);
        ret.v1 = r;

        carry = if (o1 && o2) {
            2
        } else if (o1 || o2) {
            1
        } else {
            0
        };

        let (r, o1) = overflowing_sub(a.v2, b.v2);
        let (r, o2) = overflowing_sub(r, carry);
        ret.v2 = r;

        carry = if (o1 && o2) {
            2
        } else if (o1 || o2) {
            1
        } else {
            0
        };

        let (r, o1) = overflowing_sub(a.v3, b.v3);
        let (r, o2) = overflowing_sub(r, carry);
        ret.v3 = r;

        assert!(!o1 && !o2, EOVERFLOW);

        ret
    }

    /// Divide `a` by `b`.
    public fun div(a: U256, b: U256): U256 {
        let ret = zero();

        let a_bits = bits(&a);
        let b_bits = bits(&b);

        assert!(b_bits != 0, EDIV_BY_ZERO); // DIVIDE BY ZERO.
        if (a_bits < b_bits) {
            // Immidiatelly return.
            return ret
        };

        let shift = a_bits - b_bits;
        b = shl(b, (shift as u8));

        div_recursive(a, b, &mut ret, (shift as u8));

        ret
    }

    /// Binary xor `a` by `b`.
    fun bitxor(a: U256, b: U256): U256 {
        let ret = zero();

        ret.v0 = a.v0 ^ b.v0;
        ret.v1 = a.v1 ^ b.v1;
        ret.v2 = a.v2 ^ b.v2;
        ret.v3 = a.v3 ^ b.v3;

        ret
    }

    /// Binary and `a` by `b`.
    fun bitand(a: U256, b: U256): U256 {
        let ret = zero();

        ret.v0 = a.v0 & b.v0;
        ret.v1 = a.v1 & b.v1;
        ret.v2 = a.v2 & b.v2;
        ret.v3 = a.v3 & b.v3;

        ret
    }

    /// Binary or `a` by `b`.
    fun bitor(a: U256, b: U256): U256 {
        let ret = zero();

        ret.v0 = a.v0 | b.v0;
        ret.v1 = a.v1 | b.v1;
        ret.v2 = a.v2 | b.v2;
        ret.v3 = a.v3 | b.v3;

        ret
    }

    /// Binary not for `a`
    fun bitnot(a: U256): U256 {
        let ret = zero();

        ret.v0 = a.v0 ^ 0xFFFFFFFFFFFFFFFF;
        ret.v1 = a.v1 ^ 0xFFFFFFFFFFFFFFFF;
        ret.v2 = a.v2 ^ 0xFFFFFFFFFFFFFFFF;
        ret.v3 = a.v3 ^ 0xFFFFFFFFFFFFFFFF;

        ret
    }

    /// Shift right `a`  by `shift`.
    public fun shr(a: U256, shift: u8): U256 {
        let ret = zero();

        let word_shift = shift / 64;
        let bit_shift = shift % 64;

        if (word_shift == 0) {
            ret = a;
        } else if (word_shift == 1) {
            ret.v0 = a.v1;
            ret.v1 = a.v2;
            ret.v2 = a.v3;
        } else if (word_shift == 2) {
            ret.v0 = a.v2;
            ret.v1 = a.v3;
        } else if (word_shift == 3) {
            ret.v0 = a.v3;
        };

        if (bit_shift > 0) {
            ret.v0 = (ret.v0 >> bit_shift) + (ret.v1 << (64 - bit_shift));
            ret.v1 = (ret.v1 >> bit_shift) + (ret.v2 << (64 - bit_shift));
            ret.v2 = (ret.v2 >> bit_shift) + (ret.v3 << (64 - bit_shift));
            ret.v3 = ret.v3 >> bit_shift;
        };

        ret
    }

    /// Shift left `a` by `shift`.
    public fun shl(a: U256, shift: u8): U256 {
        let ret = zero();

        let word_shift = shift / 64;
        let bit_shift = shift % 64;

        if (word_shift == 0) {
            ret = a;
        } else if (word_shift == 1) {
            ret.v3 = a.v2;
            ret.v2 = a.v1;
            ret.v1 = a.v0;
        } else if (word_shift == 2) {
            ret.v3 = a.v1;
            ret.v2 = a.v0;
        } else if (word_shift == 3) {
            ret.v3 = a.v0;
        };

        if (bit_shift > 0) {
            ret.v3 = (ret.v3 << bit_shift) + (ret.v2 >> (64 - bit_shift));
            ret.v2 = (ret.v2 << bit_shift) + (ret.v1 >> (64 - bit_shift));
            ret.v1 = (ret.v1 << bit_shift) + (ret.v0 >> (64 - bit_shift));
            ret.v0 = ret.v0 << bit_shift;
        };

        ret
    }

    /// Returns max value.
    public fun max(): U256 {
        U256 {
            v0: (U64_MAX as u64),
            v1: (U64_MAX as u64),
            v2: (U64_MAX as u64),
            v3: (U64_MAX as u64)
        }
    }

    /// Returns `U256` equals to zero.
    public fun zero(): U256 {
        U256 {
            v0: 0,
            v1: 0,
            v2: 0,
            v3: 0,
        }
    }

    // Private functions.
    /// Get bits used to store `a`.
    fun bits(a: &U256): u64 {
        if (a.v3 > 0) {
            return 0x40 * 4 - (leading_zeros_u64(a.v3) as u64)
        };

        if (a.v2 > 0) {
            return 0x40 * 3 - (leading_zeros_u64(a.v2) as u64)
        };

        if (a.v1 > 0) {
            return 0x40 * 2 - (leading_zeros_u64(a.v1) as u64)
        };

        0x40 - (leading_zeros_u64(a.v0) as u64)
    }

    /// Get leading zeros of u64 blocks
    fun leading_zeros_u64_block(a: U256): u8 {
        if (a.v0 == 0) {
            return 4
        } else if (a.v1 == 0) {
            return 3
        } else if (a.v2 == 0) {
            return 2
        } else if (a.v3 == 0) {
            return 1
        };

        0
    }

    fun leading_zeros_u4(a: u8): u8 {
        if (a == 0) {
            4
        } else if (a == 1) {
            3
        } else if (a <= 3) {
            2
        } else if (a <= 7) {
            1
        } else {
            0
        }
    }

    fun leading_zeros_u8(a: u8): u8 {
        let a1 = a % 0x80;
        let a2 = a >> 4;
        if (a2 == 0) {
            4 + leading_zeros_u4(a1)
        } else {
            leading_zeros_u4(a2)
        }
    }

    /// Get leading zeros of a binary representation of `a`.
    fun leading_zeros_u64(a: u64): u8 {
        if (a == 0) {
            return 64
        };

        // first 8 bits
        let a_chunk = a >> 56;

        if (a_chunk > 0) {
            return leading_zeros_u8((a_chunk as u8))
        };

        a_chunk = a >> 48;
        if (a_chunk > 0) {
            return 8 + leading_zeros_u8((a_chunk as u8))
        };

        a_chunk = a >> 40;
        if (a_chunk > 0) {
            return 16 + leading_zeros_u8((a_chunk as u8))
        };

        a_chunk = a >> 32;
        if (a_chunk > 0) {
            return 24 + leading_zeros_u8((a_chunk as u8))
        };

        a_chunk = a >> 24;
        if (a_chunk > 0) {
            return 32 + leading_zeros_u8((a_chunk as u8))
        };

        a_chunk = a >> 16;
        if (a_chunk > 0) {
            return 40 + leading_zeros_u8((a_chunk as u8))
        };

        a_chunk = a >> 8;
        if (a_chunk > 0) {
            return 48 + leading_zeros_u8((a_chunk as u8))
        };

        56 + leading_zeros_u8((a as u8))
    }

    fun div_recursive(a: U256, b: U256, ret: &mut U256, shift: u8) {
        let cmp = compare(&a, &b);
        if (cmp == GREATER_THAN || cmp == EQUAL) {
            let index = shift / 64;
            let m = get(ret, (index as u64));
            let tmp = ((shift % 64) as u8);
            let c = if ((m >> tmp) % 2 == 0) {
                m + (1 << tmp)
            } else {
                m
            };
            put(ret, (index as u64), c);

            a = sub(a, b);
        };

        b = shr(b, 1);
        if (shift == 0) {
            return
        };

        div_recursive(a, b, ret, shift - 1);
    }

    /// Similar to Rust `overflowing_add`.
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fun overflowing_add(a: u64, b: u64): (u64, bool) {
        let r = (U64_MAX as u64) - b;
        if (r < a) {
            return (a - r - 1, true)
        };
        r = (U64_MAX as u64) - a;
        if (r < b) {
            return (b - r - 1, true)
        };

        (a + b, false)
    }

    /// Similar to Rust `overflowing_sub`.
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fun overflowing_sub(a: u64, b: u64): (u64, bool) {
        if (a < b) {
            let r = b - a;
            ((U64_MAX as u64) - r + 1, true)
        } else {
            (a - b, false)
        }
    }

    /// Extracts two `u64` from `a` `u128`.
    fun split_u128(a: u128): (u64, u64) {
        let a1 = ((a / 0x10000000000000000) as u64);
        let a2 =  ((a % (0xFFFFFFFFFFFFFFFF + 1)) as u64);

        (a1, a2)
    }

    /// Get word from `a` by index `i`.
    public fun get(a: &U256, i: u64): u64 {
        if (i == 0) {
            a.v0
        } else if (i == 1) {
            a.v1
        } else if (i == 2) {
            a.v2
        } else if (i == 3) {
            a.v3
        } else {
            abort EWORDS_OVERFLOW
        }
    }

    /// Put new word `val` into `U256` by index `i`.
    fun put(a: &mut U256, i: u64, val: u64) {
        if (i == 0) {
            a.v0 = val;
        } else if (i == 1) {
            a.v1 = val;
        } else if (i == 2) {
            a.v2 = val;
        } else if (i == 3) {
            a.v3 = val;
        } else {
            abort EWORDS_OVERFLOW
        }
    }

    #[test]
    fun test_get() {
        let a = U256 {
            v0: 1,
            v1: 2,
            v2: 3,
            v3: 4,
        };

        assert!(get(&a, 0) == 1, 0);
        assert!(get(&a, 1) == 2, 1);
        assert!(get(&a, 2) == 3, 2);
        assert!(get(&a, 3) == 4, 3);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_get_aborts() {
        let _ = get(&zero(), 4);
    }

    #[test]
    fun test_put() {
        let a = zero();
        put(&mut a, 0, 255);
        assert!(get(&a, 0) == 255, 0);

        put(&mut a, 1, (U64_MAX as u64));
        assert!(get(&a, 1) == (U64_MAX as u64), 1);

        put(&mut a, 2, 100);
        assert!(get(&a, 2) == 100, 2);

        put(&mut a, 3, 3);
        assert!(get(&a, 3) == 3, 3);

        put(&mut a, 2, 0);
        assert!(get(&a, 2) == 0, 4);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_put_overflow() {
        let a = zero();
        put(&mut a, 6, 255);
    }

    #[test]
    fun test_from_u128() {
        let i = 0;
        while (i < 1024) {
            let big = from_u128(i);
            assert!(as_u128(big) == i, 0);
            i = i + 1;
        };
    }

    #[test]
    fun test_add() {
        let a = from_u128(1000);
        let b = from_u128(500);

        let s = as_u128(add(a, b));
        assert!(s == 1500, 0);

        a = from_u128(U64_MAX);
        b = from_u128(U64_MAX);

        s = as_u128(add(a, b));
        assert!(s == (U64_MAX + U64_MAX), 1);

        let a = zero();
        let b = zero();
        let s = add(a, b);
        assert!(as_u128(s) == 0, 2);
    }

    #[test]
    #[expected_failure(abort_code = 2)]
    fun test_add_overflow() {
        let max = (U64_MAX as u64);

        let a = U256 {
            v0: max,
            v1: max,
            v2: max,
            v3: max
        };

        let _ = add(a, from_u128(1));
    }

    #[test]
    fun test_sub() {
        let a = from_u128(1000);
        let b = from_u128(500);

        let s = as_u128(sub(a, b));
        assert!(s == 500, 0);
    }

    #[test]
    #[expected_failure(abort_code = 2)]
    fun test_sub_overflow() {
        let a = from_u128(0);
        let b = from_u128(1);

        let _ = sub(a, b);
    }

    #[test]
    #[expected_failure(abort_code = 0)]
    fun test_too_big_to_cast_to_u128() {
        let a = from_u128(U128_MAX);
        let b = from_u128(U128_MAX);

        let _ = as_u128(add(a, b));
    }

    #[test]
    fun test_overflowing_add() {
        let (n, z) = overflowing_add(10, 10);
        assert!(n == 20, 0);
        assert!(!z, 1);

        (n, z) = overflowing_add((U64_MAX as u64), 1);
        assert!(n == 0, 2);
        assert!(z, 3);

        (n, z) = overflowing_add((U64_MAX as u64), 10);
        assert!(n == 9, 4);
        assert!(z, 5);

        (n, z) = overflowing_add(5, 8);
        assert!(n == 13, 6);
        assert!(!z, 7);
    }

    #[test]
    fun test_overflowing_sub() {
        let (n, z) = overflowing_sub(10, 5);
        assert!(n == 5, 0);
        assert!(!z, 1);

        (n, z) = overflowing_sub(0, 1);
        assert!(n == (U64_MAX as u64), 2);
        assert!(z, 3);

        (n, z) = overflowing_sub(10, 10);
        assert!(n == 0, 4);
        assert!(!z, 5);
    }

    #[test]
    fun test_split_u128() {
        let (a1, a2) = split_u128(100);
        assert!(a1 == 0, 0);
        assert!(a2 == 100, 1);

        (a1, a2) = split_u128(U64_MAX + 1);
        assert!(a1 == 1, 2);
        assert!(a2 == 0, 3);
    }

    #[test]
    fun test_mul() {
        let a = from_u128(285);
        let b = from_u128(375);

        let c = as_u128(mul(a, b));
        assert!(c == 106875, 0);

        a = from_u128(0);
        b = from_u128(1);

        c = as_u128(mul(a, b));

        assert!(c == 0, 1);

        a = from_u128(U64_MAX);
        b = from_u128(2);

        c = as_u128(mul(a, b));

        assert!(c == 36893488147419103230, 2);

        a = from_u128(U128_MAX);
        b = from_u128(U128_MAX);

        let z = mul(a, b);
        assert!(bits(&z) == 256, 3);
    }

    #[test]
    #[expected_failure(abort_code = 2)]
    fun test_mul_overflow() {
        let max = (U64_MAX as u64);

        let a = U256 {
            v0: max,
            v1: max,
            v2: max,
            v3: max,
        };

        let _ = mul(a, from_u128(2));
    }

    #[test]
    fun test_zero() {
        let a = as_u128(zero());
        assert!(a == 0, 0);

        let a = zero();
        assert!(a.v0 == 0, 1);
        assert!(a.v1 == 0, 2);
        assert!(a.v2 == 0, 3);
        assert!(a.v3 == 0, 4);
    }

    #[test]
    fun test_not() {
        let a = from_u128(0);
        let r = bitnot(a);

        assert!(r.v0 == 0xFFFFFFFFFFFFFFFF, 0);
        assert!(r.v1 == 0xFFFFFFFFFFFFFFFF, 1);
        assert!(r.v2 == 0xFFFFFFFFFFFFFFFF, 2);
        assert!(r.v3 == 0xFFFFFFFFFFFFFFFF, 3);

        let a = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let r = bitnot(a);

        assert!(r.v0 == 0xf0f0f0f0f0f0f0f0, 4);
        assert!(r.v1 == 0xFFFFFFFFFFFFFFFF, 5);
        assert!(r.v2 == 0xFFFFFFFFFFFFFFFF, 6);
        assert!(r.v3 == 0xFFFFFFFFFFFFFFFF, 7);
    }

    #[test]
    fun test_or() {
        let a = from_u128(0);
        let b = from_u128(1);
        let c = bitor(a, b);
        assert!(as_u128(c) == 1, 0);

        let a = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let b = from_u128(0xf0f0f0f0f0f0f0f0u128);
        let c = bitor(a, b);
        assert!(as_u128(c) == 0xffffffffffffffffu128, 1);
    }

    #[test]
    fun test_and() {
        let a = from_u128(0);
        let b = from_u128(1);
        let c = bitand(a, b);
        assert!(as_u128(c) == 0, 0);

        let a = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let b = from_u128(0xf0f0f0f0f0f0f0f0u128);
        let c = bitand(a, b);
        assert!(as_u128(c) == 0, 1);

        let a = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let b = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let c = bitand(a, b);
        assert!(as_u128(c) == 0x0f0f0f0f0f0f0f0fu128, 1);
    }

    #[test]
    fun test_xor() {
        let a = from_u128(0);
        let b = from_u128(1);
        let c = bitxor(a, b);
        assert!(as_u128(c) == 1, 0);

        let a = from_u128(0x0f0f0f0f0f0f0f0fu128);
        let b = from_u128(0xf0f0f0f0f0f0f0f0u128);
        let c = bitxor(a, b);
        assert!(as_u128(c) == 0xffffffffffffffffu128, 1);
    }

    #[test]
    fun test_from_u64() {
        let a = as_u128(from_u64(100));
        assert!(a == 100, 0);

        // TODO: more tests.
    }

    #[test]
    fun test_compare() {
        let a = from_u128(1000);
        let b = from_u128(50);

        let cmp = compare(&a, &b);
        assert!(cmp == 2, 0);

        a = from_u128(100);
        b = from_u128(100);
        cmp = compare(&a, &b);

        assert!(cmp == 0, 1);

        a = from_u128(50);
        b = from_u128(75);

        cmp = compare(&a, &b);
        assert!(cmp == 1, 2);
    }

    #[test]
    fun test_leading_zeros_u64() {
        let a = leading_zeros_u64(0);
        assert!(a == 64, 0);

        let a = leading_zeros_u64(1);
        assert!(a == 63, 1);

        // TODO: more tests.
    }

    #[test]
    fun test_bits() {
        let a = bits(&from_u128(0));
        assert!(a == 0, 0);

        a = bits(&from_u128(255));
        assert!(a == 8, 1);

        a = bits(&from_u128(256));
        assert!(a == 9, 2);

        a = bits(&from_u128(300));
        assert!(a == 9, 3);

        a = bits(&from_u128(60000));
        assert!(a == 16, 4);

        a = bits(&from_u128(70000));
        assert!(a == 17, 5);

        let b = from_u64(70000);
        let sh = shl(b, 100);
        assert!(bits(&sh) == 117, 6);

        let sh = shl(sh, 100);
        assert!(bits(&sh) == 217, 7);

        let sh = shl(sh, 100);
        assert!(bits(&sh) == 0, 8);
    }

    #[test]
    fun test_shift_left() {
        let a = from_u128(100);
        let b = shl(a, 2);

        assert!(as_u128(b) == 400, 0);

        // TODO: more shift left tests.
    }

    #[test]
    fun test_shift_right() {
        let a = from_u128(100);
        let b = shr(a, 2);

        assert!(as_u128(b) == 25, 0);

        // TODO: more shift right tests.
    }

    #[test]
    fun test_div() {
        let a = from_u128(100);
        let b = from_u128(5);
        let d = div(a, b);

        assert!(as_u128(d) == 20, 0);

        let a = from_u128(U64_MAX);
        let b = from_u128(U128_MAX);
        let d = div(a, b);
        assert!(as_u128(d) == 0, 1);

        let a = from_u128(U64_MAX);
        let b = from_u128(U128_MAX);
        let d = div(a, b);
        assert!(as_u128(d) == 0, 2);

        let a = from_u128(U128_MAX);
        let b = from_u128(U64_MAX);
        let d = div(a, b);
        assert!(as_u128(d) == 18446744073709551617, 2);
    }

    #[test]
    #[expected_failure(abort_code=3)]
    fun test_div_by_zero() {
        let a = from_u128(1);
        let _z = div(a, from_u128(0));
    }

    #[test]
    fun test_as_u64() {
        let _ = as_u64(from_u64((U64_MAX as u64)));
        let _ = as_u64(from_u128(1));
    }

    #[test]
    #[expected_failure(abort_code=0)]
    fun test_as_u64_overflow() {
        let _ = as_u64(from_u128(U128_MAX));
    }
}
