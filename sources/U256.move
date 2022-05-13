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
/// Would be nice to help with the following TODO list:
/// * Refactoring.
/// * Gas optimisation.
/// * Still missing Div func.
/// * More tests.
module Sender::U256 {
    use Std::Vector;

    // Errors.
    /// When can't cast `U256` to `u128` (e.g. number too large).
    const EU128_OVERFLOW: u64 = 0;

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
    /// Contains 4 u64 numbers inside in vector `ret`.
    struct U256 has copy, drop, store {
        ret: vector<u64>,
    }

    // Public functions.

    /// Adds two U256 and returns sum.
    public fun add(a: U256, b: U256): U256 {
        let ret = Vector::empty<u64>();
        let carry = 0u64;

        let i = 0;
        while (i < WORDS) {
            let a1 = *Vector::borrow(&a.ret, i);
            let b1 = *Vector::borrow(&b.ret, i);

            if (carry != 0) {
                let (res1, is_overflow1) = overflowing_add(a1, b1);
                let (res2, is_overflow2) = overflowing_add(res1, carry);
                Vector::push_back(&mut ret, res2);

                carry = 0;
                if (is_overflow1) {
                    carry = carry + 1;
                };

                if (is_overflow2) {
                    carry = carry + 1;
                }
            } else {
                let (res,is_overflow) = overflowing_add(a1, b1);
                Vector::push_back(&mut ret, res);

                carry = 0;
                if (is_overflow) {
                    carry = 1;
                };
            };

            i = i + 1;
        };

        U256 { ret }
    }

    /// Convert `U256` to `u128` value if possible (otherwise it aborts).
    public fun as_u128(a: U256): u128 {
        let a1 = *Vector::borrow(&a.ret, 0);
        let a2 = *Vector::borrow(&a.ret, 1);
        let z = *Vector::borrow(&a.ret, 2);

        assert!(z == 0, EU128_OVERFLOW);

        ((a2 as u128) << 64) + (a1 as u128)
    }

    /// Compares two `U256` numbers.
    public fun compare(a: &U256, b: &U256): u8 {
        let i = WORDS;
        while (i > 0) {
            i = i - 1;
            let a1 = *Vector::borrow(&a.ret, i);
            let b1 = *Vector::borrow(&b.ret, i);

            if (a1 != b1) {
                if (a1 < b1) {
                    return LESS_THAN
                } else {
                    return GREATER_THAN
                }
            }
        };

        // Equal.
        EQUAL
    }

    /// Returns a `U256` from `u64` value.
    public fun from_u64(val: u64): U256 {
        from_u128((val as u128))
    }

    /// Returns a `U256` from `u128` value.
    public fun from_u128(val: u128): U256 {
        let (a2, a1) = split_u128(val);

        let ret = Vector::singleton<u64>(a1);
        Vector::push_back(&mut ret, a2);
        Vector::push_back(&mut ret, 0);
        Vector::push_back(&mut ret, 0);

        U256 { ret }
    }

    /// Multiples two `U256`, returns result.
    public fun mul(a: U256, b: U256): U256 {
        let ret = Vector::empty<u64>();

        let i = 0;
        while (i < WORDS * 2) {
            Vector::push_back(&mut ret, 0);
            i = i + 1;
        };

        let i = 0;
        while (i < WORDS) {
            let carry = 0u64;
            let b1 = *Vector::borrow(&b.ret, i);

            let j = 0;
            while (j < WORDS) {
                let a1 = *Vector::borrow(&a.ret, j);

                if (a1 != 0 || carry != 0) {
                    let (hi, low) = split_u128((a1 as u128) * (b1 as u128));

                    let overflow = {
                        let existing_low = Vector::borrow_mut(&mut ret, i + j);
                        let (low, o) = overflowing_add(low, *existing_low);
                        *existing_low = low;
                        if (o) {
                            1
                        } else {
                            0
                        }
                    };

                    carry = {
                        let existing_hi = Vector::borrow_mut(&mut ret, i + j + 1);
                        let hi = hi + overflow;
                        let (hi, o0) = overflowing_add(hi, carry);
                        let (hi, o1) = overflowing_add(hi, *existing_hi);
                        *existing_hi = hi;

                        if (o0 || o1) {
                            1
                        } else {
                            0
                        }
                    };
                };

                j = j + 1;
            };

            i = i + 1;
        };

        // TODO: probably check zeros in ret[4..] and see if overflow happened and abort?

        let final = Vector::empty<u64>();
        let i = 0;
        while (i < WORDS) {
            Vector::push_back(&mut final, *Vector::borrow(&ret, i));
            i = i + 1;
        };

        U256 { ret: final }
    }

    /// Subtracts two `U256`, returns result.
    public fun sub(a: U256, b: U256): U256 {
        let ret = Vector::empty<u64>();

        let carry = 0u64;

        let i = 0;
        while (i < WORDS) {
            let a1 = *Vector::borrow(&a.ret, i);
            let b1 = *Vector::borrow(&b.ret, i);

            if (carry != 0) {
                let (res1, is_overflow1) = overflowing_sub(a1, b1);
                let (res2, is_overflow2) = overflowing_sub(res1, carry);
                Vector::push_back(&mut ret, res2);

                carry = 0;
                if (is_overflow1) {
                    carry = carry + 1;
                };

                if (is_overflow2) {
                    carry = carry + 1;
                }
            } else {
                let (res,is_overflow) = overflowing_sub(a1, b1);
                Vector::push_back(&mut ret, res);

                carry = 0;
                if (is_overflow) {
                    carry = 1;
                };
            };

            i = i + 1;
        };

        U256 { ret }
    }

    /// Returns `U256` equals to zero.
    public fun zero(): U256 {
        let ret = Vector::empty<u64>();
        Vector::push_back(&mut ret, 0);
        Vector::push_back(&mut ret, 0);
        Vector::push_back(&mut ret, 0);
        Vector::push_back(&mut ret, 0);

        U256 { ret }
    }

    // Private functions.

    /// Similar to Rust `overflowing_add`.
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fun overflowing_add(a: u64, b: u64): (u64, bool) {
        let a128 = (a as u128);
        let b128 = (b as u128);

        let r = a128 + b128;
        if (r > U64_MAX) {
            // overflow
            let overflow = r - U64_MAX - 1;
            ((overflow as u64), true)
        } else {
            (((a128 + b128) as u64), false)
        }
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

    /// Extracts two `u64` from `u128`.
    fun split_u128(a: u128): (u64, u64) {
        let a1 = ((a >> 64) as u64);
        let a2 = ((a & 0xFFFFFFFFFFFFFFFF) as u64);

        (a1, a2)
    }


    // Tests.

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
        assert!(s == (U64_MAX *2), 1);
    }

    #[test]
    fun test_sub() {
        let a = from_u128(1000);
        let b = from_u128(500);

        let s = as_u128(sub(a, b));
        assert!(s == 500, 0);

        let overflow = sub(from_u128(0), from_u128(1));
        let i = 0;
        while (i < WORDS) {
            let j = *Vector::borrow(&overflow.ret, i);
            assert!(j == (U64_MAX as u64), 1);
            i = i + 1;
        }
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
    }

    #[test]
    fun test_zero() {
        let a = as_u128(zero());
        assert!(a == 0, 0);
    }

    #[test]
    fun test_from_u64() {
        let a = as_u128(from_u64(100));
        assert!(a == 100, 0);
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
}
