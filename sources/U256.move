module Sender::U256 {
    use Std::Vector;
    use Std::Debug;

    // Errors.
    const EU128_OVERFLOW: u64 = 0;

    const MAX_U64: u128 = 18446744073709551615;
    const MAX_u128: u128 = 340282366920938463463374607431768211455;

    const WORDS: u64 = 4;

    struct U256 has copy, drop, store {
        raw: vector<u64>,
    }

    // Public functions.

    public fun from_u128(val: u128): U256 {
        let a128 = val >> 64;
        let a2: u64 = (a128 as u64);
        let a1: u64 = (((val << 64) >> 64) as u64);

        Debug::print(&a1);
        Debug::print(&a2);

        let raw = Vector::singleton<u64>(a1);
        Vector::push_back(&mut raw, a2);
        Vector::push_back(&mut raw, 0);
        Vector::push_back(&mut raw, 0);

        Debug::print(&raw);

        U256 { raw }
    }

    public fun as_u128(a: U256): u128 {
        let a1 = *Vector::borrow(&a.raw, 0);
        let a2 = *Vector::borrow(&a.raw, 1);
        let z = *Vector::borrow(&a.raw, 2);

        assert!(z == 0, EU128_OVERFLOW);

        ((a2 as u128) << 64) + (a1 as u128)
    }

    /// Similar to rust overflowing_add.
    fun overflowing_add(a: u64, b: u64): (u64, bool) {
        let a128 = (a as u128);
        let b128 = (b as u128);

        let r = a128 + b128;
        if (r > MAX_U64) {
            // overflow
            let overflow = r - MAX_U64 - 1;
            ((overflow as u64), true)
        } else {
            (((a128 + b128) as u64), false)
        }
    }

    /// Similar to rust overflowing_sub.
    fun overflowing_sub(a: u64, b: u64): (u64, bool) {
        if (a < b) {
            let r = b - a;
            ((MAX_U64 as u64) - r + 1, true)
        } else {
            (a - b, false)
        }
    }

//    public fun sub(a: u64, b: u64): (u64, bool) {
//        let raw = Vector::empty<u64>();
//
//        let carry = 0u64;
//
//    }

    /// Add two U256.
    public fun add(a: U256, b: U256): U256 {
        let raw = Vector::empty<u64>();

        let carry = 0u64;

        let i = 0;
        while (i < WORDS) {
            let a1 = *Vector::borrow(&a.raw, i);
            let b1 = *Vector::borrow(&b.raw, i);

            if (carry != 0) {
                let (res1, is_overflow1) = overflowing_add(a1, b1);
                let (res2, is_overflow2) = overflowing_add(res1, carry);
                Vector::push_back(&mut raw, res2);

                carry = 0;
                if (is_overflow1) {
                    carry = carry + 1;
                };

                if (is_overflow2) {
                    carry = carry + 1;
                }
            } else {
                let (res,is_overflow) = overflowing_add(a1, b1);
                Vector::push_back(&mut raw, res);

                carry = 0;
                if (is_overflow) {
                    carry = 1;
                };
            };

            i = i + 1;
        };

        U256 { raw }
    }

    #[test]
    fun test_from_u128() {
        let i = 0;
        while (i < 1024) {
            let big = from_u128(i);
            assert!(as_u128(big) == i, 1);
            i = i + 1;
        };
    }

    #[test]
    fun test_add() {
        let a = from_u128(1000);
        let b = from_u128(500);

        let s = as_u128(add(a, b));
        assert!(s == 1500, 1);

        a = from_u128(MAX_U64);
        b = from_u128(MAX_U64);

        s = as_u128(add(a, b));
        assert!(s == (MAX_U64*2), 2);
    }

    #[test]
    #[expected_failure(abort_code = 0)]
    fun test_too_big_to_cast_to_u128() {
        let a = from_u128(MAX_u128);
        let b = from_u128(MAX_u128);

        let _ = as_u128(add(a, b));
    }

    #[test]
    fun test_overflowing_add() {
        let (n, z) = overflowing_add(10, 10);
        assert!(n == 20, 1);
        assert!(!z, 2);

        (n, z) = overflowing_add((MAX_U64 as u64), 1);
        assert!(n == 0, 3);
        assert!(z, 4);

        (n, z) = overflowing_add((MAX_U64 as u64), 10);
        assert!(n == 9, 5);
        assert!(z, 6);

        (n, z) = overflowing_add(5, 8);
        assert!(n == 13, 7);
        assert!(!z, 8);
    }

    #[test]
    fun test_overflowing_sub() {
        let (n, z) = overflowing_sub(10, 5);
        assert!(n == 5, 1);
        assert!(!z, 2);

        (n, z) = overflowing_sub(0, 1);
        assert!(n == (MAX_U64 as u64), 3);
        assert!(z, 4);

        (n, z) = overflowing_sub(10, 10);
        assert!(n == 0, 5);
        assert!(!z, 6);
    }
}