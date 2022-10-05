spec u256::u256 {
    // Spec functions.

    spec fun max_u256(): num {
        (U128_MAX * (0xffffffffffffffffffffffffffffffffu128 + 1)) + U128_MAX
    }

    spec fun num_val(a: U256): num {
        a.v0
            + (a.v1 * 0x10000000000000000u128)
            + (a.v2 * (0xffffffffffffffffffffffffffffffffu128 + 1))
            + (a.v3 * ((0xffffffffffffffffffffffffffffffffu128 + 1) * 0x10000000000000000u128))
    }

    // Zero & max.

    spec max {
        aborts_if false;
        ensures result.v0 == U64_MAX;
        ensures result.v1 == U64_MAX;
        ensures result.v2 == U64_MAX;
        ensures result.v3 == U64_MAX;
        ensures num_val(result) == max_u256();
    }

    spec zero {
        aborts_if false;
        ensures result.v0 == 0;
        ensures result.v1 == 0;
        ensures result.v2 == 0;
        ensures result.v3 == 0;
        ensures num_val(result) == 0;
    }

    // Internal get/put.

    spec get {
        aborts_if i > 3 with EWORDS_OVERFLOW;
        ensures i == 0 ==> result == a.v0;
        ensures i == 1 ==> result == a.v1;
        ensures i == 2 ==> result == a.v2;
        ensures i == 3 ==> result == a.v3;
    }

    spec put {
        aborts_if i > 3 with EWORDS_OVERFLOW;
        ensures i == 0 ==> a.v0 == val;
        ensures i == 1 ==> a.v1 == val;
        ensures i == 2 ==> a.v2 == val;
        ensures i == 3 ==> a.v3 == val;
    }

    // 'From' functions.

    spec from_u128 {
        aborts_if false;
        ensures num_val(result) == val;
    }

    spec from_u64 {
        aborts_if false;
        ensures num_val(result) == val;
    }

    // 'As' functions.

    spec as_u128 {
        aborts_if num_val(a) > U128_MAX with ECAST_OVERFLOW;
        ensures result == num_val(a);
    }

    spec as_u64 {
        aborts_if num_val(a) > U64_MAX with ECAST_OVERFLOW;
        ensures result == num_val(a);
    }

    // Compare.

    spec compare {
        aborts_if false;
        ensures num_val(a) > num_val(b) ==> result == GREATER_THAN;
        ensures num_val(a) < num_val(b) ==> result == LESS_THAN;
        ensures num_val(a) == num_val(b) ==> result == EQUAL;
    }

    // Basic math functions (add, sub, mul, div).

    spec add {
        aborts_if num_val(a) + num_val(b) > max_u256() with EOVERFLOW;
        ensures num_val(result) == num_val(a) + num_val(b);
    }

    spec sub {
        aborts_if num_val(a) - num_val(b) < 0 with EOVERFLOW;
        ensures num_val(result) == num_val(a) - num_val(b);
    }

    spec mul {
        pragma verify = false;
        aborts_if (num_val(a) * num_val(b)) > max_u256() with EOVERFLOW;
        ensures num_val(result) == num_val(a) * num_val(b);
    }

    spec div {
        pragma opaque;
        pragma verify = false;
        ensures num_val(result) == num_val(a) / num_val(b);
    }

    // Shifts.

    spec shr {
        pragma verify = false;
        ensures num_val(result) == num_val(a) >> shift;
    }

    spec shl {
        pragma verify = false;
        ensures num_val(result) == num_val(a) << shift;
    }

    // Internal functions.

    spec bitxor {
        pragma verify = false;
    }

    spec bitand {
        pragma verify = false;
    }

    spec bitor {
        pragma verify = false;
    }

    spec bitnot {
        pragma verify = false;
    }

    spec div_recursive {
        pragma verify = false;
    }

    spec bitnot {
        pragma verify = false;
    }

    spec leading_zeros_u64_block {
        pragma verify = false;
    }

    spec leading_zeros_u4 {
        pragma verify = false;
    }

    spec leading_zeros_u8 {
        pragma verify = false;
    }

}
