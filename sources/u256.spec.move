spec u256::u256 {
    spec fun max_u256(): num {
         (U128_MAX << 128) + U128_MAX
    }

    spec fun num_val(a: U256): num {
        a.v0 + (a.v1 << 64) + (a.v2 << 128) + (a.v3 << 192)
    }

    spec max {
        ensures num_val(result) == max_u256();
    }

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

    spec zero {
        aborts_if false;
        ensures result.v0 == 0;
        ensures result.v1 == 0;
        ensures result.v2 == 0;
        ensures result.v3 == 0;
        ensures num_val(result) == 0;
    }

    spec from_u128 {
        aborts_if false;
        ensures num_val(result) == val;
    }

    spec from_u64 {
        aborts_if false;
        ensures num_val(result) == val;
    }

    spec sub {
        pragma verify = false;
    }

    spec mul {
        pragma verify = false;
    }

    spec div {
        pragma verify = false;
    }

    spec shr {
        pragma verify = false;
    }

    spec shl {
        pragma verify = false;
    }

    spec du256_to_u256 {
        pragma verify = false;
    }

    spec add {
        ensures num_val(result) == num_val(a) + num_val(b);
    }
}
