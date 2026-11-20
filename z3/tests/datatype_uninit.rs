//! Regression test for `create_datatypes` reading its output buffer uninitialized when Z3
//! rejects the datatypes.
//!
//! It lives in its own file so that cargo builds it as a separate test binary: if the bug
//! comes back and this segfaults, only this binary dies, and cargo still reports the failure.

use z3::DatatypeAccessor;
use z3::DatatypeBuilder;
use z3::datatype_builder::create_datatypes;

#[test]
fn test_non_well_founded_datatypes_do_not_read_uninitialized_sorts() {
    const N: usize = 6;
    // `N` mutually recursive datatypes with no base case, which Z3 rejects.
    let builders = (0..N)
        .map(|i| {
            DatatypeBuilder::new(format!("T{i}")).variant(
                &format!("c{i}"),
                vec![("f", DatatypeAccessor::datatype(format!("T{}", (i + 1) % N)))],
            )
        })
        .collect::<Vec<_>>();
    // Leave non-null garbage in freed allocations of the size `create_datatypes` uses for its
    // output buffer, so that reading it uninitialized fails loudly. This relies on the
    // allocator reusing freed memory (as glibc's does); elsewhere the test still checks that
    // an error is returned.
    drop(
        (0..256)
            .map(|_| vec![0x4141_4141_4141_4140usize; N])
            .collect::<Vec<_>>(),
    );
    assert!(create_datatypes(builders).is_err());
}
