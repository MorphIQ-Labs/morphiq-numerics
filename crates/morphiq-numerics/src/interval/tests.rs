use super::{FiniteInterval as I, IntervalError as E};
#[test]
fn constructors_and_domain_failures() {
    for v in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(I::point(v), Err(E::InvalidBounds));
    }
    assert_eq!(I::new(2., 1.), Err(E::InvalidBounds));
    assert_eq!(I::new(0., 1.).unwrap().checked_ln(), Err(E::Domain));
    assert_eq!(I::new(-1., 1.).unwrap().checked_sqrt(), Err(E::Domain));
    assert_eq!(
        I::point(1.).unwrap().checked_div(I::new(-1., 1.).unwrap()),
        Err(E::Domain)
    );
    assert_eq!(
        I::point(f64::MAX)
            .unwrap()
            .checked_add(I::point(f64::MAX).unwrap()),
        Err(E::Range)
    );
    assert_eq!(I::point(1000.).unwrap().checked_exp(), Err(E::Range));
}
#[test]
fn subnormal_uncertainty_is_not_erased() {
    let got = I::point(-1000.).unwrap().checked_exp().unwrap();
    assert_eq!(got.lower(), 0.);
    assert_eq!(got.upper().to_bits(), 1);
    let got = I::point(f64::from_bits(1))
        .unwrap()
        .checked_mul(I::point(0.5).unwrap())
        .unwrap();
    assert_eq!(got.lower().to_bits(), (-f64::from_bits(1)).to_bits());
    assert_eq!(got.upper().to_bits(), 1);
}

#[test]
fn independent_reference_endpoints_match_bit_for_bit() {
    use crate::test_exact::{entries, field, word};
    const FIXTURE: &str = include_str!("../../../reference/fixtures/interval.json");
    let cases = entries(FIXTURE, &["cases"]);
    assert_eq!(cases.len(), 4072);
    for case in cases {
        let a = I::new(word(case, "al"), word(case, "au")).unwrap();
        let b = I::new(word(case, "bl"), word(case, "bu")).unwrap();
        let result = match field(case, "op") {
            "add" => a.checked_add(b),
            "sub" => a.checked_sub(b),
            "mul" => a.checked_mul(b),
            "div" => a.checked_div(b),
            "square" => a.checked_square(),
            "ln" => a.checked_ln(),
            "exp" => a.checked_exp(),
            "sqrt" => a.checked_sqrt(),
            op => panic!("unexpected operation {op}"),
        };
        match field(case, "status") {
            "range" => assert_eq!(result, Err(E::Range), "{case}"),
            "domain" => assert_eq!(result, Err(E::Domain), "{case}"),
            "ok" => {
                let result = result.unwrap_or_else(|e| panic!("{case}: {e:?}"));
                assert_eq!(
                    result.lower().to_bits(),
                    word(case, "lo").to_bits(),
                    "{case}"
                );
                assert_eq!(
                    result.upper().to_bits(),
                    word(case, "hi").to_bits(),
                    "{case}"
                );
                assert!(result.lower().is_finite());
                assert!(result.upper().is_finite());
                assert!(result.lower() <= result.upper());
            }
            status => panic!("unexpected status {status}"),
        }
    }
}

#[test]
fn exact_transforms_and_membership() {
    for (l, u, al, au) in [
        (2., 3., 2.0_f64, 3.0_f64),
        (-3., -2., 2., 3.),
        (-3., 0., 0., 3.),
        (-3., -0., 0., 3.),
        (-3., 2., 0., 3.),
        (-2., 3., 0., 3.),
        (-0., 0., 0., 0.),
        (0., 0., 0., 0.),
    ] {
        let a = I::new(l, u).unwrap();
        assert!(a.contains(l));
        assert!(a.contains(u));
        for v in [
            l.next_down(),
            u.next_up(),
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
        ] {
            assert!(!a.contains(v));
        }
        assert_eq!(a.negated().lower().to_bits(), (-u).to_bits());
        assert_eq!(a.negated().upper().to_bits(), (-l).to_bits());
        assert_eq!(a.abs().lower().to_bits(), al.to_bits());
        assert_eq!(a.abs().upper().to_bits(), au.to_bits());
        assert_eq!(a.negated().negated(), a);
    }
    for (a, b, expected) in [
        ((-3., 1.), (-2., 4.), (-2.0_f64, 4.0_f64)),
        ((-2., 4.), (-3., 1.), (-2., 4.)),
        ((-3., 4.), (-2., 1.), (-2., 4.)),
        ((-2., 1.), (-3., 4.), (-2., 4.)),
        ((-0., -0.), (0., 0.), (0., 0.)),
        ((0., 0.), (-0., -0.), (0., 0.)),
        ((0., 0.), (1., 1.), (1., 1.)),
        ((1., 1.), (0., 0.), (1., 1.)),
        ((0., 0.), (-1., -1.), (0., 0.)),
        ((-1., -1.), (0., 0.), (0., 0.)),
    ] {
        let got = I::new(a.0, a.1).unwrap().max(I::new(b.0, b.1).unwrap());
        assert_eq!(got.lower().to_bits(), expected.0.to_bits());
        assert_eq!(got.upper().to_bits(), expected.1.to_bits());
    }
    for v in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(I::new(v, 1.), Err(E::InvalidBounds));
        assert_eq!(I::new(-1., v), Err(E::InvalidBounds));
    }
}
