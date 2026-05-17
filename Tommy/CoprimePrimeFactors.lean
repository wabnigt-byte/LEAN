import Mathlib

/-! # Coprimality via disjoint prime factor sets

Two equivalent views of "visible" / "coprime":

1. **Lattice point (x, y):** the point is visible from the origin iff `gcd(x, y) = 1`,
   which is equivalent to the prime factor sets of `x` and `y` being disjoint.

2. **Fraction x/y:** a fraction is in lowest terms iff the numerator and denominator
   share no prime factor, i.e. their prime factor sets are disjoint.

Both reduce to the Mathlib fact `Nat.disjoint_primeFactors`.
-/

/-- A lattice point `(x, y)` is visible (coprime) iff the prime-factor sets of
`x` and `y` are disjoint. -/
theorem coprime_iff_primeFactors_disjoint (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Nat.Coprime x y ↔ Disjoint x.primeFactors y.primeFactors :=
  (Nat.disjoint_primeFactors hx hy).symm

/-- A rational number in lowest terms (as every `ℚ` value is) has disjoint prime-factor
sets between numerator and denominator. -/
theorem rat_reduced_primeFactors_disjoint (q : ℚ) (hnum : q.num ≠ 0) :
    Disjoint q.num.natAbs.primeFactors q.den.primeFactors :=
  (Nat.disjoint_primeFactors (Int.natAbs_ne_zero.mpr hnum) q.den_ne_zero).mpr q.reduced
