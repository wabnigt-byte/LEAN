import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Zify

/-!
# Thomae Projection and Visible Lattice Points

This module defines the Thomae projection τ and the visible lattice, and proves
the listed properties with complete Lean proofs.

- `tau : ℤ × ℤ → ℚ` — the Thomae projection τ(x,y) = 1/gcd(|x|,|y|) for (x,y)≠(0,0), 0 at origin.
- `visibleLattice` — nonzero integer pairs (x,y) with gcd(|x|,|y|) = 1.
- `tau_eq_one_iff_gcd_one` — τ(x,y) = 1 ↔ gcd = 1 (nonzero pair).
- `tau_eq_one_iff_visible` — τ(x,y) = 1 ↔ (x,y) ∈ visibleLattice (nonzero pair).
- `tau_invariant_flipX/Y/neg` — invariance under sign flips (all four quadrants).
- `tau_quadrant_invariant` — invariance under arbitrary sign combinations.
- `tau_symm` — symmetry in x and y.
- `tau_le_one_of_nonzero` — τ(x,y) ≤ 1 for nonzero pairs.
- `tau_pos_of_nonzero` — τ(x,y) > 0 for nonzero pairs.
- `semiprime_quadratic` — g(pq) + 1 = p + q for distinct primes p, q.
- `semiprime_quadratic_roots` — root identity: p² + pq = (p+q)·p.
-/

/-- The Thomae projection: τ(x,y) = 1/gcd(|x|,|y|) for (x,y)≠(0,0), and 0 at origin. -/
noncomputable def tau (p : ℤ × ℤ) : ℚ :=
  let g := Int.gcd p.1 p.2
  if g = 0 then 0 else 1 / (g : ℚ)

/-- The visible lattice points: nonzero integer pairs with gcd = 1. -/
def visibleLattice : Set (ℤ × ℤ) :=
  {p : ℤ × ℤ | p ≠ (0, 0) ∧ Int.gcd p.1 p.2 = 1}

/-! ## Basic lemmas about Int.gcd -/

/-- For nonzero (x,y), Int.gcd x y ≠ 0. -/
lemma int_gcd_ne_zero_of_nonzero {x y : ℤ} (h : (x, y) ≠ (0, 0)) : Int.gcd x y ≠ 0 := by
  intro hgcd
  apply h
  have hx : Int.natAbs x = 0 := (Nat.gcd_eq_zero_iff.mp hgcd).1
  have hy : Int.natAbs y = 0 := (Nat.gcd_eq_zero_iff.mp hgcd).2
  simp [Int.natAbs_eq_zero.mp hx, Int.natAbs_eq_zero.mp hy]

/-- Int.gcd is positive for nonzero pairs. -/
lemma int_gcd_pos_of_nonzero {x y : ℤ} (h : (x, y) ≠ (0, 0)) : 0 < Int.gcd x y :=
  Nat.pos_of_ne_zero (int_gcd_ne_zero_of_nonzero h)

/-! ## tau definitions -/

/-- tau at a nonzero pair is 1/gcd. -/
lemma tau_of_nonzero {p : ℤ × ℤ} (h : p ≠ (0, 0)) : tau p = 1 / (Int.gcd p.1 p.2 : ℚ) := by
  simp only [tau, if_neg (int_gcd_ne_zero_of_nonzero h)]

/-- tau at the origin is 0. -/
@[simp]
lemma tau_zero : tau (0, 0) = 0 := by
  simp [tau, Int.gcd]

/-- tau(x,y) > 0 for (x,y) ≠ (0,0). -/
lemma tau_pos_of_nonzero {p : ℤ × ℤ} (h : p ≠ (0, 0)) : 0 < tau p := by
  rw [tau_of_nonzero h]
  apply div_pos one_pos
  have : 0 < Int.gcd p.1 p.2 := int_gcd_pos_of_nonzero h
  exact_mod_cast this

/-! ## tau = 1 iff gcd = 1 -/

/-- tau(x,y) = 1 iff gcd(x,y) = 1, for nonzero (x,y). -/
theorem tau_eq_one_iff_gcd_one {p : ℤ × ℤ} (h : p ≠ (0, 0)) :
    tau p = 1 ↔ Int.gcd p.1 p.2 = 1 := by
  rw [tau_of_nonzero h, one_div]
  constructor
  · intro heq
    -- heq : (Int.gcd p.1 p.2 : ℚ)⁻¹ = 1
    have hg_pos : (0 : ℚ) < (Int.gcd p.1 p.2 : ℚ) := by
      exact_mod_cast int_gcd_pos_of_nonzero h
    have hg_ne : (Int.gcd p.1 p.2 : ℚ) ≠ 0 := ne_of_gt hg_pos
    have hg1 : (Int.gcd p.1 p.2 : ℚ) = 1 := by
      rw [← inv_inv (Int.gcd p.1 p.2 : ℚ), heq]
      simp
    have : Int.gcd p.1 p.2 = 1 := by exact_mod_cast hg1
    exact this
  · intro heq
    -- heq : Int.gcd p.1 p.2 = 1
    have : (Int.gcd p.1 p.2 : ℚ) = 1 := by exact_mod_cast heq
    rw [this]
    simp

/-- tau(x,y) = 1 iff (x,y) is a visible lattice point (for nonzero pairs). -/
theorem tau_eq_one_iff_visible {p : ℤ × ℤ} (h : p ≠ (0, 0)) :
    tau p = 1 ↔ p ∈ visibleLattice := by
  rw [tau_eq_one_iff_gcd_one h]
  constructor
  · intro hgcd
    exact ⟨h, hgcd⟩
  · intro hv
    exact hv.2

/-! ## Quadrant invariance: sign flips -/

/-- tau is invariant under sign flip in x. -/
theorem tau_invariant_flipX (x y : ℤ) : tau (-x, y) = tau (x, y) := by
  simp only [tau, Int.gcd, Int.natAbs_neg]

/-- tau is invariant under sign flip in y. -/
theorem tau_invariant_flipY (x y : ℤ) : tau (x, -y) = tau (x, y) := by
  simp only [tau, Int.gcd, Int.natAbs_neg]

/-- tau is invariant under negating both coordinates. -/
theorem tau_invariant_neg (x y : ℤ) : tau (-x, -y) = tau (x, y) := by
  simp only [tau, Int.gcd, Int.natAbs_neg]

/-- tau is symmetric in its arguments. -/
theorem tau_symm (x y : ℤ) : tau (x, y) = tau (y, x) := by
  simp only [tau, Int.gcd, Nat.gcd_comm]

/-- tau is invariant under all four sign-flip combinations of (x, y). -/
theorem tau_quadrant_invariant (x y : ℤ) (sx sy : Bool) :
    tau (if sx then -x else x, if sy then -y else y) = tau (x, y) := by
  -- All four cases: (ff,ff) = id; (ff,tt) = flipY; (tt,ff) = flipX; (tt,tt) = neg
  cases sx <;> cases sy
  · simp
  · exact tau_invariant_flipY x y
  · exact tau_invariant_flipX x y
  · exact tau_invariant_neg x y

/-! ## Visible lattice -/

/-- visibleLattice equals the set of primitive integer vectors. -/
theorem visibleLattice_eq_primitiveVectors :
    visibleLattice = {p : ℤ × ℤ | p ≠ (0 : ℤ × ℤ) ∧ Int.gcd p.1 p.2 = 1} := rfl

/-- The origin is not a visible lattice point. -/
theorem origin_not_visible : (⟨0, 0⟩ : ℤ × ℤ) ∉ visibleLattice := by
  simp [visibleLattice]

/-- For any nonzero (x,y), tau(x,y) ≤ 1. -/
theorem tau_le_one_of_nonzero {p : ℤ × ℤ} (h : p ≠ (0, 0)) : tau p ≤ 1 := by
  rw [tau_of_nonzero h, one_div]
  apply inv_le_one_of_one_le₀
  have : 1 ≤ Int.gcd p.1 p.2 := int_gcd_pos_of_nonzero h
  exact_mod_cast this

/-! ## Semiprime quadratic identity -/

/-- Semiprime quadratic identity: for distinct primes p, q,
    g(p*q) + 1 = p + q, where g(n) = n - φ(n).
    This means p and q are roots of X² - (p+q)·X + pq = (X-p)(X-q). -/
theorem semiprime_quadratic (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    p * q - Nat.totient (p * q) + 1 = p + q := by
  have hpq_cop : Nat.Coprime p q :=
    hp.coprime_iff_not_dvd.mpr fun hdvd =>
      hpq (hq.eq_one_or_self_of_dvd p hdvd |>.resolve_left hp.one_lt.ne')
  have htot : Nat.totient (p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul hpq_cop, Nat.totient_prime hp, Nat.totient_prime hq]
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  -- (p-1)*(q-1) ≤ p*q in ℕ
  have h_sub : (p - 1) * (q - 1) ≤ p * q := by
    calc (p - 1) * (q - 1) ≤ p * (q - 1) := Nat.mul_le_mul_right _ (Nat.sub_le p 1)
      _ ≤ p * q := Nat.mul_le_mul_left _ (Nat.sub_le q 1)
  rw [htot]
  -- Use zify to lift ℕ subtraction to ℤ arithmetic
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp.ne_zero
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne_zero
  zify [h_sub, hp1, hq1]
  ring

/-- Algebraic root identity: p² + pq = (p+q)·p and q² + pq = (p+q)·q. -/
theorem semiprime_quadratic_roots (p q : ℕ) :
    p * p + p * q = (p + q) * p ∧ q * q + p * q = (p + q) * q := by
  constructor <;> ring

/-! ## Concrete tau evaluations -/

/-- tau(1,0) = 1 (the pair (1,0) is visible). -/
@[simp] theorem tau_one_zero : tau ((1 : ℤ), (0 : ℤ)) = 1 := by
  rw [tau_of_nonzero (by decide)]; simp [Int.gcd]

/-- tau(0,1) = 1 (the pair (0,1) is visible). -/
@[simp] theorem tau_zero_one : tau ((0 : ℤ), (1 : ℤ)) = 1 := by
  rw [tau_of_nonzero (by decide)]; simp [Int.gcd]

/-- tau(2,0) = 1/2. -/
theorem tau_two_zero : tau ((2 : ℤ), (0 : ℤ)) = 1 / 2 := by
  rw [tau_of_nonzero (by decide)]; simp [Int.gcd]

/-- (1,1) is visible: gcd(1,1) = 1. -/
@[simp] theorem tau_one_one : tau ((1 : ℤ), (1 : ℤ)) = 1 := by
  rw [tau_of_nonzero (by decide)]; simp [Int.gcd]

/-- tau(2,3) = 1 since gcd(2,3) = 1. -/
theorem tau_two_three : tau ((2 : ℤ), (3 : ℤ)) = 1 := by
  rw [tau_of_nonzero (by decide)]; native_decide

/-- tau(2,4) = 1/2 since gcd(2,4) = 2. -/
theorem tau_two_four : tau ((2 : ℤ), (4 : ℤ)) = 1 / 2 := by
  rw [tau_of_nonzero (by decide)]; native_decide
