import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.GCD
import Tommy.Thomae

/-!
# SL(2,ℤ) preserves gcd on ℤ × ℤ

This file proves that the standard linear action of SL(2,ℤ) on integer pairs
preserves the gcd of the two components.

## Main definitions

* `Modular.SL2Z` — abbreviation for `Matrix.SpecialLinearGroup (Fin 2) ℤ`
* `Modular.sl2Act` — explicit linear action of SL(2,ℤ) on ℤ × ℤ

## Main results

* `Modular.sl2_preserves_gcd` — `Int.gcd (sl2Act M v).1 (sl2Act M v).2 = Int.gcd v.1 v.2`
* `Modular.sl2Act_ne_zero` — `v ≠ (0, 0) → sl2Act M v ≠ (0, 0)`
* `Modular.tau_sl2_invariant` — `v ≠ (0, 0) → tau (sl2Act M v) = tau v`
* `Modular.sl2_preserves_visibleLattice` — `v ∈ visibleLattice → sl2Act M v ∈ visibleLattice`

## Proof sketch

Factor out `d := gcd(v.1, v.2)`: write `v.1 = d * a`, `v.2 = d * b` with `IsCoprime a b`.
Then `sl2Act M v = (d * x, d * y)` where `(x, y)` are coprime by
`IsCoprime.mulVecSL` (Mathlib).  Apply `Int.gcd_mul_left` and `Int.isCoprime_iff_gcd_eq_one`.
-/

open Matrix MatrixGroups

namespace Modular

/-- Abbreviation for the special linear group SL(2,ℤ). -/
abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-- The explicit linear action of SL(2,ℤ) on ℤ × ℤ by left matrix multiplication. -/
def sl2Act (M : SL2Z) (v : ℤ × ℤ) : ℤ × ℤ :=
  (M.val 0 0 * v.1 + M.val 0 1 * v.2,
   M.val 1 0 * v.1 + M.val 1 1 * v.2)

/-- Helper: if `a` and `b` are coprime, so are the entries of `M * ![a, b]` for `M ∈ SL(2,ℤ)`.
This follows directly from `IsCoprime.mulVecSL` in Mathlib. -/
private lemma mulVecSL_components (M : SL2Z) (a b : ℤ) (h : IsCoprime a b) :
    IsCoprime (M.val 0 0 * a + M.val 0 1 * b) (M.val 1 0 * a + M.val 1 1 * b) := by
  have hv : IsCoprime (![a, b] 0) (![a, b] 1) := by simp [h]
  have hmv := hv.mulVecSL M
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
             Matrix.cons_val_one] at hmv
  exact hmv

/-- **SL(2,ℤ) preserves gcd**: the action of any `M ∈ SL(2,ℤ)` on `v : ℤ × ℤ` via
    `sl2Act` does not change `Int.gcd v.1 v.2`. -/
theorem sl2_preserves_gcd (M : SL2Z) (v : ℤ × ℤ) :
    Int.gcd (sl2Act M v).1 (sl2Act M v).2 = Int.gcd v.1 v.2 := by
  -- Fix d = gcd(v.1, v.2) as a natural number.
  set d : ℕ := Int.gcd v.1 v.2 with hd_def
  cases Nat.eq_zero_or_pos d with
  | inl h0 =>
    -- d = 0 iff v.1 = v.2 = 0; then sl2Act M v = (0, 0) as well.
    have ⟨hv1, hv2⟩ := Int.gcd_eq_zero_iff.mp (hd_def ▸ h0 : v.1.gcd v.2 = 0)
    simp [sl2Act, hv1, hv2]; omega
  | inr hpos =>
    -- d > 0: write v.1 = d * a, v.2 = d * b.
    have hdv1 : (d : ℤ) ∣ v.1 := Int.gcd_dvd_left (a := v.1) (b := v.2)
    have hdv2 : (d : ℤ) ∣ v.2 := Int.gcd_dvd_right (a := v.1) (b := v.2)
    set a := v.1 / (d : ℤ)
    set b := v.2 / (d : ℤ)
    have ha : v.1 = (d : ℤ) * a := (Int.mul_ediv_cancel' hdv1).symm
    have hb : v.2 = (d : ℤ) * b := (Int.mul_ediv_cancel' hdv2).symm
    -- a and b are coprime: from Int.gcd_mul_left and the definition of d.
    have hab_cop : IsCoprime a b := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hmul := Int.gcd_mul_left (d : ℤ) a b
      rw [← ha, ← hb, Int.natAbs_natCast, ← hd_def] at hmul
      exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
    -- Unfold sl2Act and substitute v.1 = d*a, v.2 = d*b.
    simp only [sl2Act]
    conv_lhs => rw [ha, hb]
    -- Factor d out of both output components.
    rw [show M.val 0 0 * ((d : ℤ) * a) + M.val 0 1 * ((d : ℤ) * b) =
          (d : ℤ) * (M.val 0 0 * a + M.val 0 1 * b) from by ring,
        show M.val 1 0 * ((d : ℤ) * a) + M.val 1 1 * ((d : ℤ) * b) =
          (d : ℤ) * (M.val 1 0 * a + M.val 1 1 * b) from by ring,
        -- Apply Int.gcd_mul_left: gcd(d*x, d*y) = d.natAbs * gcd(x, y).
        Int.gcd_mul_left, Int.natAbs_natCast,
        -- The coprimeness of the new entries follows from mulVecSL.
        Int.isCoprime_iff_gcd_eq_one.mp (mulVecSL_components M a b hab_cop),
        Nat.mul_one]

/-! ## Nonzero preservation -/

/-- **sl2Act maps nonzero to nonzero**: if `v ≠ (0, 0)` then `sl2Act M v ≠ (0, 0)`.

Proof: if `sl2Act M v = (0, 0)` then `Int.gcd` of the output is 0,
so by `sl2_preserves_gcd` the gcd of `v` is also 0,
so by `Int.gcd_eq_zero_iff` we get `v = (0, 0)` — contradiction. -/
theorem sl2Act_ne_zero (M : SL2Z) (v : ℤ × ℤ) (h : v ≠ (0, 0)) :
    sl2Act M v ≠ (0, 0) := by
  intro hzero
  -- If sl2Act M v = (0, 0), both components are 0.
  have h1 : (sl2Act M v).1 = 0 := by rw [hzero]
  have h2 : (sl2Act M v).2 = 0 := by rw [hzero]
  -- Then gcd of the output is 0.
  have hgcd_out : Int.gcd (sl2Act M v).1 (sl2Act M v).2 = 0 := by
    simp [h1, h2, Int.gcd]
  -- By sl2_preserves_gcd, gcd of the input is also 0.
  have hgcd_in : Int.gcd v.1 v.2 = 0 := by
    rw [← sl2_preserves_gcd M v]; exact hgcd_out
  -- By Int.gcd_eq_zero_iff, v = (0, 0).
  have ⟨hv1, hv2⟩ := Int.gcd_eq_zero_iff.mp hgcd_in
  exact h (Prod.ext hv1 hv2)

/-- Iff version: `sl2Act M v = (0, 0) ↔ v = (0, 0)`. -/
theorem sl2Act_eq_zero_iff (M : SL2Z) (v : ℤ × ℤ) :
    sl2Act M v = (0, 0) ↔ v = (0, 0) := by
  constructor
  · intro hzero
    by_contra h
    exact sl2Act_ne_zero M v h hzero
  · intro hv
    simp [sl2Act, hv]

/-! ## τ is SL(2,ℤ)-invariant -/

/-- **τ is SL(2,ℤ)-invariant**: for any nonzero `v : ℤ × ℤ` and `M : SL2Z`,
    `tau (sl2Act M v) = tau v`.

Proof: both sides equal `1 / Int.gcd v.1 v.2` because `sl2_preserves_gcd` equates
the gcds, and `sl2Act_ne_zero` ensures the output is nonzero. -/
theorem tau_sl2_invariant (M : SL2Z) (v : ℤ × ℤ) (h : v ≠ (0, 0)) :
    tau (sl2Act M v) = tau v := by
  have hout : sl2Act M v ≠ (0, 0) := sl2Act_ne_zero M v h
  rw [tau_of_nonzero hout, tau_of_nonzero h]
  congr 1
  -- Both sides are (Int.gcd ... : ℚ), equal by sl2_preserves_gcd.
  have := sl2_preserves_gcd M v
  exact_mod_cast congrArg (Nat.cast (R := ℚ)) this

/-! ## SL(2,ℤ) restricts to the visible lattice -/

/-- **SL(2,ℤ) preserves the visible lattice**: if `v ∈ visibleLattice` then
    `sl2Act M v ∈ visibleLattice`.

Proof: visibleLattice requires `v ≠ (0,0)` and `gcd = 1`.
`sl2Act_ne_zero` gives the nonzero condition; `sl2_preserves_gcd` preserves `gcd = 1`. -/
theorem sl2_preserves_visibleLattice (M : SL2Z) (v : ℤ × ℤ)
    (h : v ∈ visibleLattice) : sl2Act M v ∈ visibleLattice := by
  obtain ⟨hne, hgcd⟩ := h
  constructor
  · exact sl2Act_ne_zero M v hne
  · rw [sl2_preserves_gcd]; exact hgcd

/-! ## Standard generators of SL(2,ℤ) -/

/-- The S generator of SL(2,ℤ): rotation by π/2, i.e. [[0,-1],[1,0]]. -/
def S_gen : SL2Z := ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

/-- The T generator of SL(2,ℤ): shear, i.e. [[1,1],[0,1]]. -/
def T_gen : SL2Z := ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two]⟩

/-- The action of S on a pair (a, b) gives (-b, a). -/
theorem sl2Act_S (v : ℤ × ℤ) : sl2Act S_gen v = (-v.2, v.1) := by
  simp [sl2Act, S_gen, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The action of T on a pair (a, b) gives (a + b, b). -/
theorem sl2Act_T (v : ℤ × ℤ) : sl2Act T_gen v = (v.1 + v.2, v.2) := by
  simp [sl2Act, T_gen, Matrix.cons_val_zero, Matrix.cons_val_one]

end Modular
