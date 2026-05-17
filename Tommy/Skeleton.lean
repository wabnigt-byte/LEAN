import Tommy.Thomae
import Tommy.Closure
import Tommy.Torus
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Thomae Arithmetic Skeleton Embedding into the Farey Torus

This module formalizes the **arithmetic skeleton embedding**: the map that sends
each nonzero integer lattice point `(x, y) ∈ ℤ² \ {(0,0)}` to a point in the
Farey torus `S¹ × [0,1] / ~`.

## Main definitions

* `thomae_cylinder_embedding` — map `{p : ℤ × ℤ // p ≠ (0,0)} → Cylinder` with:
    - angle = `phi ((x : ℝ), (y : ℝ))` (projection onto S¹)
    - height = `(tau p : ℝ)` as an element of `Set.Icc 0 1`
* `thomae_torus_embedding` — composition with the quotient map `Cylinder → FareyTorus`.

## Main lemma

* `visible_maps_to_top` — if `tau p = 1` (equivalently p is visible), the height
  coordinate of `thomae_cylinder_embedding p` equals 1.

## Scope

Density/closure of the image in the torus, continuity, and homeomorphism are
**not** attempted here (Category D).
-/

open Set Real

namespace ThomaeSkeleton

/-! ## The embedding into the cylinder -/

/-- For a nonzero integer pair `p`, the real cast is nonzero in `ℝ × ℝ`. -/
private lemma real_cast_nonzero {p : ℤ × ℤ} (h : p ≠ (0, 0)) :
    ((p.1 : ℝ), (p.2 : ℝ)) ≠ (0, 0) := by
  intro heq
  apply h
  have heq1 : (p.1 : ℝ) = 0 := congr_arg Prod.fst heq
  have heq2 : (p.2 : ℝ) = 0 := congr_arg Prod.snd heq
  have h1 : p.1 = 0 := by exact_mod_cast heq1
  have h2 : p.2 = 0 := by exact_mod_cast heq2
  exact Prod.ext h1 h2

/-- The real cast vector has positive squared norm for nonzero integer pairs. -/
private lemma real_cast_norm_pos {p : ℤ × ℤ} (h : p ≠ (0, 0)) :
    0 < (p.1 : ℝ)^2 + (p.2 : ℝ)^2 := by
  by_contra hle
  push_neg at hle
  have hle' : (p.1 : ℝ)^2 + (p.2 : ℝ)^2 ≤ 0 := hle
  have h1sq : 0 ≤ (p.1 : ℝ)^2 := sq_nonneg _
  have h2sq : 0 ≤ (p.2 : ℝ)^2 := sq_nonneg _
  have h1z : (p.1 : ℝ)^2 = 0 := le_antisymm (by linarith) h1sq
  have h2z : (p.2 : ℝ)^2 = 0 := le_antisymm (by linarith) h2sq
  have hp1 : (p.1 : ℝ) = 0 := by nlinarith [sq_nonneg (p.1 : ℝ)]
  have hp2 : (p.2 : ℝ) = 0 := by nlinarith [sq_nonneg (p.2 : ℝ)]
  apply real_cast_nonzero h
  simp [show (p.1 : ℝ) = 0 from hp1, show (p.2 : ℝ) = 0 from hp2]

/-- `phi` of a nonzero real-cast integer pair lands in S¹. -/
private lemma phi_real_cast_mem_S1 {p : ℤ × ℤ} (h : p ≠ (0, 0)) :
    phi ((p.1 : ℝ), (p.2 : ℝ)) ∈ S1 := by
  simp only [phi, S1, Set.mem_setOf_eq]
  have hpos := real_cast_norm_pos h
  have hsqrt_ne : Real.sqrt ((p.1 : ℝ)^2 + (p.2 : ℝ)^2) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero _ hsqrt_ne),
      Real.sq_sqrt hpos.le]

/-- The tau value of a nonzero pair, cast to ℝ, lies in [0, 1]. -/
private lemma tau_mem_Icc {p : ℤ × ℤ} (h : p ≠ (0, 0)) :
    (tau p : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · -- 0 ≤ (tau p : ℝ)
    have hpos : 0 < tau p := tau_pos_of_nonzero h
    exact_mod_cast le_of_lt hpos
  · -- (tau p : ℝ) ≤ 1
    have hle : tau p ≤ 1 := tau_le_one_of_nonzero h
    exact_mod_cast hle

/-- The Thomae cylinder embedding:
    each nonzero integer pair maps to `(phi(x,y), tau(x,y)) ∈ S¹ × [0,1]`. -/
noncomputable def thomae_cylinder_embedding
    (p : {p : ℤ × ℤ // p ≠ (0, 0)}) : Cylinder :=
  ⟨⟨phi ((p.val.1 : ℝ), (p.val.2 : ℝ)), phi_real_cast_mem_S1 p.property⟩,
   ⟨(tau p.val : ℝ), tau_mem_Icc p.property⟩⟩

/-- The Thomae torus embedding: compose with the Farey quotient map. -/
noncomputable def thomae_torus_embedding
    (p : {p : ℤ × ℤ // p ≠ (0, 0)}) : FareyTorus :=
  Quotient.mk fareySetoid (thomae_cylinder_embedding p)

/-! ## Sanity-check lemma -/

/-- If `tau p = 1` (i.e. p is a visible lattice point), then the height
    coordinate of `thomae_cylinder_embedding p` equals 1.

    This exposes the projection: the height slot of the cylinder point is
    exactly the tau value cast to ℝ. -/
theorem visible_maps_to_top
    (p : {p : ℤ × ℤ // p ≠ (0, 0)})
    (h : tau p.val = 1) :
    (thomae_cylinder_embedding p).2.1 = 1 := by
  simp only [thomae_cylinder_embedding]
  exact_mod_cast h

/-- Variant: if p is in visibleLattice, then the height equals 1. -/
theorem visibleLattice_maps_to_top
    (p : {p : ℤ × ℤ // p ≠ (0, 0)})
    (hv : p.val ∈ visibleLattice) :
    (thomae_cylinder_embedding p).2.1 = 1 := by
  apply visible_maps_to_top
  exact (tau_eq_one_iff_visible p.property).mpr hv

end ThomaeSkeleton
