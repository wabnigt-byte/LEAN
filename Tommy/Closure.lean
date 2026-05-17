import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Real Set Metric

/-- The unit circle S¹ as the Euclidean circle {v | v.1² + v.2² = 1}. -/
def S1 : Set (ℝ × ℝ) := {v : ℝ × ℝ | v.1^2 + v.2^2 = 1}

/-- Primitive integer vectors: pairs (x,y) of integers with gcd = 1. -/
def P : Set (ℝ × ℝ) :=
  {v : ℝ × ℝ | ∃ (x y : ℤ), v = ((x : ℝ), (y : ℝ)) ∧ x.gcd y = 1}

/-- The projection map ϕ : ℝ² \ {0} → S¹, v ↦ v / ‖v‖. -/
noncomputable def phi (v : ℝ × ℝ) : ℝ × ℝ :=
  let norm := Real.sqrt (v.1^2 + v.2^2)
  (v.1 / norm, v.2 / norm)

/-- The set of primitive integer directions in S¹: ϕ(P). -/
def primitive_dirs : Set (ℝ × ℝ) := phi '' P

/-! ## phi properties -/

/-- phi is idempotent on S¹: if v ∈ S¹, then phi v = v. -/
theorem phi_idempotent_on_S1 (v : ℝ × ℝ) (hv : v ∈ S1) : phi v = v := by
  simp only [S1, Set.mem_setOf_eq] at hv
  simp only [phi]
  have h1 : Real.sqrt (v.1 ^ 2 + v.2 ^ 2) = 1 := by
    rw [hv, Real.sqrt_one]
  simp [h1]

/-- phi maps nonzero vectors to S¹. -/
theorem phi_mem_S1 (v : ℝ × ℝ) (hv : v ≠ (0, 0)) : phi v ∈ S1 := by
  simp only [phi, S1, Set.mem_setOf_eq]
  have hpos : 0 < v.1 ^ 2 + v.2 ^ 2 := by
    rcases not_and_or.mp (fun ⟨h1, h2⟩ => hv (Prod.ext h1 h2)) with h | h
    · have : v.1 ≠ 0 := h; positivity
    · have : v.2 ≠ 0 := h; positivity
  have hsqrt_ne : Real.sqrt (v.1 ^ 2 + v.2 ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero _ hsqrt_ne),
      Real.sq_sqrt hpos.le]

/-! ## S1 is closed -/

lemma S1_isClosed : IsClosed S1 := by
  have : S1 = (fun v : ℝ × ℝ => v.1^2 + v.2^2) ⁻¹' {1} := by ext v; simp [S1]
  rw [this]; exact isClosed_eq (by fun_prop) continuous_const

/-! ## primitive_dirs ⊆ S1 -/

lemma primitive_dirs_subset_S1 : primitive_dirs ⊆ S1 := by
  rintro _ ⟨⟨a, b⟩, ⟨x, y, hv, hgcd⟩, rfl⟩
  have ha : a = (x : ℝ) := by exact_mod_cast (Prod.ext_iff.mp hv).1
  have hb : b = (y : ℝ) := by exact_mod_cast (Prod.ext_iff.mp hv).2
  subst ha; subst hb
  simp only [S1, Set.mem_setOf_eq, phi]
  have hnonzero : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hgcd
  have hxy_pos : 0 < (x : ℝ)^2 + (y : ℝ)^2 := by
    rcases hnonzero with hx | hy
    · have : (x : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hx; positivity
    · have : (y : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hy; positivity
  have hsqrt_ne : Real.sqrt ((x : ℝ)^2 + (y : ℝ)^2) ≠ 0 :=
    (Real.sqrt_pos.mpr hxy_pos).ne'
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero _ hsqrt_ne),
      Real.sq_sqrt hxy_pos.le]

/-! ## Right half-circle parametrisation -/

noncomputable def phiRight (t : ℝ) : ℝ × ℝ :=
  (1 / Real.sqrt (1 + t^2), t / Real.sqrt (1 + t^2))

lemma phiRight_sqrt_pos (t : ℝ) : 0 < Real.sqrt (1 + t ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

lemma phiRight_cont : Continuous phiRight :=
  (continuous_const.div
    (continuous_sqrt.comp (continuous_const.add (continuous_pow 2)))
    (fun t => (phiRight_sqrt_pos t).ne')).prodMk
  (continuous_id.div
    (continuous_sqrt.comp (continuous_const.add (continuous_pow 2)))
    (fun t => (phiRight_sqrt_pos t).ne'))

lemma phi_den_num_eq_phiRight (q : ℚ) : phi ((q.den : ℝ), (q.num : ℝ)) = phiRight (q : ℝ) := by
  have hd_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.den_pos
  have hq_num : (q.num : ℝ) = (q.den : ℝ) * (q : ℝ) := by rw [Rat.cast_def]; field_simp
  show ((q.den : ℝ) / √((q.den : ℝ)^2 + (q.num : ℝ)^2),
        (q.num : ℝ) / √((q.den : ℝ)^2 + (q.num : ℝ)^2)) =
       (1 / √(1 + (q : ℝ)^2), (q : ℝ) / √(1 + (q : ℝ)^2))
  rw [hq_num, show (q.den : ℝ)^2 + ((q.den : ℝ) * (q : ℝ))^2 = (q.den : ℝ)^2 * (1 + (q : ℝ)^2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hd_pos.le]
  ext1 <;> simp only [mul_div_assoc, div_mul_eq_div_div] <;> field_simp

lemma phiRight_rat_mem_primitive_dirs (q : ℚ) : phiRight (q : ℝ) ∈ primitive_dirs := by
  rw [← phi_den_num_eq_phiRight q]
  exact Set.mem_image_of_mem _ ⟨q.den, q.num, by push_cast; rfl, by exact_mod_cast q.reduced.symm⟩

lemma phiRight_in_closure (t : ℝ) : phiRight t ∈ closure primitive_dirs := by
  apply closure_mono (show phiRight '' (range ((↑) : ℚ → ℝ)) ⊆ primitive_dirs from ?_)
  · exact mem_closure_image phiRight_cont.continuousAt (Rat.denseRange_cast t)
  · rintro v ⟨r, ⟨q, rfl⟩, rfl⟩; exact phiRight_rat_mem_primitive_dirs q

/-! ## Left half-circle parametrisation -/

noncomputable def phiLeft (t : ℝ) : ℝ × ℝ :=
  (-1 / Real.sqrt (1 + t^2), t / Real.sqrt (1 + t^2))

lemma phiLeft_sqrt_pos (t : ℝ) : 0 < Real.sqrt (1 + t ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

lemma phiLeft_cont : Continuous phiLeft :=
  (continuous_const.div
    (continuous_sqrt.comp (continuous_const.add (continuous_pow 2)))
    (fun t => (phiLeft_sqrt_pos t).ne')).prodMk
  (continuous_id.div
    (continuous_sqrt.comp (continuous_const.add (continuous_pow 2)))
    (fun t => (phiLeft_sqrt_pos t).ne'))

lemma phi_neg_den_num_eq_phiLeft (q : ℚ) :
    phi (-(q.den : ℝ), (q.num : ℝ)) = phiLeft (q : ℝ) := by
  have hd_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.den_pos
  have hq_num : (q.num : ℝ) = (q.den : ℝ) * (q : ℝ) := by rw [Rat.cast_def]; field_simp
  show (-(q.den : ℝ) / √((-(q.den : ℝ))^2 + (q.num : ℝ)^2),
        (q.num : ℝ) / √((-(q.den : ℝ))^2 + (q.num : ℝ)^2)) =
       (-1 / √(1 + (q : ℝ)^2), (q : ℝ) / √(1 + (q : ℝ)^2))
  rw [neg_sq, hq_num,
      show (q.den : ℝ)^2 + ((q.den : ℝ) * (q : ℝ))^2 = (q.den : ℝ)^2 * (1 + (q : ℝ)^2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hd_pos.le]
  have hd_ne : (q.den : ℝ) ≠ 0 := hd_pos.ne'
  ext1 <;> field_simp [hd_ne]

lemma phiLeft_rat_mem_primitive_dirs (q : ℚ) : phiLeft (q : ℝ) ∈ primitive_dirs := by
  rw [← phi_neg_den_num_eq_phiLeft q]
  have hcop : (-↑q.den : ℤ).gcd (↑q.num : ℤ) = 1 := by
    unfold Int.gcd
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    exact q.reduced.symm
  exact Set.mem_image_of_mem _
    ⟨-↑q.den, ↑q.num, by push_cast; simp, hcop⟩

lemma phiLeft_in_closure (t : ℝ) : phiLeft t ∈ closure primitive_dirs := by
  apply closure_mono (show phiLeft '' (range ((↑) : ℚ → ℝ)) ⊆ primitive_dirs from ?_)
  · exact mem_closure_image phiLeft_cont.continuousAt (Rat.denseRange_cast t)
  · rintro v ⟨r, ⟨q, rfl⟩, rfl⟩; exact phiLeft_rat_mem_primitive_dirs q

/-! ## Boundary points -/

lemma zero_one_mem_primitive_dirs : ((0 : ℝ), (1 : ℝ)) ∈ primitive_dirs :=
  ⟨(0, 1), ⟨0, 1, by push_cast; rfl, by norm_num⟩, by simp [phi, Real.sqrt_one]⟩

lemma zero_neg_one_mem_primitive_dirs : ((0 : ℝ), (-1 : ℝ)) ∈ primitive_dirs :=
  ⟨(0, -1), ⟨0, -1, by push_cast; rfl, by norm_num⟩, by simp [phi, Real.sqrt_one]⟩

/-! ## Every point of S1 is in closure primitive_dirs -/

lemma S1_subset_closure_primitive_dirs : S1 ⊆ closure primitive_dirs := by
  intro v hv
  simp only [S1, Set.mem_setOf_eq] at hv
  by_cases h1 : 0 < v.1
  · -- Right half: v = phiRight (v.2 / v.1)
    have h_v1sq_ne : v.1^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h1)
    have h_sqrt_eq : Real.sqrt (1 + (v.2 / v.1)^2) = 1 / v.1 := by
      have heq : 1 + (v.2 / v.1)^2 = 1 / v.1^2 := by
        rw [div_pow, add_div' _ _ _ h_v1sq_ne, one_mul, hv, one_div]
      rw [heq, one_div, Real.sqrt_inv, Real.sqrt_sq h1.le, one_div]
    have hv_eq : v = phiRight (v.2 / v.1) := by
      simp only [phiRight, h_sqrt_eq]
      ext1 <;> field_simp
    rw [hv_eq]; exact phiRight_in_closure _
  · by_cases h2 : v.1 < 0
    · -- Left half: v = phiLeft (v.2 / (-v.1))
      have hnv1_pos : 0 < -v.1 := neg_pos.mpr h2
      have h_nv1sq_ne : (-v.1)^2 ≠ 0 := pow_ne_zero 2 hnv1_pos.ne'
      have h_sqrt_eq : Real.sqrt (1 + (v.2 / (-v.1))^2) = 1 / (-v.1) := by
        have heq : 1 + (v.2 / (-v.1))^2 = 1 / (-v.1)^2 := by
          rw [div_pow, add_div' _ _ _ h_nv1sq_ne, one_mul, neg_sq, hv, one_div]
        rw [heq, one_div, Real.sqrt_inv, Real.sqrt_sq hnv1_pos.le, one_div]
      have hv_eq : v = phiLeft (v.2 / (-v.1)) := by
        simp only [phiLeft, h_sqrt_eq]
        have hv1_ne : v.1 ≠ 0 := ne_of_lt h2
        ext1 <;> field_simp
      rw [hv_eq]; exact phiLeft_in_closure _
    · -- Boundary: v.1 = 0, so v.2 = ±1
      have hv1_zero : v.1 = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rcases v with ⟨a, b⟩
      simp only at hv1_zero; subst hv1_zero
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hv
      rcases sq_eq_one_iff.mp hv with rfl | rfl
      · exact subset_closure zero_one_mem_primitive_dirs
      · exact subset_closure zero_neg_one_mem_primitive_dirs

/-! ## Countability of primitive_dirs -/

/-- The set P of primitive integer vectors is countable (it is a subset of ℤ × ℤ). -/
lemma P_countable : Set.Countable P := by
  apply Set.Countable.mono _ (Set.countable_univ (α := ℤ × ℤ) |>.image
    (fun p => ((p.1 : ℝ), (p.2 : ℝ))))
  rintro v ⟨x, y, rfl, _⟩
  exact ⟨(x, y), trivial, rfl⟩

/-- The set of primitive integer directions primitive_dirs = ϕ(P) is countable. -/
lemma primitive_dirs_countable : Set.Countable primitive_dirs := by
  exact P_countable.image phi

/-! ## Lebesgue measure zero for primitive_dirs -/

/-- The set of primitive integer directions has Lebesgue measure zero in ℝ².  
    This follows immediately from countability: any countable set has measure zero under  
    a non-atomic measure, and the product Lebesgue measure on ℝ × ℝ is non-atomic  
    (since ℝ has no atoms). -/
theorem primitive_dirs_volume_zero :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) primitive_dirs = 0 := by
  -- volume on ℝ × ℝ = Measure.prod volume volume (prod.measureSpace)
  -- NoAtoms on ℝ gives NoAtoms on Measure.prod via prod.instNoAtoms_fst
  haveI hna : MeasureTheory.NoAtoms
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
       (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
    MeasureTheory.Measure.prod.instNoAtoms_fst
  -- volume_eq_prod is rfl so these are definitionally equal
  exact primitive_dirs_countable.measure_zero _

/-- The same zero-measure statement after restricting ambient Lebesgue measure to the unit circle.

This is the scoped version of `primitive_dirs_volume_zero`: restriction of a measure is bounded
above by the original measure on every set, so a set of ambient volume zero also has zero measure
for the restricted measure. -/
theorem primitive_dirs_restrict_volume_zero :
    ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict S1) primitive_dirs = 0 := by
  apply le_antisymm
  · calc
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict S1) primitive_dirs
          ≤ (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) primitive_dirs :=
        MeasureTheory.Measure.restrict_apply_le S1 primitive_dirs
      _ = 0 := primitive_dirs_volume_zero
  · exact zero_le _

/-! ## Theorem 1: closure primitive_dirs = S1 -/

/-- Theorem 1: The closure of primitive integer directions equals S¹.

    Proof: For any (a, b) ∈ S¹ (a² + b² = 1):
    (1) a > 0: write (a,b) = phiRight(b/a), use density of ℚ in ℝ + continuity of phiRight.
    (2) a < 0: write (a,b) = phiLeft(b/(-a)), use density of ℚ in ℝ + continuity of phiLeft.
    (3) a = 0: then b = ±1, which are directly in primitive_dirs.
    Other direction: primitive_dirs ⊆ S¹ and S¹ is closed. -/
theorem theorem_1 : closure primitive_dirs = S1 := by
  apply Set.eq_of_subset_of_subset
  · exact S1_isClosed.closure_subset_iff.mpr primitive_dirs_subset_S1
  · exact S1_subset_closure_primitive_dirs
