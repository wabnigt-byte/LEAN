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

open Real Set Metric

def S1 : Set (ℝ × ℝ) := {v : ℝ × ℝ | v.1^2 + v.2^2 = 1}
def P : Set (ℝ × ℝ) :=
  {v : ℝ × ℝ | ∃ (x y : ℤ), v = ((x : ℝ), (y : ℝ)) ∧ x.gcd y = 1}
noncomputable def phi (v : ℝ × ℝ) : ℝ × ℝ :=
  let norm := Real.sqrt (v.1^2 + v.2^2)
  (v.1 / norm, v.2 / norm)
def primitive_dirs : Set (ℝ × ℝ) := phi '' P

lemma S1_isClosed : IsClosed S1 := by
  have : S1 = (fun v : ℝ × ℝ => v.1^2 + v.2^2) ⁻¹' {1} := by ext v; simp [S1]
  rw [this]; exact isClosed_eq (by fun_prop) continuous_const

lemma primitive_dirs_subset_S1 : primitive_dirs ⊆ S1 := by
  rintro _ ⟨⟨a, b⟩, ⟨x, y, hv, hgcd⟩, rfl⟩
  have ha : a = (x : ℝ) := by exact_mod_cast (Prod.ext_iff.mp hv).1
  have hb : b = (y : ℝ) := by exact_mod_cast (Prod.ext_iff.mp hv).2
  subst ha; subst hb
  simp only [S1, Set.mem_setOf_eq, phi]
  have hnonzero : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h; push_neg at h; simp [h.1, h.2] at hgcd
  have hxy_pos : 0 < (x : ℝ)^2 + (y : ℝ)^2 := by
    rcases hnonzero with hx | hy
    · have : (x : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hx; positivity
    · have : (y : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hy; positivity
  have hsqrt_ne : Real.sqrt ((x : ℝ)^2 + (y : ℝ)^2) ≠ 0 :=
    (Real.sqrt_pos.mpr hxy_pos).ne'
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero _ hsqrt_ne),
      Real.sq_sqrt hxy_pos.le]

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

lemma zero_one_mem_primitive_dirs : ((0 : ℝ), (1 : ℝ)) ∈ primitive_dirs :=
  ⟨(0, 1), ⟨0, 1, by push_cast; rfl, by norm_num⟩, by simp [phi, Real.sqrt_one]⟩

lemma zero_neg_one_mem_primitive_dirs : ((0 : ℝ), (-1 : ℝ)) ∈ primitive_dirs :=
  ⟨(0, -1), ⟨0, -1, by push_cast; rfl, by norm_num⟩, by simp [phi, Real.sqrt_one]⟩

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

theorem theorem_1 : closure primitive_dirs = S1 := by
  apply Set.eq_of_subset_of_subset
  · exact S1_isClosed.closure_subset_iff.mpr primitive_dirs_subset_S1
  · exact S1_subset_closure_primitive_dirs
