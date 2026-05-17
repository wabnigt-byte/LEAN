import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Topology.Constructions.SumProd

open Real Set Metric

def P : Set (ℝ × ℝ) := {v : ℝ × ℝ | ∃ (x y : ℤ), v = ((x : ℝ), (y : ℝ)) ∧ x.gcd y = 1}
noncomputable def phi (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.1 / Real.sqrt (v.1^2 + v.2^2), v.2 / Real.sqrt (v.1^2 + v.2^2))
def primitive_dirs : Set (ℝ × ℝ) := phi '' P

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

-- For every t : ℝ, phiRight t ∈ closure primitive_dirs
lemma phiRight_in_closure (t : ℝ) : phiRight t ∈ closure primitive_dirs := by
  apply closure_mono (show phiRight '' (range ((↑) : ℚ → ℝ)) ⊆ primitive_dirs from ?_)
  · -- phiRight(t) ∈ closure (phiRight '' range ↑)
    apply mem_closure_image phiRight_cont.continuousAt
    exact Rat.denseRange_cast.dense_range.mono (subset_univ _) |>.closure_eq ▸ mem_univ _
  · -- phiRight '' range ↑ ⊆ primitive_dirs
    rintro v ⟨t, ⟨q, rfl⟩, rfl⟩
    exact phiRight_rat_mem_primitive_dirs q

