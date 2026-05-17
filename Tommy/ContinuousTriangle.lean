import Mathlib

/-!
# Continuous Area Mapping: Geometric Uniformity

The continuous analogue of the empirical CDF result. On the continuous triangle
`{(X,Y) : 0 ≤ X ≤ Y ≤ N}`, the ratio `X/Y` is uniformly distributed on `[0,1]`.

Specifically, for `r ∈ [0,1]`:
  P(X/Y ≤ r) = area({(X,Y) : 0 ≤ X ≤ rY, 0 ≤ Y ≤ N}) / area(triangle)
             = (r · N² / 2) / (N² / 2)
             = r

This result is independent of N, making the asymptotic limit transparent.

We formalize this as: the Lebesgue measure of the sub-triangle
`{(x,y) : 0 ≤ x ≤ r*y, 0 ≤ y ≤ N}` equals `r` times the measure of the full triangle.
-/

open MeasureTheory Set

noncomputable section

/-- The full triangle {(x,y) : 0 ≤ x ≤ y ≤ N}. -/
def fullTriangle (N : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ N}

/-- The sub-triangle {(x,y) : 0 ≤ x ≤ r·y, 0 ≤ y ≤ N} for r ∈ [0,1]. -/
def subTriangle (N r : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ r * p.2 ∧ 0 ≤ p.2 ∧ p.2 ≤ N}

/-
The sub-triangle is contained in the full triangle when r ∈ [0,1].
-/
theorem subTriangle_subset (N r : ℝ) (hN : 0 ≤ N) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    subTriangle N r ⊆ fullTriangle N := by
  exact fun p hp => ⟨ hp.1, by nlinarith [ hp.2.1, hp.2.2 ], by nlinarith [ hp.2.1, hp.2.2.2 ] ⟩

/-
The Lebesgue measure of the full triangle is N²/2.
-/
theorem volume_fullTriangle (N : ℝ) (hN : 0 < N) :
    MeasureTheory.volume (fullTriangle N) = ENNReal.ofReal (N ^ 2 / 2) := by
  erw [ MeasureTheory.Measure.prod_apply ];
  · -- Let's simplify the integral.
    have h_integral : ∫⁻ (x : ℝ), volume (Prod.mk x ⁻¹' fullTriangle N) = ∫⁻ (x : ℝ) in Set.Icc 0 N, ENNReal.ofReal (N - x) := by
      rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator, fullTriangle ];
      congr with x ; by_cases hx : 0 ≤ x <;> by_cases hx' : x ≤ N <;> simp +decide [ *, Set.Icc_def ];
    rw [ h_integral, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
    · rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN.le, intervalIntegral.integral_sub ] <;> norm_num ; ring;
    · exact Continuous.integrableOn_Icc ( by continuity );
    · exact Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Icc ) fun x hx => sub_nonneg.2 hx.2;
  · exact MeasurableSet.inter ( measurableSet_le measurable_const measurable_fst ) ( MeasurableSet.inter ( measurableSet_le measurable_fst measurable_snd ) ( measurableSet_le measurable_snd measurable_const ) )

/-
The Lebesgue measure of the sub-triangle is r·N²/2.
-/
theorem volume_subTriangle (N r : ℝ) (hN : 0 < N) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    MeasureTheory.volume (subTriangle N r) = ENNReal.ofReal (r * N ^ 2 / 2) := by
  -- The set can be described as {(x, y) | 0 ≤ x ≤ ry ∧ 0 ≤ y ≤ N}.
  have h_desc : subTriangle N r = {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ r * p.2 ∧ 0 ≤ p.2 ∧ p.2 ≤ N} := by
    grind;
  -- We can rewrite the set as $\{ (x, y) \mid 0 \leq y \leq N, 0 \leq x \leq ry \}$.
  have h_set_eq : subTriangle N r = {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ N ∧ 0 ≤ p.1 ∧ p.1 ≤ r * p.2} := by
    exact h_desc.trans ( by ext; aesop );
  -- We can rewrite the set as $\{ (x, y) \mid 0 \leq y \leq N, 0 \leq x \leq ry \}$ and use Fubini's theorem.
  have h_fubini : ∫⁻ (p : ℝ × ℝ) in subTriangle N r, 1 = ∫⁻ (y : ℝ) in Set.Icc 0 N, ∫⁻ (x : ℝ) in Set.Icc 0 (r * y), 1 := by
    rw [ h_set_eq, ← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator ];
    · erw [ MeasureTheory.lintegral_prod_symm ];
      · congr with y ; by_cases hy : 0 ≤ y <;> by_cases hy' : y ≤ N <;> simp +decide [ *, Set.indicator ];
        rw [ show ( ∫⁻ x : ℝ, if 0 ≤ x ∧ x ≤ r * y then 1 else 0 ) = ∫⁻ x : ℝ in Set.Icc 0 ( r * y ), 1 by rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ] ] ; norm_num [ hy, hy', hr0, hr1 ];
      · exact Measurable.aemeasurable ( by exact Measurable.indicator measurable_const <| by exact MeasurableSet.inter ( measurableSet_le measurable_const measurable_snd ) <| MeasurableSet.inter ( measurableSet_le measurable_snd measurable_const ) <| MeasurableSet.inter ( measurableSet_le measurable_const measurable_fst ) <| measurableSet_le measurable_fst <| measurable_const.mul measurable_snd );
    · norm_num;
    · exact MeasurableSet.inter ( measurableSet_le measurable_const measurable_snd ) ( MeasurableSet.inter ( measurableSet_le measurable_snd measurable_const ) ( MeasurableSet.inter ( measurableSet_le measurable_const measurable_fst ) ( measurableSet_le measurable_fst ( measurable_const.mul measurable_snd ) ) ) );
  convert h_fubini using 1;
  · norm_num;
  · norm_num [ ← ENNReal.ofReal_mul, hN.le ];
    rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
    · rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] <;> norm_num [ mul_comm r ] ; ring ; linarith;
    · exact Continuous.integrableOn_Icc ( by continuity );
    · exact Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Icc ) fun x hx => mul_nonneg hr0 hx.1

/-
**Geometric uniformity:** The ratio of sub-triangle to full triangle area equals r.
    This is the continuous analogue showing X/Y ~ U(0,1).
-/
theorem geometric_uniformity (N r : ℝ) (hN : 0 < N) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (MeasureTheory.volume (subTriangle N r)).toReal /
      (MeasureTheory.volume (fullTriangle N)).toReal = r := by
  rw [ volume_subTriangle N r hN hr0 hr1, volume_fullTriangle N hN, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, div_eq_iff ] <;> ring <;> positivity

end