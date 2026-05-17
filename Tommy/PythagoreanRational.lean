import Mathlib
import Tommy.Closure

open Real Set

/-! # Pythagorean-Rational Classification

We prove that for integer pairs (x,y) ≠ (0,0), the first (resp. second) coordinate
of `phi(x,y)` is rational if and only if (x,y) is an integer multiple of a
Pythagorean pair (a,b) with a² + b² = c², c ≠ 0.

## Proof outline

The key equivalence chain is:
1. `x / √(x²+y²) ∈ ℚ` ↔ `√(x²+y²) ∈ ℚ` (for integer x,y with (x,y) ≠ (0,0))
2. `√(x²+y²) ∈ ℚ` ↔ `x²+y² is a perfect square` (√n rational for n:ℕ iff n = m²)
3. `x²+y² is a perfect square` ↔ the Pythagorean-triple RHS condition
-/

/-! ## Key lemma: √n rational implies n is a perfect square -/

/-
If √n is rational for a natural number n, then n is a perfect square.
-/
theorem sqrt_nat_rational_iff_sq (n : ℕ) :
    (∃ q : ℚ, (q : ℝ) = Real.sqrt (n : ℝ)) ↔ ∃ m : ℕ, n = m ^ 2 := by
  refine' ⟨ fun ⟨ q, hq ⟩ => _, fun ⟨ m, hm ⟩ => ⟨ m, _ ⟩ ⟩;
  · have := congr_arg ( · ^ 2 ) hq; norm_num at this;
    exact ⟨ q.num.natAbs, by norm_cast at this; simpa [ ← Int.natCast_inj, sq, Rat.mul_self_num ] using congr_arg Rat.num this.symm ⟩;
  · norm_num [ hm ]

/-! ## The RHS condition is equivalent to x²+y² being a perfect square -/

/-
The Pythagorean-multiple condition is equivalent to x²+y² being a perfect square.
-/
theorem pyth_multiple_iff_sum_sq_is_sq (x y : ℤ) (h : (x, y) ≠ (0, 0)) :
    (∃ a b c : ℤ, a ^ 2 + b ^ 2 = c ^ 2 ∧ c ≠ 0 ∧ ∃ k : ℤ, x = k * a ∧ y = k * b) ↔
    ∃ c : ℤ, x ^ 2 + y ^ 2 = c ^ 2 := by
  constructor;
  · rintro ⟨ a, b, c, h₁, h₂, k, rfl, rfl ⟩ ; exact ⟨ k * c, by linear_combination' h₁ * k ^ 2 ⟩ ;
  · exact fun ⟨ c, hc ⟩ => ⟨ x, y, c, hc, by rintro rfl; exact h <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩, 1, by norm_num, by norm_num ⟩

/-! ## Rationality of x/√(x²+y²) ↔ √(x²+y²) is rational -/

private lemma int_pair_sq_sum_pos {x y : ℤ} (h : (x, y) ≠ (0, 0)) :
    (0 : ℝ) < (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
  exact mod_cast not_le.mp fun hx => h <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩

private lemma sqrt_int_pair_ne_zero {x y : ℤ} (h : (x, y) ≠ (0, 0)) :
    Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos.mpr (int_pair_sq_sum_pos h))

/-
For integer x,y with (x,y)≠(0,0), x/√(x²+y²) is rational iff √(x²+y²) is rational.
-/
theorem div_sqrt_rational_iff_sqrt_rational (x y : ℤ) (h : (x, y) ≠ (0, 0)) :
    (∃ q : ℚ, (q : ℝ) = (x : ℝ) / Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) ↔
    (∃ q : ℚ, (q : ℝ) = Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) := by
  constructor <;> intro hq;
  · -- If $x = 0$, then $y \neq 0$ and $\sqrt{x^2 + y^2} = |y|$ which is rational.
    by_cases hx : x = 0;
    · exact ⟨ |y|, by simp +decide [ hx, Real.sqrt_sq_eq_abs ] ⟩;
    · exact ⟨ x / hq.choose, by push_cast; rw [ hq.choose_spec, div_div_cancel₀ ( by positivity ) ] ⟩;
  · exact ⟨ x / hq.choose, by push_cast; rw [ hq.choose_spec, div_eq_mul_inv ] ⟩

/-
Analogous: y/√(x²+y²) is rational iff √(x²+y²) is rational.
-/
theorem div_sqrt_rational_iff_sqrt_rational' (x y : ℤ) (h : (x, y) ≠ (0, 0)) :
    (∃ q : ℚ, (q : ℝ) = (y : ℝ) / Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) ↔
    (∃ q : ℚ, (q : ℝ) = Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) := by
  constructor <;> intro hq;
  · by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide;
    · exact ⟨ |y|, by simp +decide [ Real.sqrt_sq_eq_abs ] ⟩;
    · exact ⟨ |x|, by simp +decide [ Real.sqrt_sq_eq_abs ] ⟩;
    · exact ⟨ y / hq.choose, by push_cast; rw [ hq.choose_spec, div_div_cancel₀ ( by positivity ) ] ⟩;
  · exact ⟨ y / hq.choose, by push_cast; rw [ hq.choose_spec, div_eq_mul_inv ] ⟩

/-! ## Bridge: √(x²+y²) rational ↔ x²+y² perfect square -/

/-
√(x²+y²) is rational iff x²+y² is a perfect integer square.
-/
theorem sqrt_sum_sq_rational_iff_perfect_sq (x y : ℤ) (h : (x, y) ≠ (0, 0)) :
    (∃ q : ℚ, (q : ℝ) = Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) ↔
    ∃ c : ℤ, x ^ 2 + y ^ 2 = c ^ 2 := by
  constructor;
  · rintro ⟨ q, hq ⟩;
    -- Squaring both sides of the equation $q = \sqrt{x^2 + y^2}$, we get $q^2 = x^2 + y^2$.
    have hq_sq : q^2 = x^2 + y^2 := by
      simpa [ ← @Rat.cast_inj ℝ ] using hq.symm ▸ Real.sq_sqrt <| by positivity;
    exact ⟨ q.num, by norm_cast at hq_sq; simpa only [ sq, Rat.mul_self_num ] using congr_arg Rat.num hq_sq.symm ⟩;
  · rintro ⟨ c, hc ⟩ ; use c.natAbs; norm_cast; simp +decide ;
    rw [ eq_comm, Real.sqrt_eq_iff_mul_self_eq ] <;> norm_cast <;> cases abs_cases c <;> nlinarith

/-! ## Main theorems -/

/-
First coordinate of phi is rational iff (x,y) is a Pythagorean multiple.
-/
theorem phi_rational_first_coord_iff (x y : ℤ) (h : (x, y) ≠ (0, 0)) :
    (∃ q : ℚ, (phi ((x : ℝ), (y : ℝ))).1 = (q : ℝ)) ↔
    (∃ a b c : ℤ, a ^ 2 + b ^ 2 = c ^ 2 ∧ c ≠ 0 ∧ ∃ k : ℤ, x = k * a ∧ y = k * b) := by
  convert div_sqrt_rational_iff_sqrt_rational x y h using 1;
  · exact exists_congr fun q => eq_comm;
  · rw [ pyth_multiple_iff_sum_sq_is_sq x y h, sqrt_sum_sq_rational_iff_perfect_sq x y h ]

/-
Second coordinate of phi is rational iff (x,y) is a Pythagorean multiple.
-/
theorem phi_rational_second_coord_iff (x y : ℤ) (h : (x, y) ≠ (0, 0)) :
    (∃ q : ℚ, (phi ((x : ℝ), (y : ℝ))).2 = (q : ℝ)) ↔
    (∃ a b c : ℤ, a ^ 2 + b ^ 2 = c ^ 2 ∧ c ≠ 0 ∧ ∃ k : ℤ, x = k * a ∧ y = k * b) := by
  simp_all +decide [ phi ];
  convert div_sqrt_rational_iff_sqrt_rational' x y ( by aesop ) using 1;
  · simp +decide only [eq_comm];
  · convert ( pyth_multiple_iff_sum_sq_is_sq x y ( by aesop ) ) using 1;
    convert sqrt_sum_sq_rational_iff_perfect_sq x y ( by aesop ) using 1