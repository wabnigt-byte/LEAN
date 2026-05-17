import Mathlib

/-!
# Empirical CDF of Rational Ratios on the Triangular Grid

We formalize the "analytic bridge" from the asymptotic uniformity paper.

Given the triangular grid `S_N = {(p,q) ∈ ℕ² | 1 ≤ p ≤ q ≤ N}`, with `|S_N| = N(N+1)/2`,
the empirical CDF of `p/q` at `x ∈ [0,1]` is

  `F_N(x) = C_N(x) / |S_N|`

where `C_N(x) = Σ_{q=1}^{N} ⌊xq⌋` counts pairs with `p/q ≤ x`.

Using the floor bounds `xq - 1 < ⌊xq⌋ ≤ xq`, we get the squeeze:

  `x - 2/(N+1) < F_N(x) ≤ x`

which gives `F_N(x) → x` as `N → ∞`, i.e., the CDF of U(0,1).
-/

open Finset Filter

noncomputable section

/-- The size of the triangular grid S_N = {(p,q) : 1 ≤ p ≤ q ≤ N}. -/
def triangleSize (N : ℕ) : ℕ := N * (N + 1) / 2

/-- The count C_N(x) = Σ_{q=1}^{N} ⌊xq⌋, counting pairs (p,q) in S_N with p/q ≤ x. -/
def cdfCount (N : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 N, (⌊x * (q : ℝ)⌋₊ : ℝ)

/-- The empirical CDF F_N(x) = C_N(x) / |S_N|. -/
def empiricalCDF (N : ℕ) (x : ℝ) : ℝ :=
  cdfCount N x / ((N : ℝ) * ((N : ℝ) + 1) / 2)

/-
Triangle size is positive for N ≥ 1.
-/
lemma triangleSize_pos (N : ℕ) (hN : 0 < N) : (0 : ℝ) < (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  positivity

/-
Upper bound on C_N(x): each ⌊xq⌋ ≤ xq, so C_N(x) ≤ x · N(N+1)/2.
-/
lemma cdfCount_le_mul (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    cdfCount N x ≤ x * ((N : ℝ) * ((N : ℝ) + 1) / 2) := by
  exact le_trans ( Finset.sum_le_sum fun i hi => Nat.floor_le <| mul_nonneg hx <| Nat.cast_nonneg i ) <| by induction' N with N ih <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at * ; nlinarith;

/-
Lower bound on C_N(x): each ⌊xq⌋ > xq - 1, so C_N(x) > x·N(N+1)/2 - N.
-/
lemma mul_lt_cdfCount (N : ℕ) (hN : 0 < N) (x : ℝ) (_hx : 0 ≤ x) :
    x * ((N : ℝ) * ((N : ℝ) + 1) / 2) - (N : ℝ) < cdfCount N x := by
  have h_floor : ∀ q ∈ Finset.Icc 1 N, ⌊x * q⌋₊ ≥ x * q - 1 := by
    exact fun q hq => le_of_lt ( Nat.sub_one_lt_floor _ );
  -- Apply induction on $N$ to show that $cdfCount N x > x * (N * (N + 1)) / 2 - N$.
  induction' N with N ih;
  · contradiction;
  · rcases N.eq_zero_or_pos with rfl | hN <;> simp_all +decide [ cdfCount ];
    · linarith [ Nat.lt_floor_add_one x ];
    · erw [ Finset.sum_Ioc_succ_top, add_comm ] <;> norm_num;
      have := ih fun q hq₁ hq₂ => h_floor q hq₁ ( by linarith ) ; have := h_floor ( N + 1 ) ( by linarith ) ( by linarith ) ; norm_num at * ; nlinarith!;

/-
Upper bound on the empirical CDF: F_N(x) ≤ x.
-/
theorem empiricalCDF_le (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : 0 ≤ x) :
    empiricalCDF N x ≤ x := by
  exact div_le_of_le_mul₀ ( by positivity ) ( by positivity ) ( cdfCount_le_mul N x hx )

/-
Lower bound on the empirical CDF: x - 2/(N+1) < F_N(x).
-/
theorem lt_empiricalCDF (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : 0 ≤ x) :
    x - 2 / ((N : ℝ) + 1) < empiricalCDF N x := by
  unfold empiricalCDF;
  rw [ lt_div_iff₀ ] <;> nlinarith [ show ( N : ℝ ) > 0 by positivity, div_mul_cancel₀ ( 2 : ℝ ) ( by positivity : ( N : ℝ ) + 1 ≠ 0 ), mul_lt_cdfCount N hN x hx ]

/-
**Asymptotic Uniformity (Analytic Bridge):**
    The empirical CDF of p/q on the triangular grid S_N converges pointwise to x,
    i.e., to the CDF of the uniform distribution U(0,1).
-/
theorem empiricalCDF_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun N => empiricalCDF (N + 1) x) atTop (nhds x) := by
  refine' ( tendsto_of_tendsto_of_tendsto_of_le_of_le _ tendsto_const_nhds _ _ );
  exact fun N => x - 2 / ( N + 2 );
  · exact le_trans ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ) ( by norm_num );
  · intro N;
    exact le_of_lt ( by have := lt_empiricalCDF ( N + 1 ) ( Nat.succ_pos _ ) x hx; norm_num at *; ring_nf at *; linarith );
  · exact fun N => empiricalCDF_le _ ( Nat.succ_pos _ ) _ hx

end