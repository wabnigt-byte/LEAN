import Mathlib

open Finset ArithmeticFunction BigOperators

/-! # Visible Lattice Point Density (6/π²)

This file proves that the density of visible lattice points (coprime pairs) is 6/π².

## Step 1: Möbius count identity
## Step 2: ∑ μ(d)/d² = 6/π²
## Step 3: Density limit
-/

/-
Step 1: The number of coprime pairs in [1,N]² equals ∑_{d=1}^{N} μ(d)·⌊N/d⌋².
-/
theorem count_coprime_pairs_eq_moebius_sum (N : ℕ) (hN : 0 < N) :
    (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
        (fun p => Nat.gcd p.1 p.2 = 1)).card : ℤ) =
    ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.moebius d * (N / d : ℤ)^2 := by
  -- Let's rewrite the left-hand side of the equation using the definition of coprimality.
  have h_lhs : (↑(#({p ∈ Icc 1 N ×ˢ Icc 1 N | p.1.gcd p.2 = 1})) : ℂ) = ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (∑ d ∈ Nat.divisors (Nat.gcd p.1 p.2), (moebius d : ℂ)) := by
    have h_lhs : ∀ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (∑ d ∈ Nat.divisors (Nat.gcd p.1 p.2), (moebius d : ℂ)) = if Nat.gcd p.1 p.2 = 1 then 1 else 0 := by
      -- By definition of Möbius function, we know that $\sum_{d \mid n} \mu(d) = 1$ if $n = 1$ and $0$ otherwise.
      have h_moebius_sum : ∀ n : ℕ, n ≠ 0 → (∑ d ∈ Nat.divisors n, (moebius d : ℂ)) = if n = 1 then 1 else 0 := by
        intro n hn_ne_zero
        have h_sum : ∑ d ∈ Nat.divisors n, (ArithmeticFunction.moebius d : ℂ) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) n := by
          simp +decide [ ArithmeticFunction.moebius, ArithmeticFunction.zeta ];
          rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else if Squarefree x then ( -1 : ℂ ) ^ cardFactors x else 0 ];
          exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn_ne_zero ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
        aesop;
      exact fun p hp => h_moebius_sum _ <| Nat.ne_of_gt <| Nat.gcd_pos_of_pos_left _ <| Finset.mem_Icc.mp ( Finset.mem_product.mp hp |>.1 ) |>.1;
    rw [ Finset.sum_congr rfl h_lhs, Finset.sum_ite ] ; aesop;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (∑ d ∈ Nat.divisors (Nat.gcd p.1 p.2), (moebius d : ℂ)) = ∑ d ∈ Finset.Icc 1 N, (moebius d : ℂ) * (∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, if d ∣ p.1 ∧ d ∣ p.2 then 1 else 0) := by
    have h_fubini : ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (∑ d ∈ Nat.divisors (Nat.gcd p.1 p.2), (moebius d : ℂ)) = ∑ d ∈ Finset.Icc 1 N, (∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, if d ∣ p.1 ∧ d ∣ p.2 then (moebius d : ℂ) else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro p hp; rw [ ← Finset.sum_filter ] ; congr; ext; simp +decide [ Nat.dvd_gcd_iff ] ;
      simp +zetaDelta at *;
      exact ⟨ fun h => ⟨ ⟨ Nat.pos_of_dvd_of_pos h.1.1 hp.1.1, Nat.le_trans ( Nat.le_of_dvd hp.1.1 h.1.1 ) hp.1.2 ⟩, h.1 ⟩, fun h => ⟨ h.2, by aesop ⟩ ⟩;
    simpa only [ mul_boole, Finset.mul_sum _ _ _ ] using h_fubini;
  -- Let's simplify the inner sum $\sum_{p \in [1, N]^2} \mathbf{1}_{d \mid p.1 \land d \mid p.2}$.
  have h_inner : ∀ d ∈ Finset.Icc 1 N, (∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, if d ∣ p.1 ∧ d ∣ p.2 then 1 else 0) = (N / d) ^ 2 := by
    intros d hd
    have h_inner_sum : (∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, if d ∣ p.1 ∧ d ∣ p.2 then 1 else 0) = (∑ x ∈ Finset.Icc 1 N, if d ∣ x then 1 else 0) * (∑ y ∈ Finset.Icc 1 N, if d ∣ y then 1 else 0) := by
      erw [ Finset.sum_product, Finset.sum_mul ];
      exact Finset.sum_congr rfl fun x hx => by split_ifs <;> simp +decide [ * ] ;
    simp_all +decide [ sq ];
    rw [ show { x ∈ Finset.Icc 1 N | d ∣ x } = Finset.image ( fun x => d * x ) ( Finset.Icc 1 ( N / d ) ) from ?_, Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( by linarith ) hxy ] ; aesop;
    ext x; simp [Finset.mem_image];
    exact ⟨ fun hx => ⟨ x / d, ⟨ by nlinarith [ Nat.div_mul_cancel hx.2 ], Nat.div_le_div_right hx.1.2 ⟩, by rw [ mul_comm, Nat.div_mul_cancel hx.2 ] ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith, by nlinarith [ Nat.div_mul_le_self N d ] ⟩, by simp +decide ⟩ ⟩;
  simp_all +decide [ Finset.sum_ite ];
  convert h_lhs using 1;
  norm_num [ ← @Int.cast_inj ℂ ];
  rw [ Finset.sum_congr rfl ] ; intros ; aesop

/-
Step 2: The Dirichlet series ∑ μ(d)/d² converges to 6/π².
-/
theorem moebius_sum_inv_sq_eq :
    HasSum (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)^2)
           (6 / Real.pi^2) := by
  -- We use the Möbius-zeta product identity: $\zeta(s) \sum_{d=1}^{\infty} \frac{\mu(d)}{d^s} = 1$.
  have h_prod : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s * riemannZeta s = 1 := by
    exact fun s hs => by rw [ mul_comm, ← LSeries_one_eq_riemannZeta hs, ← LSeries_one_mul_Lseries_moebius hs ] ;
  have h_eval : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 = 6 / Real.pi ^ 2 := by
    -- By definition of the Riemann zeta function, we know that $\zeta(2) = \frac{\pi^2}{6}$.
    have h_zeta2 : riemannZeta 2 = Real.pi ^ 2 / 6 := by
      exact riemannZeta_two;
    exact eq_one_div_of_mul_eq_one_left ( h_prod 2 ( by norm_num ) ) ▸ h_zeta2.symm ▸ by norm_num;
  -- We use the fact that the L-series is the sum of the terms of the series.
  have h_sum : HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ 2) (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) := by
    convert Summable.hasSum _ using 1;
    · exact tsum_congr fun n => by unfold LSeries.term; aesop;
    · contrapose! h_eval;
      rw [ LSeries ];
      rw [ tsum_eq_zero_of_not_summable ];
      · exact Ne.symm <| div_ne_zero ( by norm_num ) <| pow_ne_zero 2 <| Complex.ofReal_ne_zero.mpr <| by positivity;
      · convert h_eval using 1;
        exact iff_of_eq ( by congr; ext n; unfold LSeries.term; aesop );
  convert Complex.hasSum_re h_sum using 1;
  · norm_num [ div_eq_mul_inv ];
    norm_cast ; norm_num [ sq ];
    ext; by_cases h : ‹_› = 0 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm ] ;
  · exact h_eval.symm ▸ by norm_cast;

/-
Step 3: The density of coprime pairs in [1,N]² tends to 6/π².
-/
theorem visible_density :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
            (fun p => Nat.gcd p.1 p.2 = 1)).card : ℝ) / (N : ℝ)^2)
      Filter.atTop (nhds (6 / Real.pi^2)) := by
  -- We'll use the fact that $\sum_{d=1}^{N} \mu(d) \cdot \lfloor N/d \rfloor^2$ can be rewritten as $\sum_{d=1}^{N} \mu(d) \cdot (N/d)^2 + O(N \log N)$.
  have h_sum_rewrite : ∀ N : ℕ, N ≥ 1 →
    |(((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.gcd p.1 p.2 = 1)).card : ℝ) / N^2 - (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / d^2)| ≤ (2 * (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d) + 1) / N := by
      intro N hN
      have h_sum_rewrite : |(((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.gcd p.1 p.2 = 1)).card : ℝ) - (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * (N / d : ℝ)^2)| ≤ 2 * (∑ d ∈ Finset.Icc 1 N, (N / d : ℝ)) + N := by
        have h_sum_rewrite : |(((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.gcd p.1 p.2 = 1)).card : ℝ) - (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * (N / d : ℝ)^2)| ≤ ∑ d ∈ Finset.Icc 1 N, |(ArithmeticFunction.moebius d : ℝ) * ((N / d : ℝ)^2 - (N / d : ℕ)^2)| := by
          have h_sum_rewrite : |(((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.gcd p.1 p.2 = 1)).card : ℝ) - (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * (N / d : ℝ)^2)| = |∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ)^2 - (N / d : ℝ)^2)| := by
            have h_sum_rewrite : (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.gcd p.1 p.2 = 1)).card : ℝ) = ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * (N / d : ℕ)^2 := by
              convert count_coprime_pairs_eq_moebius_sum N hN using 1;
              norm_num [ ← @Int.cast_inj ℝ ];
              congr! 2;
            simp +decide [ h_sum_rewrite, mul_sub ];
          exact h_sum_rewrite.symm ▸ le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun x hx => by rw [ ← abs_neg ] ; ring_nf; norm_num );
        -- We'll use the fact that $|\mu(d)| \leq 1$ and $|(N/d)^2 - (N/d)^2| \leq 2N/d + 1$.
        have h_bound : ∀ d ∈ Finset.Icc 1 N, |(ArithmeticFunction.moebius d : ℝ) * ((N / d : ℝ)^2 - (N / d : ℕ)^2)| ≤ 2 * (N / d : ℝ) + 1 := by
          intros d hd
          have h_abs : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
            simp +decide [ ArithmeticFunction.moebius ];
            split_ifs <;> norm_num
          have h_diff : |((N / d : ℝ)^2 - (N / d : ℕ)^2)| ≤ 2 * (N / d : ℝ) + 1 := by
            rw [ abs_le ];
            constructor <;> nlinarith only [ show ( N : ℝ ) / d ≥ ↑ ( N / d ) by exact_mod_cast Nat.cast_div_le .., show ( N : ℝ ) / d ≤ ↑ ( N / d ) + 1 by exact le_of_lt <| by rw [ div_lt_iff₀ <| Nat.cast_pos.mpr <| Finset.mem_Icc.mp hd |>.1 ] ; norm_cast ; linarith [ Nat.div_add_mod N d, Nat.mod_lt N <| Finset.mem_Icc.mp hd |>.1 ] ]
          exact abs_le.mpr ⟨by nlinarith only [abs_le.mp h_abs, abs_le.mp h_diff], by nlinarith only [abs_le.mp h_abs, abs_le.mp h_diff]⟩;
        exact h_sum_rewrite.trans ( le_trans ( Finset.sum_le_sum h_bound ) ( by simp +decide [ Finset.mul_sum _ _ _, Finset.sum_add_distrib ] ) );
      convert div_le_div_of_nonneg_right h_sum_rewrite ( sq_nonneg ( N : ℝ ) ) using 1;
      · rw [ show ( ∑ d ∈ Finset.Icc 1 N, ( moebius d : ℝ ) * ( N / d ) ^ 2 ) = ( ∑ d ∈ Finset.Icc 1 N, ( moebius d : ℝ ) / d ^ 2 ) * N ^ 2 by rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring ];
        rw [ div_sub', abs_div, abs_sq ] ; ring ; positivity;
      · simp +decide [ div_eq_mul_inv, sq, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, ne_of_gt ( zero_lt_one.trans_le hN ) ];
        simp +decide [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, ne_of_gt ( zero_lt_one.trans_le hN ) ];
  -- We'll use the fact that $\sum_{d=1}^{N} \frac{1}{d}$ is bounded by $\log N + 1$.
  have h_harmonic_bound : ∀ N : ℕ, N ≥ 1 → (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d) ≤ Real.log N + 1 := by
    intro N hN; induction' hN with N hN ih <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
    rw [ show ( N : ℝ ) + 1 = N * ( 1 + ( N : ℝ ) ⁻¹ ) by nlinarith only [ mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ) ], Real.log_mul ( by positivity ) ( by positivity ) ];
    nlinarith [ inv_pos.mpr ( by positivity : 0 < ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ), Real.log_inv ( 1 + ( N : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + ( N : ℝ ) ⁻¹ ) ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ) ];
  -- Using the bounds, we can show that the difference tends to zero.
  have h_diff_zero : Filter.Tendsto (fun N : ℕ => (2 * (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d) + 1) / N) Filter.atTop (nhds 0) := by
    -- We'll use the fact that $\frac{\log N}{N}$ tends to $0$ as $N$ tends to infinity.
    have h_log_div_N_zero : Filter.Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
      suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
        exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    refine' squeeze_zero_norm' _ _;
    use fun N => ( 2 * ( Real.log N + 1 ) + 1 ) / N;
    · filter_upwards [ Filter.eventually_ge_atTop 1 ] with N hN using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; aesop;
    · ring_nf;
      simpa using Filter.Tendsto.add ( h_log_div_N_zero.mul_const 2 ) ( tendsto_inv_atTop_nhds_zero_nat.mul_const 3 );
  -- Using the bounds, we can show that the difference tends to zero, hence the limit is $6 / \pi^2$.
  have h_limit : Filter.Tendsto (fun N : ℕ => (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / d^2)) Filter.atTop (nhds (6 / Real.pi^2)) := by
    have := moebius_sum_inv_sq_eq;
    convert this.tendsto_sum_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) using 1;
    exact funext fun n => by erw [ Function.comp_apply, Finset.sum_Ico_eq_sub _ ] <;> norm_num;
  simpa using h_limit.add ( squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun N hN => h_sum_rewrite N hN ⟩ ) h_diff_zero )