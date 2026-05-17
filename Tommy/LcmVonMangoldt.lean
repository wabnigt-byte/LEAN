import Mathlib

/-! # p-adic valuation of lcm(1..N) and exp(ψ) = lcm

This file proves:
1. `padicValNat p (lcm(1..N)) = Nat.log p N` for prime p, N ≥ 1.
2. `log(lcm(1..N)) = ∑_{p prime ≤ N} (Nat.log p N) · log p`.
3. `∑_{n=2}^{N} Λ(n) = ∑_{p prime ≤ N} (Nat.log p N) · log p` (von Mangoldt regrouping).
4. `exp(ψ(N)) = lcm(1..N)` (rank 28 closing theorem).
-/

open Finset

/-
The p-adic valuation of lcm(1, 2, …, N) equals ⌊log_p N⌋.
-/
theorem padic_val_lcm_range (N : ℕ) (p : ℕ) (hp : p.Prime) (hN : 0 < N) :
    padicValNat p (Finset.lcm (Finset.Icc 1 N) id) =
    Nat.log p N := by
  -- By definition of $p$-adic valuation, we need to show that $p^{Nat.log p N}$ divides the lcm but $p^{Nat.log p N + 1}$ does not.
  have h_div : p ^ (Nat.log p N) ∣ Finset.lcm (Finset.Icc 1 N) id := by
    exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, Nat.pow_log_le_self p hN.ne' ⟩ )
  have h_not_div : ¬(p ^ (Nat.log p N + 1) ∣ Finset.lcm (Finset.Icc 1 N) id) := by
    rw [ Nat.Prime.pow_dvd_iff_le_factorization ] <;> norm_num [ hp ];
    have h_factorization : ∀ {S : Finset ℕ}, (∀ n ∈ S, n ≠ 0) → (Finset.lcm S id).factorization p ≤ Finset.sup S (fun n => n.factorization p) := by
      intros S hS_nonzero
      induction' S using Finset.induction with n S hnS ih;
      · simp +decide [ Finset.lcm ];
      · simp_all +decide [ Finset.lcm_insert ];
        by_cases h : S.lcm id = 0 <;> simp_all +decide [ GCDMonoid.lcm, Nat.factorization_lcm ];
        exact Classical.or_iff_not_imp_left.2 fun h => by linarith;
    refine le_trans ( h_factorization fun n hn => by linarith [ Finset.mem_Icc.mp hn ] ) ?_;
    simp +zetaDelta at *;
    exact fun n hn₁ hn₂ => Nat.le_log_of_pow_le hp.one_lt <| Nat.le_trans ( Nat.le_of_dvd hn₁ <| Nat.ordProj_dvd _ _ ) hn₂;
  haveI := Fact.mk hp; rw [ ← Nat.factorization_def ];
  · exact le_antisymm ( Nat.le_of_not_lt fun h => h_not_div <| dvd_trans ( pow_dvd_pow _ h ) <| Nat.ordProj_dvd _ _ ) ( Nat.le_of_not_lt fun h => absurd ( dvd_trans ( pow_dvd_pow _ h ) h_div ) <| Nat.pow_succ_factorization_not_dvd ( Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) hp );
  · exact hp

/-! ## log(lcm(1..N)) as a sum over primes

We decompose the real logarithm of lcm(1..N) using the fundamental theorem
of arithmetic: every positive natural is the product of its prime-power factors,
so log n = Σ_p factorization(n)(p) · log p.
Combined with `padic_val_lcm_range`, we get the target identity.
-/

/-
lcm(1..N) is nonzero for N ≥ 1.
-/
lemma lcm_Icc_ne_zero (N : ℕ) (hN : 0 < N) :
    (Finset.lcm (Finset.Icc 1 N) id : ℕ) ≠ 0 := by
      exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;

/-
The prime factors of lcm(1..N) are exactly the primes in [2, N].
-/
lemma primeFactors_lcm_Icc (N : ℕ) (hN : 0 < N) :
    (Finset.lcm (Finset.Icc 1 N) id : ℕ).primeFactors =
    Finset.filter Nat.Prime (Finset.Icc 2 N) := by
      ext p; constructor;
      · simp +zetaDelta at *;
        exact fun hp hp' => ⟨ ⟨ hp.two_le, hp.dvd_factorial.mp <| dvd_trans hp' <| Finset.lcm_dvd fun x hx => Nat.dvd_factorial ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ⟩, hp ⟩;
      · simp +zetaDelta at *;
        exact fun _ _ hp => ⟨ hp, Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ⟩

/-
For any positive natural, log n = Σ_{p ∈ primeFactors n} factorization(n)(p) · log p.
-/
lemma Real.log_natCast_eq_sum_factorization (n : ℕ) (hn : n ≠ 0) :
    Real.log (n : ℝ) =
    ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
      -- By definition of prime factorization, we can write n as a product of prime powers.
      have h_factorization : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
        exact Eq.symm ( Nat.factorization_prod_pow_eq_self hn );
      conv_lhs => rw [ h_factorization ];
      rw [ Nat.cast_prod, Real.log_prod ] <;> norm_cast <;> norm_num;
      exact fun p pp _ _ hp => absurd hp pp.ne_zero

theorem log_lcm_range_eq_sum (N : ℕ) (hN : 0 < N) :
    Real.log ((Finset.lcm (Finset.Icc 1 N) id : ℕ) : ℝ) =
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N),
      (Nat.log p N : ℝ) * Real.log p := by
        convert Real.log_natCast_eq_sum_factorization _ _ using 1;
        · refine' Finset.sum_bij ( fun p hp => p ) _ _ _ _ <;> simp_all +decide [ Finset.ext_iff ];
          · exact fun p hp₁ hp₂ hp₃ => Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, hp₂ ⟩ );
          · exact fun p pp dp => ⟨ pp.two_le, pp.dvd_factorial.mp <| dvd_trans dp <| Finset.lcm_dvd fun x hx => Nat.dvd_factorial ( Finset.mem_Icc.mp hx |>.1 ) <| Finset.mem_Icc.mp hx |>.2 ⟩;
          · intro p hp₁ hp₂ hp₃; rw [ Nat.factorization_def ] ;
            · exact Or.inl ( Eq.symm ( padic_val_lcm_range N p hp₃ hN ) );
            · assumption;
        · exact lcm_Icc_ne_zero N hN

/-! ## Von Mangoldt regrouping

We show that ∑_{n=2}^{N} Λ(n) = ∑_{p prime ≤ N} (Nat.log p N) · log p.
The key insight: every n with Λ(n) ≠ 0 is a prime power p^k (k ≥ 1),
and Λ(p^k) = log p. For each prime p ≤ N, the powers p^1, …, p^{Nat.log p N}
lie in [2, N], each contributing log p.
-/

open ArithmeticFunction in
theorem sum_vonMangoldt_eq_sum_primes (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 2 N, vonMangoldt n) =
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N),
      (Nat.log p N : ℝ) * Real.log p := by
  -- By definition of von Mangoldt function, we know that Λ(n) = log p if n is a prime power p^k, and 0 otherwise.
  have h_von_mangoldt : ∀ n ∈ Finset.Icc 2 N, Λ n = if IsPrimePow n then Real.log (n.minFac) else 0 := by
    intro n hn; split_ifs <;> simp_all +decide [ ArithmeticFunction.vonMangoldt ] ;
  -- We'll use the fact that if the von Mangoldt function is non-zero, then $n$ must be a prime power.
  have h_prime_powers : Finset.filter IsPrimePow (Finset.Icc 2 N) = Finset.biUnion (Finset.filter Nat.Prime (Finset.Icc 2 N)) (fun p => Finset.image (fun k => p^k) (Finset.Icc 1 (Nat.log p N))) := by
    ext;
    simp +zetaDelta at *;
    constructor;
    · rintro ⟨ ⟨ h₁, h₂ ⟩, h₃ ⟩;
      obtain ⟨ p, k, hp, hk, rfl ⟩ := h₃;
      exact ⟨ p, ⟨ ⟨ hp.nat_prime.two_le, by linarith [ Nat.le_self_pow hk.ne' p ] ⟩, hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt h₂ ⟩, rfl ⟩;
    · rintro ⟨ p, ⟨ ⟨ hp₁, hp₂ ⟩, hp₃ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
      exact ⟨ ⟨ le_trans hp₁ ( Nat.le_self_pow ( by linarith ) _ ), Nat.pow_le_of_le_log ( by linarith ) hk₂ ⟩, hp₃.isPrimePow.pow ( by linarith ) ⟩;
  -- By definition of von Mangoldt function, we know that Λ(n) = log p if n is a prime power p^k, and 0 otherwise. Therefore, we can rewrite the sum.
  have h_sum_rewrite : ∑ n ∈ Finset.Icc 2 N, Λ n = ∑ n ∈ Finset.filter IsPrimePow (Finset.Icc 2 N), Real.log (n.minFac) := by
    rw [ Finset.sum_filter, Finset.sum_congr rfl h_von_mangoldt ];
  rw [ h_sum_rewrite, h_prime_powers, Finset.sum_biUnion ];
  · refine' Finset.sum_congr rfl fun p hp => _;
    rw [ Finset.sum_image ] <;> norm_num;
    · rw [ Finset.sum_congr rfl fun x hx => by rw [ Nat.pow_minFac ] ; aesop ] ; aesop;
    · exact fun a ha b hb hab => Nat.pow_right_injective ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) hab;
  · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ] ;
    rintro a x hx₁ hx₂ rfl y hy₁ hy₂; intro H; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( H.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;

/-! ## Closing theorem: exp(ψ(N)) = lcm(1..N)

Chaining together:
- theorem_3_psi_eq_chebyshev: ∑ Λ = Chebyshev.psi N
- sum_vonMangoldt_eq_sum_primes: ∑ Λ = ∑_p (Nat.log p N) · log p
- log_lcm_range_eq_sum: log(lcm) = ∑_p (Nat.log p N) · log p
- Real.exp_log on lcm_Icc_ne_zero
-/

theorem exp_chebyshevPsi_eq_lcm (N : ℕ) (hN : 0 < N) :
    Real.exp (Chebyshev.psi (N : ℝ)) =
    ((Finset.lcm (Finset.Icc 1 N) id : ℕ) : ℝ) := by
  unfold Chebyshev.psi;
  convert Real.exp_log ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( lcm_Icc_ne_zero N hN ) ) ) using 1;
  convert congr_arg Real.exp ( sum_vonMangoldt_eq_sum_primes N hN ) using 1;
  · rw [ show ( Ioc 0 ⌊ ( N : ℝ ) ⌋₊ : Finset ℕ ) = Finset.Icc 1 N from ?_ ];
    · rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; aesop;
    · norm_num [ Nat.floor_natCast ];
      rfl;
  · exact congr_arg Real.exp ( log_lcm_range_eq_sum N hN )