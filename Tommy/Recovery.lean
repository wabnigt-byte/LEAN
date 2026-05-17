import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev

open Nat ArithmeticFunction

/-- g(n) = n - φ(n) -/
def g (n : ℕ) : ℕ := n - totient n

/-- Indicator for prime powers: 1 if n > 1 and g(n) | n, else 0 -/
def chi (n : ℕ) : ℕ := if n > 1 ∧ g n ∣ n then 1 else 0

/-- Indicator for primes: 1 if n > 1 and g(n) = 1, else 0 -/
def chi1 (n : ℕ) : ℕ := if n > 1 ∧ g n = 1 then 1 else 0

lemma prime_dvd_prod_mem (S : Finset ℕ) (q : ℕ) (hq : q.Prime) (h_dvd : q ∣ ∏ p ∈ S, p)
  (h_primes : ∀ p ∈ S, p.Prime) : q ∈ S := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty] at h_dvd
    have h_not_dvd : ¬ (q ∣ 1) := Nat.Prime.not_dvd_one hq
    contradiction
  | insert p S hp_not_mem ih =>
    rw [Finset.prod_insert hp_not_mem] at h_dvd
    have h_dvd_or : q ∣ p ∨ q ∣ ∏ p ∈ S, p := (Nat.Prime.dvd_mul hq).mp h_dvd
    rcases h_dvd_or with h_dvd_p | h_dvd_prod
    · have p_prime : p.Prime := h_primes p (Finset.mem_insert_self p S)
      have h_eq : q = p := (Nat.prime_dvd_prime_iff_eq hq p_prime).mp h_dvd_p
      rw [h_eq]
      exact Finset.mem_insert_self p S
    · have h_mem : q ∈ S := by
        apply ih h_dvd_prod
        intro p' hp'
        exact h_primes p' (Finset.mem_insert_of_mem hp')
      exact Finset.mem_insert_of_mem h_mem

/-- Hard direction of Lemma 2. -/
theorem isPrimePow_of_sub_totient_dvd (n : ℕ) (hn : n > 1) (h : g n ∣ n) : IsPrimePow n := by
  -- Write n via its prime factorisation as `n.factorization` (a Finsupp ℕ →₀ ℕ).
  have n_eq_prod : n = ∏ p ∈ n.factorization.support, p ^ (n.factorization p) := by
    have hn_ne_zero : n ≠ 0 := by omega
    have := Nat.factorization_prod_pow_eq_self hn_ne_zero
    rw [Finsupp.prod] at this
    exact this.symm

  -- Let S be the prime divisors of n: `S := n.factorization.support`.
  let S := n.factorization.support

  -- Then `g n = (∏ p ∈ S, p ^ (n.factorization p − 1)) * Δ` where Δ := ∏ p ∈ S, p − ∏ p ∈ S, (p − 1).
  have g_eq_prod_delta : g n = (∏ p ∈ S, p ^ (n.factorization p - 1)) * (∏ p ∈ S, p - ∏ p ∈ S, (p - 1)) := by
    unfold g
    have hn_ne_zero : n ≠ 0 := by omega
    have totient_eq : totient n = ∏ p ∈ S, p ^ (n.factorization p - 1) * (p - 1) := by
      exact totient_eq_prod_factorization hn_ne_zero
    rw [totient_eq]
    nth_rw 1 [n_eq_prod]
    have h_prod_mul : (∏ p ∈ S, p ^ (n.factorization p - 1) * (p - 1)) = (∏ p ∈ S, p ^ (n.factorization p - 1)) * (∏ p ∈ S, (p - 1)) := by
      exact Finset.prod_mul_distrib
    rw [h_prod_mul]
    have h_n_prod_mul : (∏ p ∈ S, p ^ (n.factorization p)) = (∏ p ∈ S, p ^ (n.factorization p - 1) * p) := by
      apply Finset.prod_congr rfl
      intro p hp
      have h_pow : p ^ (n.factorization p) = p ^ (n.factorization p - 1 + 1) := by
        have h_pos : n.factorization p > 0 := by
          exact Finsupp.mem_support_iff.mp hp |> Nat.pos_of_ne_zero
        congr 1
        omega
      rw [h_pow, pow_add, pow_one]
    rw [h_n_prod_mul]
    have h_n_prod_mul2 : (∏ p ∈ S, p ^ (n.factorization p - 1) * p) = (∏ p ∈ S, p ^ (n.factorization p - 1)) * (∏ p ∈ S, p) := by
      exact Finset.prod_mul_distrib
    rw [h_n_prod_mul2]
    rw [← Nat.mul_sub_left_distrib]

  -- Phase A
  have prod_ne_zero : (∏ p ∈ S, p ^ (n.factorization p - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have p_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have p_ne_zero : p ≠ 0 := p_prime.ne_zero
    exact pow_ne_zero _ p_ne_zero

  have delta_dvd_radical : (∏ p ∈ S, p) - (∏ p ∈ S, (p - 1)) ∣ ∏ p ∈ S, p := by
    have h_dvd : (∏ p ∈ S, p ^ (n.factorization p - 1)) * ((∏ p ∈ S, p) - (∏ p ∈ S, (p - 1))) ∣ (∏ p ∈ S, p ^ (n.factorization p - 1)) * (∏ p ∈ S, p) := by
      have h_n_prod_mul : (∏ p ∈ S, p ^ (n.factorization p)) = (∏ p ∈ S, p ^ (n.factorization p - 1)) * (∏ p ∈ S, p) := by
        have h1 : (∏ p ∈ S, p ^ (n.factorization p)) = (∏ p ∈ S, p ^ (n.factorization p - 1) * p) := by
          apply Finset.prod_congr rfl
          intro p hp
          have h_pow : p ^ (n.factorization p) = p ^ (n.factorization p - 1 + 1) := by
            have h_pos : n.factorization p > 0 := by
              exact Finsupp.mem_support_iff.mp hp |> Nat.pos_of_ne_zero
            congr 1
            omega
          rw [h_pow, pow_add, pow_one]
        rw [h1]
        exact Finset.prod_mul_distrib
      rw [← g_eq_prod_delta, ← h_n_prod_mul, ← n_eq_prod]
      exact h
    have prod_pos : 0 < (∏ p ∈ S, p ^ (n.factorization p - 1)) := Nat.pos_of_ne_zero prod_ne_zero
    exact Nat.dvd_of_mul_dvd_mul_left prod_pos h_dvd

  -- Phase B
  rcases eq_or_ne S.card 1 with h_card | h_card
  · -- S.card = 1
    have S_singleton : ∃ p, S = {p} := Finset.card_eq_one.mp h_card
    rcases S_singleton with ⟨p, hp_eq⟩
    have p_prime : p.Prime := by
      have h_mem : p ∈ S := by rw [hp_eq]; exact Finset.mem_singleton_self p
      exact Nat.prime_of_mem_primeFactors h_mem
    have n_eq_pk : n = p ^ (n.factorization p) := by
      have h_n_eq : n = ∏ p ∈ S, p ^ (n.factorization p) := n_eq_prod
      rw [hp_eq] at h_n_eq
      rw [Finset.prod_singleton] at h_n_eq
      exact h_n_eq
    have k_pos : n.factorization p > 0 := by
      have h_mem : p ∈ S := by rw [hp_eq]; exact Finset.mem_singleton_self p
      exact Finsupp.mem_support_iff.mp h_mem |> Nat.pos_of_ne_zero
    use p, n.factorization p
    exact ⟨Nat.prime_iff.mp p_prime, k_pos, n_eq_pk.symm⟩
  · -- S.card >= 2
    -- For every prime p in S, p ≥ 2, so p − 1 ≥ 1.
    have p_minus_one_pos : ∀ p ∈ S, p - 1 ≥ 1 := by
      intro p hp
      have p_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have p_ge_2 : p ≥ 2 := p_prime.two_le
      omega

    -- Hence ∏ p ∈ S, (p − 1) ≥ 1.
    have prod_p_minus_one_pos : ∏ p ∈ S, (p - 1) ≥ 1 := by
      apply Finset.one_le_prod'
      intro p hp
      exact p_minus_one_pos p hp

    -- Therefore Δ = ∏p − ∏(p−1) ≤ ∏p − 1.
    have delta_le_radical_minus_one : (∏ p ∈ S, p) - (∏ p ∈ S, (p - 1)) ≤ (∏ p ∈ S, p) - 1 := by
      exact Nat.sub_le_sub_left prod_p_minus_one_pos (∏ p ∈ S, p)

    -- And ∏p − 1 < ∏p (since ∏p ≥ 1).
    have radical_minus_one_lt_radical : (∏ p ∈ S, p) - 1 < ∏ p ∈ S, p := by
      have radical_pos : ∏ p ∈ S, p ≥ 1 := by
        apply Finset.one_le_prod'
        intro p hp
        have p_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have p_ge_2 : p ≥ 2 := p_prime.two_le
        omega
      omega

    have delta_lt_radical : (∏ p ∈ S, p) - (∏ p ∈ S, (p - 1)) < ∏ p ∈ S, p := by
      omega

    -- Let p₁ be the smallest prime in S.
    have S_nonempty : S.Nonempty := by
      have h_card_pos : S.card > 0 := by
        have h_card_ge_2 : S.card ≥ 2 := by
          have h_card_ne_0 : S.card ≠ 0 := by
            intro h_zero
            have h_empty : S = ∅ := Finset.card_eq_zero.mp h_zero
            have h_n_eq_1 : n = 1 := by
              have h_n_eq : n = ∏ p ∈ S, p ^ (n.factorization p) := n_eq_prod
              rw [h_empty] at h_n_eq
              rw [Finset.prod_empty] at h_n_eq
              exact h_n_eq
            omega
          omega
        omega
      exact Finset.card_pos.mp h_card_pos
    let p1 := S.min' S_nonempty

    -- p₁ is a member of S.
    have p1_mem : p1 ∈ S := Finset.min'_mem S S_nonempty

    -- S \ {p₁} is non-empty because S.card ≥ 2.
    have S_erase_nonempty : (S.erase p1).Nonempty := by
      have h_card_erase : (S.erase p1).card = S.card - 1 := Finset.card_erase_of_mem p1_mem
      have h_card_erase_pos : (S.erase p1).card > 0 := by
        have h_card_ge_2 : S.card ≥ 2 := by
          have h_card_ne_0 : S.card ≠ 0 := by
            intro h_zero
            have h_empty : S = ∅ := Finset.card_eq_zero.mp h_zero
            have h_n_eq_1 : n = 1 := by
              have h_n_eq : n = ∏ p ∈ S, p ^ (n.factorization p) := n_eq_prod
              rw [h_empty] at h_n_eq
              rw [Finset.prod_empty] at h_n_eq
              exact h_n_eq
            omega
          omega
        omega
      exact Finset.card_pos.mp h_card_erase_pos

    -- ∏ p ∈ S, p factors as p₁ * ∏ p ∈ S \ {p₁}, p.
    have radical_eq_p1_mul_erase : ∏ p ∈ S, p = p1 * ∏ p ∈ S.erase p1, p := by
      exact Finset.mul_prod_erase S _ p1_mem |>.symm

    -- ∏ p ∈ S, (p − 1) factors as (p₁ − 1) * ∏ p ∈ S \ {p₁}, (p − 1).
    have prod_minus_one_eq_p1_minus_one_mul_erase : ∏ p ∈ S, (p - 1) = (p1 - 1) * ∏ p ∈ S.erase p1, (p - 1) := by
      exact Finset.mul_prod_erase S _ p1_mem |>.symm

    -- For each p ∈ S \ {p₁}, p − 1 ≥ 1 (since p prime, p ≥ 2) and p > p − 1.
    have p_gt_p_minus_one : ∀ p ∈ S.erase p1, p > p - 1 ∧ p - 1 ≥ 1 := by
      intro p hp
      have hp_mem : p ∈ S := Finset.mem_erase.mp hp |>.right
      have p_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have p_ge_2 : p ≥ 2 := p_prime.two_le
      exact ⟨by omega, by omega⟩

    -- Therefore ∏ p ∈ S \ {p₁}, p > ∏ p ∈ S \ {p₁}, (p − 1), strictly.
    have prod_erase_gt_prod_erase_minus_one : ∏ p ∈ S.erase p1, p > ∏ p ∈ S.erase p1, (p - 1) := by
      apply Finset.prod_lt_prod_of_nonempty
      · intro p hp
        exact (p_gt_p_minus_one p hp).right
      · intro p hp
        exact (p_gt_p_minus_one p hp).left
      · exact S_erase_nonempty

    -- Multiplying both sides by p₁ · (p₁ − 1) > 0 preserves the strict inequality.
    have p1_minus_one_pos : p1 - 1 > 0 := by
      have p1_prime : p1.Prime := Nat.prime_of_mem_primeFactors p1_mem
      have p1_ge_2 : p1 ≥ 2 := p1_prime.two_le
      omega

    have p1_pos : p1 > 0 := by
      have p1_prime : p1.Prime := Nat.prime_of_mem_primeFactors p1_mem
      exact p1_prime.pos

    have delta_mul_p1_gt_radical : ((∏ p ∈ S, p) - (∏ p ∈ S, (p - 1))) * p1 > ∏ p ∈ S, p := by
      have h_mul_lt : (∏ p ∈ S.erase p1, (p - 1)) * (p1 * (p1 - 1)) < (∏ p ∈ S.erase p1, p) * (p1 * (p1 - 1)) := by
        have h_pos : p1 * (p1 - 1) > 0 := Nat.mul_pos p1_pos p1_minus_one_pos
        exact Nat.mul_lt_mul_of_pos_right prod_erase_gt_prod_erase_minus_one h_pos
      have h_rw1 : (∏ p ∈ S.erase p1, (p - 1)) * (p1 * (p1 - 1)) = (∏ p ∈ S, (p - 1)) * p1 := by
        calc (∏ p ∈ S.erase p1, (p - 1)) * (p1 * (p1 - 1))
          _ = (p1 - 1) * (∏ p ∈ S.erase p1, (p - 1)) * p1 := by ring_nf
          _ = (∏ p ∈ S, (p - 1)) * p1 := by rw [← prod_minus_one_eq_p1_minus_one_mul_erase]
      have h_rw2 : (∏ p ∈ S.erase p1, p) * (p1 * (p1 - 1)) = (∏ p ∈ S, p) * (p1 - 1) := by
        calc (∏ p ∈ S.erase p1, p) * (p1 * (p1 - 1))
          _ = p1 * (∏ p ∈ S.erase p1, p) * (p1 - 1) := by ring_nf
          _ = (∏ p ∈ S, p) * (p1 - 1) := by rw [← radical_eq_p1_mul_erase]
      rw [h_rw1, h_rw2] at h_mul_lt
      have h_rw3 : ((∏ p ∈ S, p) - (∏ p ∈ S, (p - 1))) * p1 = (∏ p ∈ S, p) * p1 - (∏ p ∈ S, (p - 1)) * p1 := by
        exact Nat.mul_sub_right_distrib (∏ p ∈ S, p) (∏ p ∈ S, (p - 1)) p1
      rw [h_rw3]
      have h_rw4 : (∏ p ∈ S, p) * (p1 - 1) = (∏ p ∈ S, p) * p1 - (∏ p ∈ S, p) := by
        exact Nat.mul_sub_left_distrib (∏ p ∈ S, p) p1 1 |>.trans (by ring_nf)
      rw [h_rw4] at h_mul_lt
      omega

    -- Δ is positive (it divides the positive radical).
    have delta_pos : (∏ p ∈ S, p) - (∏ p ∈ S, (p - 1)) > 0 := by
      have radical_pos : ∏ p ∈ S, p > 0 := by
        apply Finset.prod_pos
        intro p hp
        have p_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
        exact p_prime.pos
      exact Nat.pos_of_dvd_of_pos delta_dvd_radical radical_pos

    -- Write ∏ p ∈ S, p = Δ · k for some k.
    have radical_eq_delta_mul_k : ∃ k, ∏ p ∈ S, p = ((∏ p ∈ S, p) - (∏ p ∈ S, (p - 1))) * k := by
      exact exists_eq_mul_right_of_dvd delta_dvd_radical
    rcases radical_eq_delta_mul_k with ⟨k, hk_eq⟩

    -- k is positive (radical is positive, Δ is positive).
    have k_pos : k > 0 := by
      have radical_pos : ∏ p ∈ S, p > 0 := by
        apply Finset.prod_pos
        intro p hp
        have p_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
        exact p_prime.pos
      have h_mul_pos : k * ((∏ p ∈ S, p) - (∏ p ∈ S, (p - 1))) > 0 := by
        rw [mul_comm, ← hk_eq]
        exact radical_pos
      exact Nat.pos_of_mul_pos_right h_mul_pos

    -- k ≥ 2 (because Δ · k = radical and Δ < radical).
    have k_ge_two : k ≥ 2 := by
      have h_not_one : k ≠ 1 := by
        intro h_one
        rw [h_one, mul_one] at hk_eq
        have h_lt : ((∏ p ∈ S, p) - (∏ p ∈ S, (p - 1))) < ∏ p ∈ S, p := delta_lt_radical
        rw [← hk_eq] at h_lt
        omega
      omega

    -- p₁ > k (cancel positive Δ in Δ · p₁ > Δ · k).
    have p1_gt_k : p1 > k := by
      have h_mul_lt : ((∏ p ∈ S, p) - (∏ p ∈ S, (p - 1))) * k < ((∏ p ∈ S, p) - (∏ p ∈ S, (p - 1))) * p1 := by
        rw [← hk_eq]
        exact delta_mul_p1_gt_radical
      exact Nat.lt_of_mul_lt_mul_left h_mul_lt

    -- k ≥ 2 has a prime divisor q.
    have q_exists : ∃ q, q.Prime ∧ q ∣ k := by
      have h_not_one : k ≠ 1 := by omega
      exact Nat.exists_prime_and_dvd h_not_one
    rcases q_exists with ⟨q, q_prime, q_dvd_k⟩

    -- q divides the radical (transitively, q ∣ k ∣ radical).
    have q_dvd_radical : q ∣ ∏ p ∈ S, p := by
      have k_dvd_radical : k ∣ ∏ p ∈ S, p := by
        rw [hk_eq]
        exact dvd_mul_left k ((∏ p ∈ S, p) - (∏ p ∈ S, (p - 1)))
      exact dvd_trans q_dvd_k k_dvd_radical

    -- q ∈ S (a prime divisor of the radical is in S).
    have q_in_S : q ∈ S := by
      apply prime_dvd_prod_mem S q q_prime q_dvd_radical
      intro p hp
      exact Nat.prime_of_mem_primeFactors hp

    -- p₁ ≤ q (p₁ is the min of S).
    have p1_le_q : p1 ≤ q := Finset.min'_le S q q_in_S

    -- q ≤ k (q ∣ k, k > 0).
    have q_le_k : q ≤ k := Nat.le_of_dvd k_pos q_dvd_k

    -- Therefore p₁ ≤ q ≤ k < p₁, contradiction.
    omega


theorem lemma_2 (n : ℕ) (hn : n > 1) : g n ∣ n ↔ IsPrimePow n := by
  constructor
  · intro h
    exact isPrimePow_of_sub_totient_dvd n hn h
  · intro h
    -- Unpack: n = p^k with p prime and k ≥ 1.
    rcases h with ⟨p, k, hp, hk, rfl⟩
    have hp_nat : p.Prime := Nat.prime_iff.mpr hp
    -- The totient of p^k is p^(k-1) * (p-1).
    have totient_pk : totient (p^k) = p^(k-1) * (p-1) := totient_prime_pow hp_nat hk
    -- So g(p^k) simplifies to p^(k-1).
    have g_pk : g (p^k) = p^(k-1) := by
      unfold g
      rw [totient_pk]
      have p_pow_eq : p^k = p^(k-1) * p := by
        have h_pow : p^k = p^(k-1 + 1) := by
          congr 1
          omega
        rw [h_pow, pow_add, pow_one]
      rw [p_pow_eq]
      rw [← Nat.mul_sub_left_distrib]
      have p_sub : p - (p - 1) = 1 := by
        have p_pos : p > 0 := hp_nat.pos
        omega
      rw [p_sub, mul_one]
    -- And p^(k-1) divides p^k.
    have div_pk : p^(k-1) ∣ p^k := pow_dvd_pow p (by omega)
    rw [g_pk]
    exact div_pk


/-- Helper: g(p^(m+1)) = p^m for prime p. -/
private lemma g_prime_pow_succ (p m : ℕ) (hp : p.Prime) : g (p^(m+1)) = p^m := by
  unfold g
  have htot : φ (p^(m+1)) = p^m * (p-1) := by
    have h := @totient_prime_pow p hp (m+1) (Nat.succ_pos m)
    norm_num at h; exact h
  rw [htot, show p^(m+1) = p^m * p from by ring,
      ← Nat.mul_sub_left_distrib,
      show p - (p - 1) = 1 from by have := hp.two_le; omega,
      mul_one]

/-- Helper: chi1 n = if n.Prime then 1 else 0. -/
lemma chi1_eq_prime_indicator (n : ℕ) : chi1 n = if n.Prime then 1 else 0 := by
  simp only [chi1, g]
  by_cases hn : n.Prime
  · simp only [hn, ite_true]
    have h1 : n > 1 := hn.one_lt
    have htot : φ n = n - 1 := totient_prime hn
    simp [h1, show n - φ n = 1 from by omega]
  · simp only [hn, ite_false, ite_eq_right_iff]
    intro ⟨h1, hg⟩
    exact absurd ((Nat.totient_eq_iff_prime (by omega)).mp (by omega)) hn

/-- Helper: chi n = if IsPrimePow n then 1 else 0. -/
lemma chi_eq_isPrimePow_indicator (n : ℕ) : chi n = if IsPrimePow n then 1 else 0 := by
  simp only [chi]
  by_cases hpp : IsPrimePow n
  · -- Condition holds: n > 1 and g n ∣ n (from lemma_2).
    simp only [hpp, ite_true]
    rw [if_pos ⟨hpp.one_lt, (lemma_2 n hpp.one_lt).mpr hpp⟩]
  · -- Condition fails.
    simp only [hpp, ite_false, ite_eq_right_iff]
    intro ⟨hn_gt1, hg_dvd⟩
    exact absurd ((lemma_2 n hn_gt1).mp hg_dvd) hpp

/-- Helper: (↑(p^(m+1)) : ℝ) / (↑(g(p^(m+1))) : ℝ) = ↑p for prime p. -/
private lemma cast_pp_div_g (p m : ℕ) (hp : p.Prime) :
    ((p^(m+1) : ℕ) : ℝ) / ((g (p^(m+1))) : ℝ) = (p : ℝ) := by
  rw [g_prime_pow_succ p m hp]
  push_cast
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp; ring

/-- The prime-power counting function: number of prime powers n with 2 ≤ n ≤ N. -/
def primePowerCount (N : ℕ) : ℕ := ∑ n ∈ Finset.Icc 2 N, if IsPrimePow n then 1 else 0

/-- Theorem 3: Recovery formula for π.
    π(N) = #{primes p ≤ N} = ∑_{2 ≤ n ≤ N} χ₁(n), where χ₁ is the prime indicator. -/
theorem theorem_3_pi (N : ℕ) : primeCounting N = ∑ n ∈ Finset.Icc 2 N, chi1 n := by
  rw [show ∑ n ∈ Finset.Icc 2 N, chi1 n =
        ∑ n ∈ Finset.Icc 2 N, if n.Prime then 1 else 0 from
      Finset.sum_congr rfl (fun x _ => chi1_eq_prime_indicator x)]
  have h_pc : primeCounting N = ((Finset.range (N + 1)).filter Nat.Prime).card := by
    simp [primeCounting, primeCounting', Nat.count_eq_card_filter_range]
  rw [h_pc, ← Finset.card_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨hN, hp⟩; exact ⟨⟨hp.two_le, Nat.lt_succ_iff.mp hN⟩, hp⟩
  · rintro ⟨⟨_, hN⟩, hp⟩; exact ⟨Nat.lt_succ_of_le hN, hp⟩

/-- Theorem 3: Recovery formula for π*.
    π*(N) = #{prime powers p^k ≤ N, k ≥ 1} = ∑_{2 ≤ n ≤ N} χ(n),
    where χ is the prime-power indicator and primePowerCount is the finite-sum definition. -/
theorem theorem_3_pi_star (N : ℕ) : primePowerCount N = ∑ n ∈ Finset.Icc 2 N, chi n := by
  unfold primePowerCount
  exact Finset.sum_congr rfl (fun x _ => (chi_eq_isPrimePow_indicator x).symm)

/-- Theorem 3 — θ formula: θ(N) = ∑_{n≤N} χ₁(n) log n. -/
theorem theorem_3_theta (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, if n.Prime then (Real.log n : ℝ) else 0) =
    ∑ n ∈ Finset.Icc 2 N, (chi1 n : ℝ) * Real.log n := by
  apply Finset.sum_congr rfl
  intro x _
  rw [chi1_eq_prime_indicator x]
  split_ifs with hx <;> simp

/-- Rank 22 bridge: the project θ sum over Icc 2 N equals Mathlib's Chebyshev.theta N. -/
theorem theorem_3_theta_eq_chebyshev (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, if n.Prime then (Real.log n : ℝ) else 0) =
    Chebyshev.theta (N : ℝ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  -- RHS filter form: ∑ p ∈ Icc 0 N with p.Prime, log p  =  ∑ p ∈ Icc 0 N, if p.Prime then log p else 0
  rw [Finset.sum_filter]
  -- We show the two if-then-else sums (over Icc 0 N and Icc 2 N) are equal
  -- by showing elements 0 and 1 in Icc 0 N \ Icc 2 N are not prime
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · intro x hx hx2
    simp only [Finset.mem_Icc] at hx hx2
    have : x = 0 ∨ x = 1 := by omega
    rcases this with rfl | rfl <;> simp [Nat.not_prime_zero, Nat.not_prime_one]

/-- Theorem 3 — Λ formula (pointwise): Λ(n) = χ(n) · log(n / g(n)). -/
theorem theorem_3_lambda (n : ℕ) :
    (vonMangoldt n : ℝ) = (chi n : ℝ) * Real.log ((n : ℝ) / (g n : ℝ)) := by
  rw [chi_eq_isPrimePow_indicator n, vonMangoldt_apply]
  by_cases hpp : IsPrimePow n
  · simp only [hpp, ite_true, Nat.cast_one, one_mul]
    rw [isPrimePow_nat_iff] at hpp
    rcases hpp with ⟨p, k, hp_prime, hk_pos, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [hp_prime.pow_minFac (by omega : m + 1 ≠ 0), cast_pp_div_g p m hp_prime]
  · simp [hpp]

/-- Theorem 3 — ψ formula: ψ(N) = ∑_{n≤N} χ(n) · log(n / g(n)). -/
theorem theorem_3_psi (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, vonMangoldt n) =
    ∑ n ∈ Finset.Icc 2 N, (chi n : ℝ) * Real.log ((n : ℝ) / (g n : ℝ)) :=
  Finset.sum_congr rfl (fun x _ => theorem_3_lambda x)

/-- Rank 23 bridge: the project ψ sum over Icc 2 N equals Mathlib's Chebyshev.psi N. -/
theorem theorem_3_psi_eq_chebyshev (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, vonMangoldt n) = Chebyshev.psi (N : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_Ioc]
    exact ⟨by omega, hx.2⟩
  · intro x hx hx2
    simp only [Finset.mem_Ioc] at hx
    simp only [Finset.mem_Icc, not_and, not_le] at hx2
    have hx1 : x = 1 := by
      have h_lt2 : x < 2 := by
        by_contra h_not_lt2
        exact absurd hx.2 (Nat.not_le.mpr (hx2 (Nat.le_of_not_lt h_not_lt2)))
      omega
    subst hx1
    exact vonMangoldt_apply_one

/-! ## Concrete evaluations of g, chi -/

/-- g(p) = 1 for prime p. -/
theorem g_prime (p : ℕ) (hp : p.Prime) : g p = 1 := by
  unfold g
  rw [Nat.totient_prime hp]
  have := hp.two_le; omega

/-- g(p²) = p for prime p. -/
theorem g_prime_sq (p : ℕ) (hp : p.Prime) : g (p ^ 2) = p := by
  have h := g_prime_pow_succ p 1 hp
  norm_num at h; exact h

/-- chi(p) = 1 for prime p. -/
theorem chi_prime (p : ℕ) (hp : p.Prime) : chi p = 1 := by
  rw [chi_eq_isPrimePow_indicator]
  simp [hp.isPrimePow]

/-- chi(n) = 0 when n is not a prime power and n > 1. -/
theorem chi_not_prime_pow (n : ℕ) (_hn : n > 1) (h : ¬IsPrimePow n) : chi n = 0 := by
  rw [chi_eq_isPrimePow_indicator]
  simp [h]

/-- chi1(p) = 1 for prime p. -/
theorem chi1_prime (p : ℕ) (hp : p.Prime) : chi1 p = 1 := by
  rw [chi1_eq_prime_indicator]
  simp [hp]

/-- chi1(n) = 0 when n is not prime. -/
theorem chi1_not_prime (n : ℕ) (h : ¬n.Prime) : chi1 n = 0 := by
  rw [chi1_eq_prime_indicator]
  simp [h]

/-- Theorem 3 — Ω formula: Ω(p^k) = log(p^k) / log(p^k / g(p^k)). -/
theorem theorem_3_omega (p k : ℕ) (hp : p.Prime) (hk : k > 0) :
    (cardFactors (p^k) : ℝ) =
    Real.log ((p^k : ℕ) : ℝ) / Real.log (((p^k : ℕ) : ℝ) / ((g (p^k)) : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hcard : cardFactors (p^(m+1)) = m + 1 := cardFactors_apply_prime_pow hp
  have hg_cast : ((g (p^(m+1))) : ℝ) = (p : ℝ)^m := by
    rw [g_prime_pow_succ p m hp]; push_cast; ring
  have hlog_pow : Real.log ((p^(m+1) : ℕ) : ℝ) = (m + 1 : ℝ) * Real.log p := by
    push_cast; rw [Real.log_pow]; push_cast; ring
  have hdiv : ((p^(m+1) : ℕ) : ℝ) / (p : ℝ)^m = (p : ℝ) := by
    push_cast; have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp; ring
  have hlog_pos : Real.log (p : ℝ) > 0 := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [hcard, hg_cast, hdiv, hlog_pow, mul_div_cancel_right₀ _ hlog_pos.ne']
  push_cast; ring

/-- Rank 24 bridge: the project's primePowerCount N equals Mathlib's Nat.count IsPrimePow (N+1).
    This mirrors `primeCounting' = Nat.count Nat.Prime` for primes. -/
theorem theorem_3_pi_star_eq_count (N : ℕ) :
    primePowerCount N = Nat.count IsPrimePow (N + 1) := by
  rw [ primePowerCount, Nat.count_eq_card_filter_range ];
  rw [ Finset.range_eq_Ico, Finset.Ico_eq_cons_Ioo, Finset.filter_cons ] <;> norm_num;
  congr 1 with ( _ | _ | x ) <;> simp +arith +decide