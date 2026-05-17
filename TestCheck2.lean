import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.PrimeCounting

open Nat ArithmeticFunction

-- primeCounting' N = count Nat.Prime N = #{p : p prime, p < N}
-- primeCounting N = #{p : p prime, p ≤ N}
-- These count PRIMES, not prime powers.

-- The task says theorem_3_pi_star relates primeCounting' to chi (prime powers).
-- The hypothesis h_primeCounting' is false as stated.

-- What if the intent was: primeCounting' counts prime powers up to N?
-- There's no standard Mathlib function for that.
-- We'd need to define it or use a different formulation.

-- Perhaps the intended meaning is:
-- "the prime power counting function" = ∑ n ∈ Icc 2 N, if IsPrimePow n then 1 else 0
-- and theorem_3_pi_star should say: this equals ∑ n ∈ Icc 2 N, chi n
-- without involving Nat.primeCounting' at all.

-- Since the old theorem kept a FALSE assumption h_primeCounting', the "fix" is either:
-- 1. Replace the theorem with a tautology about chi (trivially true)
-- 2. Change the LHS to use a finite sum definition of prime power counting

-- The task says "using the suggested finite-sum definitions/proofs"
-- So let's define prime_power_count as the finite sum and state theorem_3_pi_star about that.

def prime_power_count (N : ℕ) : ℕ := ∑ n ∈ Finset.Icc 2 N, if IsPrimePow n then 1 else 0

def g (n : ℕ) : ℕ := n - totient n
def chi (n : ℕ) : ℕ := if n > 1 ∧ g n ∣ n then 1 else 0

-- Reconstruct chi_eq_isPrimePow_indicator and lemma_2
lemma isPrimePow_of_sub_totient_dvd (n : ℕ) (hn : n > 1) (h : g n ∣ n) : IsPrimePow n := by
  sorry

theorem lemma_2 (n : ℕ) (hn : n > 1) : g n ∣ n ↔ IsPrimePow n := by
  constructor
  · intro h; exact isPrimePow_of_sub_totient_dvd n hn h
  · sorry

lemma chi_eq_isPrimePow_indicator (n : ℕ) : chi n = if IsPrimePow n then 1 else 0 := by
  simp only [chi]
  by_cases hpp : IsPrimePow n
  · simp only [hpp, ite_true]
    rw [if_pos ⟨hpp.one_lt, (lemma_2 n hpp.one_lt).mpr hpp⟩]
  · simp only [hpp, ite_false, ite_eq_right_iff]
    intro ⟨hn_gt1, hg_dvd⟩
    exact absurd ((lemma_2 n hn_gt1).mp hg_dvd) hpp

-- theorem_3_pi_star: remove h_primeCounting' assumption, use prime_power_count
theorem theorem_3_pi_star_v2 (N : ℕ) :
    prime_power_count N = ∑ n ∈ Finset.Icc 2 N, chi n := by
  unfold prime_power_count
  exact Finset.sum_congr rfl (fun x _ => (chi_eq_isPrimePow_indicator x).symm)

