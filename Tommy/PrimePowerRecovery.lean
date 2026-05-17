import Mathlib
import Tommy.Substrate

open Nat

/-- Bridges D to the prime base for prime-power inputs, zero otherwise.
    For n = p^k (prime power), returns p. Otherwise returns 0. -/
noncomputable def primePowerBase (n : ℕ) : ℕ :=
  if IsPrimePow n then n / Nat.gcd n (Nat.totient n) else 0

/-
Helper: gcd(p^k, φ(p^k)) = p^(k-1) for prime p and k ≥ 1.
-/
theorem gcd_prime_pow_totient (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    Nat.gcd (p ^ k) (Nat.totient (p ^ k)) = p ^ (k - 1) := by
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.totient_prime_pow ];
      · rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.totient_prime ];
      · norm_num [ show p ^ ( k + 1 + 1 ) = p ^ ( k + 1 ) * p by ring, Nat.gcd_mul_left ];
        cases p <;> simp_all +decide

theorem primePowerBase_eq_prime
    {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    primePowerBase (p ^ k) = p := by
      unfold primePowerBase;
      rw [ if_pos, gcd_prime_pow_totient p hp k hk, Nat.pow_div ] <;> norm_num [ hp.pos, hk ];
      · rw [ Nat.sub_sub_self hk, pow_one ];
      · exact hp.isPrimePow.pow hk.ne'

theorem primePowerBase_eq_zero_of_not
    {n : ℕ} (h : ¬ IsPrimePow n) :
    primePowerBase n = 0 := by
  unfold primePowerBase
  rw [if_neg h]

/-- Natural number projection from D: the natural floor of the norm squared x² + y². -/
noncomputable def D.toNat (d : D) : ℕ :=
  ⌊d.x ^ 2 + d.y ^ 2⌋₊

/-- Compose the prime-power base recovery with the D → ℕ norm-squared projection. -/
noncomputable def recovery_map (d : D) : ℕ :=
  primePowerBase (D.toNat d)