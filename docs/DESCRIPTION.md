# Project Description

## Lean Project from Aristotle

This project implements a formal verification of the Thomae Function on RxR and in 3D using the Lean proof assistant.

### Overview
- **Total Declarations**: 177 (106 theorems + 71 lemmas)
- **Lean Files**: 25
- **Main Library**: `Tommy/` with 152 unique declarations

### Project Goals
I am applying for a PhD in innovation research (e.g. use of A.I.). The research question: Could someone with no formal training in LEAN use LLMs to get a formal proof?

### Key Features
Exhaustive List of All Theorems and Lemmas in the Repository


## Tommy/Closure.lean (21 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `phi_idempotent_on_S1` | `(v : ℝ × ℝ) (hv : v ∈ S1) : phi v = v` |
| 2 | theorem | `phi_mem_S1` | `(v : ℝ × ℝ) (hv : v ≠ (0, 0)) : phi v ∈ S1` |
| 3 | lemma | `S1_isClosed` | `: IsClosed S1` |
| 4 | lemma | `primitive_dirs_subset_S1` | `: primitive_dirs ⊆ S1` |
| 5 | lemma | `phiRight_sqrt_pos` | `(t : ℝ) : 0 < Real.sqrt (1 + t ^ 2)` |
| 6 | lemma | `phiRight_cont` | `: Continuous phiRight` |
| 7 | lemma | `phi_den_num_eq_phiRight` | `(q : ℚ) : phi ((q.den : ℝ), (q.num : ℝ)) = phiRight (q : ℝ)` |
| 8 | lemma | `phiRight_rat_mem_primitive_dirs` | `(q : ℚ) : phiRight (q : ℝ) ∈ primitive_dirs` |
| 9 | lemma | `phiRight_in_closure` | `(t : ℝ) : phiRight t ∈ closure primitive_dirs` |
| 10 | lemma | `phiLeft_sqrt_pos` | `(t : ℝ) : 0 < Real.sqrt (1 + t ^ 2)` |
| 11 | lemma | `phiLeft_cont` | `: Continuous phiLeft` |
| 12 | lemma | `phi_neg_den_num_eq_phiLeft` | `(q : ℚ) : phi (-(q.den : ℝ), (q.num : ℝ)) = phiLeft (q : ℝ)` |
| 13 | lemma | `phiLeft_rat_mem_primitive_dirs` | `(q : ℚ) : phiLeft (q : ℝ) ∈ primitive_dirs` |
| 14 | lemma | `phiLeft_in_closure` | `(t : ℝ) : phiLeft t ∈ closure primitive_dirs` |
| 15 | lemma | `zero_one_mem_primitive_dirs` | `: ((0 : ℝ), (1 : ℝ)) ∈ primitive_dirs` |
| 16 | lemma | `zero_neg_one_mem_primitive_dirs` | `: ((0 : ℝ), (-1 : ℝ)) ∈ primitive_dirs` |
| 17 | lemma | `S1_subset_closure_primitive_dirs` | `: S1 ⊆ closure primitive_dirs` |
| 18 | lemma | `P_countable` | `: Set.Countable P` |
| 19 | lemma | `primitive_dirs_countable` | `: Set.Countable primitive_dirs` |
| 20 | theorem | `primitive_dirs_volume_zero` | `: (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) primitive_dirs = 0` |
| 21 | theorem | `primitive_dirs_restrict_volume_zero` | `: ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict S1) primitive_dirs = 0` |
| 22 | theorem | `theorem_1` | `: closure primitive_dirs = S1` |

---

## Tommy/ClosureEmbedding.lean (3 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `default_mem_S1` | `: ((1 : ℝ), (0 : ℝ)) ∈ S1` |
| 2 | theorem | `closure_embedding_eq_toS1` | `(d : D_nz) : closure_embedding d.val = D_nz.toS1 d` |
| 3 | theorem | `closure_embedding_surjective` | `: Function.Surjective closure_embedding` |

---

## Tommy/Compactification.lean (2 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `height_tendsto_zero` | `: Tendsto (fun q : ℕ => (1 : ℝ) / ((q : ℝ) + 1)) atTop (nhds 0)` |
| 2 | theorem | `height_tendsto_onepoint` | `: Tendsto (fun q : ℕ => (OnePoint.some ((1 : ℝ) / ((q : ℝ) + 1)) : OnePoint ℝ)) atTop (nhds (OnePoint.some 0))` |

---

## Tommy/ContinuousTriangle.lean (4 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `subTriangle_subset` | `(N r : ℝ) (hN : 0 ≤ N) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : subTriangle N r ⊆ fullTriangle N` |
| 2 | theorem | `volume_fullTriangle` | `(N : ℝ) (hN : 0 < N) : MeasureTheory.volume (fullTriangle N) = ENNReal.ofReal (N ^ 2 / 2)` |
| 3 | theorem | `volume_subTriangle` | `(N r : ℝ) (hN : 0 < N) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : MeasureTheory.volume (subTriangle N r) = ENNReal.ofReal (r * N ^ 2 / 2)` |
| 4 | theorem | `geometric_uniformity` | `(N r : ℝ) (hN : 0 < N) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : (MeasureTheory.volume (subTriangle N r)).toReal / (MeasureTheory.volume (fullTriangle N)).toReal = r` |

---

## Tommy/CoprimePrimeFactors.lean (2 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `coprime_iff_primeFactors_disjoint` | `(x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) : Nat.Coprime x y ↔ Disjoint x.primeFactors y.primeFactors` |
| 2 | theorem | `rat_reduced_primeFactors_disjoint` | `(q : ℚ) (hnum : q.num ≠ 0) : Disjoint q.num.natAbs.primeFactors q.den.primeFactors` |

---

## Tommy/DMaps.lean (19 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `Rot_zero` | `(a : ℝ) : Rot a zeroD = zeroD` |
| 2 | theorem | `Fold_zero` | `(ph : ℝ) : Fold ph zeroD = zeroD` |
| 3 | theorem | `Dsqrt_zero` | `: Dsqrt zeroD = zeroD` |
| 4 | theorem | `Dsqrt_quadrant_preserving` | `(d : D) (hq : d.q = quadrantOf d.x d.y) (hx : d.x ≠ 0) (hy : d.y ≠ 0) : (Dsqrt d).q = d.q` |
| 5 | theorem | `D.ext` | `{a b : D} (hx : a.x = b.x) (hy : a.y = b.y) (hq : a.q = b.q) : a = b` |
| 6 | theorem | `Rot_comp` | `(a b : ℝ) (d : D) : Rot a (Rot b d) = Rot (a + b) d` |
| 7 | theorem | `Rot_neg_cancel` | `(a : ℝ) (d : D) (hq : d.q = quadrantOf d.x d.y) : Rot (-a) (Rot a d) = d` |
| 8 | theorem | `Rot_preserves_norm_sq` | `(a : ℝ) (d : D) : (Rot a d).x ^ 2 + (Rot a d).y ^ 2 = d.x ^ 2 + d.y ^ 2` |
| 9 | theorem | `Fold_involution` | `(ph : ℝ) (d : D) (hq : d.q = quadrantOf d.x d.y) : Fold ph (Fold ph d) = d` |
| 10 | theorem | `Fold_preserves_norm_sq` | `(ph : ℝ) (d : D) : (Fold ph d).x ^ 2 + (Fold ph d).y ^ 2 = d.x ^ 2 + d.y ^ 2` |
| 11 | theorem | `Rot_two_pi` | `(d : D) (hq : d.q = quadrantOf d.x d.y) : Rot (2 * Real.pi) d = d` |
| 12 | theorem | `Rot_pi_x` | `(d : D) : (Rot Real.pi d).x = -d.x` |
| 13 | theorem | `Rot_pi_y` | `(d : D) : (Rot Real.pi d).y = -d.y` |
| 14 | theorem | `Rot_pi_half_x` | `(d : D) : (Rot (Real.pi / 2) d).x = -d.y` |
| 15 | theorem | `Rot_pi_half_y` | `(d : D) : (Rot (Real.pi / 2) d).y = d.x` |
| 16 | theorem | `Dsqrt_x_sq` | `(d : D) : (Dsqrt d).x ^ 2 = |d.x|` |
| 17 | theorem | `Dsqrt_y_sq` | `(d : D) : (Dsqrt d).y ^ 2 = |d.y|` |

---

## Tommy/DNonzero.lean (3 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `phi_real_mem_S1` | `(x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) : phi (x, y) ∈ S1` |
| 2 | theorem | `toS1_val` | `(d : D_nz) : (D_nz.toS1 d).val = phi (d.val.x, d.val.y)` |
| 3 | theorem | `toS1_surjective` | `: Function.Surjective D_nz.toS1` |

---

## Tommy/EmpiricalCDF.lean (6 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `triangleSize_pos` | `(N : ℕ) (hN : 0 < N) : (0 : ℝ) < (N : ℝ) * ((N : ℝ) + 1) / 2` |
| 2 | lemma | `cdfCount_le_mul` | `(N : ℕ) (x : ℝ) (hx : 0 ≤ x) : cdfCount N x ≤ x * ((N : ℝ) * ((N : ℝ) + 1) / 2)` |
| 3 | lemma | `mul_lt_cdfCount` | `(N : ℕ) (hN : 0 < N) (x : ℝ) (_hx : 0 ≤ x) : x * ((N : ℝ) * ((N : ℝ) + 1) / 2) - (N : ℝ) < cdfCount N x` |
| 4 | theorem | `empiricalCDF_le` | `(N : ℕ) (hN : 0 < N) (x : ℝ) (hx : 0 ≤ x) : empiricalCDF N x ≤ x` |
| 5 | theorem | `lt_empiricalCDF` | `(N : ℕ) (hN : 0 < N) (x : ℝ) (hx : 0 ≤ x) : x - 2 / ((N : ℝ) + 1) < empiricalCDF N x` |
| 6 | theorem | `empiricalCDF_tendsto` | `(x : ℝ) (hx : 0 ≤ x) : Tendsto (fun N => empiricalCDF (N + 1) x) atTop (nhds x)` |

---

## Tommy/Fibration.lean (4 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `farey_rel_proj_compat` | `: ∀ (a b : Cylinder), farey_rel a b → a.1 = b.1` |
| 2 | theorem | `torus_proj_surjective` | `: Function.Surjective torus_proj` |
| 3 | theorem | `fibre_nonempty` | `(θ : ↥S1) : (Fibre θ).Nonempty` |
| 4 | theorem | `torus_proj_of_thomae` | `(p : {p : ℤ × ℤ // p ≠ (0, 0)}) : torus_proj (thomae_torus_embedding p) = (thomae_cylinder_embedding p).1` |

---

## Tommy/HiHat.lean (8 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `mem_hiHatGraph_iff` | `(v : ℝ × ℝ × ℝ) : v ∈ hiHatGraph ↔ ∃ (a b : ℤ), v = ((a : ℝ), (b : ℝ), (tau (a, b) : ℝ))` |
| 2 | theorem | `hiHat_flipX_invariant` | `: ∀ v ∈ hiHatGraph, (-v.1, v.2.1, v.2.2) ∈ hiHatGraph` |
| 3 | theorem | `hiHat_flipY_invariant` | `: ∀ v ∈ hiHatGraph, (v.1, -v.2.1, v.2.2) ∈ hiHatGraph` |
| 4 | theorem | `hiHat_neg_invariant` | `: ∀ v ∈ hiHatGraph, (-v.1, -v.2.1, v.2.2) ∈ hiHatGraph` |
| 5 | theorem | `hiHat_sign_invariant` | `(v : ℝ × ℝ × ℝ) (hv : v ∈ hiHatGraph) (sx sy : Bool) : ((if sx then -v.1 else v.1), (if sy then -v.2.1 else v.2.1), v.2.2) ∈ hiHatGraph` |
| 6 | theorem | `hiHat_symm` | `: ∀ v ∈ hiHatGraph, (v.2.1, v.1, v.2.2) ∈ hiHatGraph` |
| 7 | lemma | `hiHatRevSurface_eq` | `: hiHatRevSurface = hiHatGraph` |
| 8 | theorem | `mem_hiHatVisibleSpikes_iff` | `(a b : ℤ) : ((a : ℝ), (b : ℝ), (1 : ℝ)) ∈ hiHatVisibleSpikes ↔ (a, b) ∈ (visibleLattice : Set (ℤ × ℤ))` |

---

## Tommy/LcmVonMangoldt.lean (7 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `padic_val_lcm_range` | `(N : ℕ) (p : ℕ) (hp : p.Prime) (hN : 0 < N) : padicValNat p (Finset.lcm (Finset.Icc 1 N) id) = Nat.log p N` |
| 2 | lemma | `lcm_Icc_ne_zero` | `(N : ℕ) (hN : 0 < N) : (Finset.lcm (Finset.Icc 1 N) id : ℕ) ≠ 0` |
| 3 | lemma | `primeFactors_lcm_Icc` | `(N : ℕ) (hN : 0 < N) : (Finset.lcm (Finset.Icc 1 N) id : ℕ).primeFactors = Finset.filter Nat.Prime (Finset.Icc 2 N)` |
| 4 | lemma | `Real.log_natCast_eq_sum_factorization` | `(n : ℕ) (hn : n ≠ 0) : Real.log (n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ)` |
| 5 | theorem | `log_lcm_range_eq_sum` | `(N : ℕ) (hN : 0 < N) : Real.log ((Finset.lcm (Finset.Icc 1 N) id : ℕ) : ℝ) = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N), (Nat.log p N : ℝ) * Real.log p` |
| 6 | theorem | `sum_vonMangoldt_eq_sum_primes` | `(N : ℕ) (hN : 0 < N) : (∑ n ∈ Finset.Icc 2 N, vonMangoldt n) = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N), (Nat.log p N : ℝ) * Real.log p` |
| 7 | theorem | `exp_chebyshevPsi_eq_lcm` | `(N : ℕ) (hN : 0 < N) : Real.exp (Chebyshev.psi (N : ℝ)) = ((Finset.lcm (Finset.Icc 1 N) id : ℕ) : ℝ)` |

---

## Tommy/Modular.lean (7 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `sl2_preserves_gcd` | `(M : SL2Z) (v : ℤ × ℤ) : Int.gcd (sl2Act M v).1 (sl2Act M v).2 = Int.gcd v.1 v.2` |
| 2 | theorem | `sl2Act_ne_zero` | `(M : SL2Z) (v : ℤ × ℤ) (h : v ≠ (0, 0)) : sl2Act M v ≠ (0, 0)` |
| 3 | theorem | `sl2Act_eq_zero_iff` | `(M : SL2Z) (v : ℤ × ℤ) : sl2Act M v = (0, 0) ↔ v = (0, 0)` |
| 4 | theorem | `tau_sl2_invariant` | `(M : SL2Z) (v : ℤ × ℤ) (h : v ≠ (0, 0)) : tau (sl2Act M v) = tau v` |
| 5 | theorem | `sl2_preserves_visibleLattice` | `(M : SL2Z) (v : ℤ × ℤ) (h : v ∈ visibleLattice) : sl2Act M v ∈ visibleLattice` |
| 6 | theorem | `sl2Act_S` | `(v : ℤ × ℤ) : sl2Act S_gen v = (-v.2, v.1)` |
| 7 | theorem | `sl2Act_T` | `(v : ℤ × ℤ) : sl2Act T_gen v = (v.1 + v.2, v.2)` |

---

## Tommy/PrimePowerRecovery.lean (3 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `gcd_prime_pow_totient` | `(p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 0 < k) : Nat.gcd (p ^ k) (Nat.totient (p ^ k)) = p ^ (k - 1)` |
| 2 | theorem | `primePowerBase_eq_prime` | `{p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) : primePowerBase (p ^ k) = p` |
| 3 | theorem | `primePowerBase_eq_zero_of_not` | `{n : ℕ} (h : ¬ IsPrimePow n) : primePowerBase n = 0` |

---

## Tommy/ProofTest.lean (5 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `phiRight_sqrt_pos` | `(t : ℝ) : 0 < Real.sqrt (1 + t ^ 2)` |
| 2 | lemma | `phiRight_cont` | `: Continuous phiRight` |
| 3 | lemma | `phi_den_num_eq_phiRight` | `(q : ℚ) : phi ((q.den : ℝ), (q.num : ℝ)) = phiRight (q : ℝ)` |
| 4 | lemma | `phiRight_rat_mem_primitive_dirs` | `(q : ℚ) : phiRight (q : ℝ) ∈ primitive_dirs` |
| 5 | lemma | `phiRight_in_closure` | `(t : ℝ) : phiRight t ∈ closure primitive_dirs` |

---

## Tommy/PythagoreanRational.lean (7 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `sqrt_nat_rational_iff_sq` | `(n : ℕ) : (∃ q : ℚ, (q : ℝ) = Real.sqrt (n : ℝ)) ↔ ∃ m : ℕ, n = m ^ 2` |
| 2 | theorem | `pyth_multiple_iff_sum_sq_is_sq` | `(x y : ℤ) (h : (x, y) ≠ (0, 0)) : (∃ a b c : ℤ, a² + b² = c² ∧ c ≠ 0 ∧ ∃ k : ℤ, x = k * a ∧ y = k * b) ↔ ∃ c : ℤ, x² + y² = c²` |
| 3 | theorem | `div_sqrt_rational_iff_sqrt_rational` | `(x y : ℤ) (h : (x, y) ≠ (0, 0)) : (∃ q : ℚ, (q : ℝ) = (x : ℝ) / √((x : ℝ)² + (y : ℝ)²)) ↔ (∃ q : ℚ, (q : ℝ) = √((x : ℝ)² + (y : ℝ)²))` |
| 4 | theorem | `div_sqrt_rational_iff_sqrt_rational'` | `(x y : ℤ) (h : (x, y) ≠ (0, 0)) : (∃ q : ℚ, (q : ℝ) = (y : ℝ) / √((x : ℝ)² + (y : ℝ)²)) ↔ (∃ q : ℚ, (q : ℝ) = √((x : ℝ)² + (y : ℝ)²))` |
| 5 | theorem | `sqrt_sum_sq_rational_iff_perfect_sq` | `(x y : ℤ) (h : (x, y) ≠ (0, 0)) : (∃ q : ℚ, (q : ℝ) = √((x : ℝ)² + (y : ℝ)²)) ↔ ∃ c : ℤ, x² + y² = c²` |
| 6 | theorem | `phi_rational_first_coord_iff` | `(x y : ℤ) (h : (x, y) ≠ (0, 0)) : (∃ q : ℚ, (phi ((x : ℝ), (y : ℝ))).1 = (q : ℝ)) ↔ (∃ a b c : ℤ, a² + b² = c² ∧ c ≠ 0 ∧ ∃ k : ℤ, x = k * a ∧ y = k * b)` |
| 7 | theorem | `phi_rational_second_coord_iff` | `(x y : ℤ) (h : (x, y) ≠ (0, 0)) : (∃ q : ℚ, (phi ((x : ℝ), (y : ℝ))).2 = (q : ℝ)) ↔ (∃ a b c : ℤ, a² + b² = c² ∧ c ≠ 0 ∧ ∃ k : ℤ, x = k * a ∧ y = k * b)` |

---

## Tommy/Recovery.lean (20 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `prime_dvd_prod_mem` | `(S : Finset ℕ) (q : ℕ) (hq : q.Prime) (h_dvd : q ∣ ∏ p ∈ S, p) (h_primes : ∀ p ∈ S, p.Prime) : q ∈ S` |
| 2 | theorem | `isPrimePow_of_sub_totient_dvd` | `(n : ℕ) (hn : n > 1) (h : g n ∣ n) : IsPrimePow n` |
| 3 | theorem | `lemma_2` | `(n : ℕ) (hn : n > 1) : g n ∣ n ↔ IsPrimePow n` |
| 4 | lemma | `chi1_eq_prime_indicator` | `(n : ℕ) : chi1 n = if n.Prime then 1 else 0` |
| 5 | lemma | `chi_eq_isPrimePow_indicator` | `(n : ℕ) : chi n = if IsPrimePow n then 1 else 0` |
| 6 | theorem | `theorem_3_pi` | `(N : ℕ) : primeCounting N = ∑ n ∈ Finset.Icc 2 N, chi1 n` |
| 7 | theorem | `theorem_3_pi_star` | `(N : ℕ) : primePowerCount N = ∑ n ∈ Finset.Icc 2 N, chi n` |
| 8 | theorem | `theorem_3_theta` | `(N : ℕ) : (∑ n ∈ Finset.Icc 2 N, if n.Prime then (Real.log n : ℝ) else 0) = ∑ n ∈ Finset.Icc 2 N, (chi1 n : ℝ) * Real.log n` |
| 9 | theorem | `theorem_3_theta_eq_chebyshev` | `(N : ℕ) : (∑ n ∈ Finset.Icc 2 N, if n.Prime then (Real.log n : ℝ) else 0) = Chebyshev.theta (N : ℝ)` |
| 10 | theorem | `theorem_3_lambda` | `(n : ℕ) : (vonMangoldt n : ℝ) = (chi n : ℝ) * Real.log ((n : ℝ) / (g n : ℝ))` |
| 11 | theorem | `theorem_3_psi` | `(N : ℕ) : (∑ n ∈ Finset.Icc 2 N, vonMangoldt n) = ∑ n ∈ Finset.Icc 2 N, (chi n : ℝ) * Real.log ((n : ℝ) / (g n : ℝ))` |
| 12 | theorem | `theorem_3_psi_eq_chebyshev` | `(N : ℕ) : (∑ n ∈ Finset.Icc 2 N, vonMangoldt n) = Chebyshev.psi (N : ℝ)` |
| 13 | theorem | `g_prime` | `(p : ℕ) (hp : p.Prime) : g p = 1` |
| 14 | theorem | `g_prime_sq` | `(p : ℕ) (hp : p.Prime) : g (p ^ 2) = p` |
| 15 | theorem | `chi_prime` | `(p : ℕ) (hp : p.Prime) : chi p = 1` |
| 16 | theorem | `chi_not_prime_pow` | `(n : ℕ) (_hn : n > 1) (h : ¬IsPrimePow n) : chi n = 0` |
| 17 | theorem | `chi1_prime` | `(p : ℕ) (hp : p.Prime) : chi1 p = 1` |
| 18 | theorem | `chi1_not_prime` | `(n : ℕ) (h : ¬n.Prime) : chi1 n = 0` |
| 19 | theorem | `theorem_3_omega` | `(p k : ℕ) (hp : p.Prime) (hk : k > 0) : (cardFactors (p^k) : ℝ) = Real.log ((p^k : ℕ) : ℝ) / Real.log (((p^k : ℕ) : ℝ) / ((g (p^k)) : ℝ))` |
| 20 | theorem | `theorem_3_pi_star_eq_count` | `(N : ℕ) : primePowerCount N = Nat.count IsPrimePow (N + 1)` |

---

## Tommy/Semifield.lean (6 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `add_coords` | `(a b : DQ1Zero) : (a + b).x = a.x + b.x ∧ (a + b).y = a.y + b.y` |
| 2 | theorem | `ext` | `{a b : DQ1Zero} (hx : a.x = b.x) (hy : a.y = b.y) : a = b` |
| 3 | theorem | `eq_iff` | `{a b : DQ1Zero} : a = b ↔ a.x = b.x ∧ a.y = b.y` |
| 4 | theorem | `mul_coords` | `(a b : DQ1Zero) : (a * b).x = a.x * b.x ∧ (a * b).y = a.y * b.y` |
| 5 | theorem | `mul_inv_cancel` | `(a : DQ1Zero) (h : a ≠ 0) : a * a⁻¹ = 1` |
| 6 | theorem | `inv_zero` | `: (0 : DQ1Zero)⁻¹ = 0` |

---

## Tommy/Skeleton.lean (2 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `visible_maps_to_top` | `(p : {p : ℤ × ℤ // p ≠ (0, 0)}) (h : tau p.val = 1) : (thomae_cylinder_embedding p).2.1 = 1` |
| 2 | theorem | `visibleLattice_maps_to_top` | `(p : {p : ℤ × ℤ // p ≠ (0, 0)}) (hv : p.val ∈ visibleLattice) : (thomae_cylinder_embedding p).2.1 = 1` |

---

## Tommy/Substrate.lean (12 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `add_preserves_quadrant` | `(a b : D) (ha : a.x > 0 ∧ a.y > 0) (hb : b.x > 0 ∧ b.y > 0) : (D.add a b).q = Quadrant.Q1` |
| 2 | lemma | `k_action_moves_quadrants` | `(d : D) (hd : d.q = Quadrant.Q1) : (K.act K.flipX d).q = Quadrant.Q2` |
| 3 | lemma | `k_act_mul` | `(k1 k2 : K) (d : D) : K.act k1 (K.act k2 d) = K.act (K.mul k1 k2) d` |
| 4 | theorem | `k_act_equiv` | `: Equivalence (fun a b => ∃ k : K, K.act k a = b)` |
| 5 | lemma | `D_toCoords_surjective` | `: Function.Surjective D.toCoords` |
| 6 | lemma | `D_Q1_add_closed` | `(a b : D) (ha : a.x > 0 ∧ a.y > 0) (hb : b.x > 0 ∧ b.y > 0) (_haq : a.q = Quadrant.Q1) (_hbq : b.q = Quadrant.Q1) : (D.add a b).q = Quadrant.Q1` |
| 7 | lemma | `D_zero_not_Q1` | `: quadrantOf 0 0 ≠ Quadrant.Q1` |
| 8 | lemma | `D_Q1_neg_leaves_Q1` | `(x y : ℝ) (hx : x > 0) (hy : y > 0) : quadrantOf (-x) (-y) = Quadrant.Q3` |
| 9 | lemma | `K.mul_assoc` | `(a b c : K) : K.mul (K.mul a b) c = K.mul a (K.mul b c)` |
| 10 | lemma | `K.one_mul` | `(a : K) : K.mul K.id a = a` |
| 11 | lemma | `K.mul_one` | `(a : K) : K.mul a K.id = a` |
| 12 | lemma | `K.inv_mul_cancel` | `(a : K) : K.mul a a = K.id` |
| 13 | lemma | `K.mul_comm` | `(a b : K) : K.mul a b = K.mul b a` |
| 14 | theorem | `K.card_eq` | `: Fintype.card K = 4` |

---

## Tommy/Synthesis.lean (2 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `synthesis_lambda` | `(n : ℕ) : (ArithmeticFunction.vonMangoldt n : ℝ) = (chi n : ℝ) * Real.log ((n : ℝ) / (g n : ℝ))` |
| 2 | theorem | `primitive_dirs_dense_in_S1` | `: closure (primitive_dirs : Set (ℝ × ℝ)) = S1` |

---

## Tommy/Thomae.lean (18 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `int_gcd_ne_zero_of_nonzero` | `{x y : ℤ} (h : (x, y) ≠ (0, 0)) : Int.gcd x y ≠ 0` |
| 2 | lemma | `int_gcd_pos_of_nonzero` | `{x y : ℤ} (h : (x, y) ≠ (0, 0)) : 0 < Int.gcd x y` |
| 3 | lemma | `tau_of_nonzero` | `{p : ℤ × ℤ} (h : p ≠ (0, 0)) : tau p = 1 / (Int.gcd p.1 p.2 : ℚ)` |
| 4 | lemma | `tau_zero` | `: tau (0, 0) = 0` |
| 5 | lemma | `tau_pos_of_nonzero` | `{p : ℤ × ℤ} (h : p ≠ (0, 0)) : 0 < tau p` |
| 6 | theorem | `tau_eq_one_iff_gcd_one` | `{p : ℤ × ℤ} (h : p ≠ (0, 0)) : tau p = 1 ↔ Int.gcd p.1 p.2 = 1` |
| 7 | theorem | `tau_eq_one_iff_visible` | `{p : ℤ × ℤ} (h : p ≠ (0, 0)) : tau p = 1 ↔ p ∈ visibleLattice` |
| 8 | theorem | `tau_invariant_flipX` | `(x y : ℤ) : tau (-x, y) = tau (x, y)` |
| 9 | theorem | `tau_invariant_flipY` | `(x y : ℤ) : tau (x, -y) = tau (x, y)` |
| 10 | theorem | `tau_invariant_neg` | `(x y : ℤ) : tau (-x, -y) = tau (x, y)` |
| 11 | theorem | `tau_symm` | `(x y : ℤ) : tau (x, y) = tau (y, x)` |
| 12 | theorem | `tau_quadrant_invariant` | `(x y : ℤ) (sx sy : Bool) : tau (if sx then -x else x, if sy then -y else y) = tau (x, y)` |
| 13 | theorem | `visibleLattice_eq_primitiveVectors` | `: visibleLattice = {p : ℤ × ℤ | p ≠ (0 : ℤ × ℤ) ∧ Int.gcd p.1 p.2 = 1}` |
| 14 | theorem | `origin_not_visible` | `: (⟨0, 0⟩ : ℤ × ℤ) ∉ visibleLattice` |
| 15 | theorem | `tau_le_one_of_nonzero` | `{p : ℤ × ℤ} (h : p ≠ (0, 0)) : tau p ≤ 1` |
| 16 | theorem | `semiprime_quadratic` | `(p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : p * q - Nat.totient (p * q) + 1 = p + q` |
| 17 | theorem | `semiprime_quadratic_roots` | `(p q : ℕ) : p * p + p * q = (p + q) * p ∧ q * q + p * q = (p + q) * q` |
| 18 | theorem | `tau_two_zero` | `: tau ((2 : ℤ), (0 : ℤ)) = 1 / 2` |
| 19 | theorem | `tau_two_three` | `: tau ((2 : ℤ), (3 : ℤ)) = 1` |
| 20 | theorem | `tau_two_four` | `: tau ((2 : ℤ), (4 : ℤ)) = 1 / 2` |

---

## Tommy/Torus.lean (1 declaration)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `farey_rel_is_equiv` | `: Equivalence farey_rel` |

---

## Tommy/VisibleDensity.lean (3 declarations)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | theorem | `count_coprime_pairs_eq_moebius_sum` | `(N : ℕ) (hN : 0 < N) : (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.gcd p.1 p.2 = 1)).card : ℤ) = ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.moebius d * (N / d : ℤ)²` |
| 2 | theorem | `moebius_sum_inv_sq_eq` | `: HasSum (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)²) (6 / Real.pi²)` |
| 3 | theorem | `visible_density` | `: Filter.Tendsto (fun N : ℕ => (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.gcd p.1 p.2 = 1)).card : ℝ) / (N : ℝ)²) Filter.atTop (nhds (6 / Real.pi²))` |

---

## Test/Auxiliary Files

### TestCheck.lean (16 declarations — duplicates of Closure.lean)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `S1_isClosed` | `: IsClosed S1` |
| 2 | lemma | `primitive_dirs_subset_S1` | `: primitive_dirs ⊆ S1` |
| 3 | lemma | `phiRight_sqrt_pos` | `(t : ℝ) : 0 < Real.sqrt (1 + t ^ 2)` |
| 4 | lemma | `phiRight_cont` | `: Continuous phiRight` |
| 5 | lemma | `phi_den_num_eq_phiRight` | `(q : ℚ) : phi ((q.den : ℝ), (q.num : ℝ)) = phiRight (q : ℝ)` |
| 6 | lemma | `phiRight_rat_mem_primitive_dirs` | `(q : ℚ) : phiRight (q : ℝ) ∈ primitive_dirs` |
| 7 | lemma | `phiRight_in_closure` | `(t : ℝ) : phiRight t ∈ closure primitive_dirs` |
| 8 | lemma | `phiLeft_sqrt_pos` | `(t : ℝ) : 0 < Real.sqrt (1 + t ^ 2)` |
| 9 | lemma | `phiLeft_cont` | `: Continuous phiLeft` |
| 10 | lemma | `phi_neg_den_num_eq_phiLeft` | `(q : ℚ) : phi (-(q.den : ℝ), (q.num : ℝ)) = phiLeft (q : ℝ)` |
| 11 | lemma | `phiLeft_rat_mem_primitive_dirs` | `(q : ℚ) : phiLeft (q : ℝ) ∈ primitive_dirs` |
| 12 | lemma | `phiLeft_in_closure` | `(t : ℝ) : phiLeft t ∈ closure primitive_dirs` |
| 13 | lemma | `zero_one_mem_primitive_dirs` | `: ((0 : ℝ), (1 : ℝ)) ∈ primitive_dirs` |
| 14 | lemma | `zero_neg_one_mem_primitive_dirs` | `: ((0 : ℝ), (-1 : ℝ)) ∈ primitive_dirs` |
| 15 | lemma | `S1_subset_closure_primitive_dirs` | `: S1 ⊆ closure primitive_dirs` |
| 16 | theorem | `theorem_1` | `: closure primitive_dirs = S1` |

### TestCheck2.lean (4 declarations — duplicates/variants of Recovery.lean)

| # | Kind | Name | Statement |
|---|------|------|-----------|
| 1 | lemma | `isPrimePow_of_sub_totient_dvd` | `(n : ℕ) (hn : n > 1) (h : g n ∣ n) : IsPrimePow n` |
| 2 | theorem | `lemma_2` | `(n : ℕ) (hn : n > 1) : g n ∣ n ↔ IsPrimePow n` |
| 3 | lemma | `chi_eq_isPrimePow_indicator` | `(n : ℕ) : chi n = if IsPrimePow n then 1 else 0` |
| 4 | theorem | `theorem_3_pi_star_v2` | `(N : ℕ) : prime_power_count N = ∑ n ∈ Finset.Icc 2 N, chi n` |

---

## Summary

| File | Theorems | Lemmas | Total |
|------|----------|--------|-------|
| Tommy/Closure.lean | 5 | 17 | 22 |
| Tommy/ClosureEmbedding.lean | 2 | 1 | 3 |
| Tommy/Compactification.lean | 2 | 0 | 2 |
| Tommy/ContinuousTriangle.lean | 4 | 0 | 4 |
| Tommy/CoprimePrimeFactors.lean | 2 | 0 | 2 |
| Tommy/DMaps.lean | 17 | 0 | 17 |
| Tommy/DNonzero.lean | 2 | 1 | 3 |
| Tommy/EmpiricalCDF.lean | 3 | 3 | 6 |
| Tommy/Fibration.lean | 3 | 1 | 4 |
| Tommy/HiHat.lean | 6 | 2 | 8 |
| Tommy/LcmVonMangoldt.lean | 4 | 3 | 7 |
| Tommy/Modular.lean | 7 | 0 | 7 |
| Tommy/PrimePowerRecovery.lean | 3 | 0 | 3 |
| Tommy/ProofTest.lean | 0 | 5 | 5 |
| Tommy/PythagoreanRational.lean | 7 | 0 | 7 |
| Tommy/Recovery.lean | 16 | 4 | 20 |
| Tommy/Semifield.lean | 6 | 0 | 6 |
| Tommy/Skeleton.lean | 2 | 0 | 2 |
| Tommy/Substrate.lean | 2 | 12 | 14 |
| Tommy/Synthesis.lean | 2 | 0 | 2 |
| Tommy/Thomae.lean | 15 | 5 | 20 |
| Tommy/Torus.lean | 1 | 0 | 1 |
| Tommy/VisibleDensity.lean | 3 | 0 | 3 |
| TestCheck.lean | 1 | 15 | 16 |
| TestCheck2.lean | 2 | 2 | 4 |
| **TOTAL** | **106** | **71** | **177** |

> **Note:** `TestCheck.lean`, `TestCheck2.lean`, and `Tommy/ProofTest.lean` are test/auxiliary files containing duplicates of declarations from the main `Tommy/` modules. Excluding those, the main library contains **152 unique declarations** (101 theorems + 51 lemmas).

