# Lean Gap Ranking and Progress Report

**Project:** `tommy_project`  
**Central thesis:** D substrate + Thomae/visible lattice arithmetic + S¹ closure + recovery.  
**Authoritative QLD source:** `qld_numbers_v11.pdf` (supersedes the prior QLD draft).  
**Build status after this session:** `lake build Tommy` — BUILD SUCCESSFUL, 0 `sorry`/`axiom`/`constant` in production files. Session 25: Asymptotic uniformity (analytic bridge, geometric bridge, compactification, closure embedding). §3f(a) D→A.

---

## 1. Ranked Open Issues — Full Status Table

Reconstructed from all prior sessions. **A** = fully proved, **C** = stated but unproved or
not yet bridged, **D** = not formalized at all.

| Rank | Description | File(s) | Key theorem(s) | Status |
|------|-------------|---------|-----------------|--------|
| 1 | S¹ closure (`theorem_1`) | `Closure.lean` | `theorem_1` | **A** |
| 2 | g(n)∣n ↔ IsPrimePow (`lemma_2`) | `Recovery.lean` | `lemma_2`, `isPrimePow_of_sub_totient_dvd` | **A** |
| 3 | τ definition + basic properties | `Thomae.lean` | `tau`, `tau_of_nonzero`, `tau_zero`, `tau_pos_of_nonzero` | **A** |
| 4 | τ = 1 ↔ visible | `Thomae.lean` | `tau_eq_one_iff_gcd_one`, `tau_eq_one_iff_visible` | **A** |
| 5 | τ ≤ 1 | `Thomae.lean` | `tau_le_one_of_nonzero` | **A** |
| 6 | τ quadrant invariance | `Thomae.lean` | `tau_invariant_flipX/Y/neg`, `tau_quadrant_invariant` | **A** |
| 7 | τ symmetry | `Thomae.lean` | `tau_symm` | **A** |
| 8 | Semiprime quadratic | `Thomae.lean` | `semiprime_quadratic`, `semiprime_quadratic_roots` | **A** |
| 9 | θ formula (Theorem 3) | `Recovery.lean` | `theorem_3_theta` | **A** |
| 10 | Λ formula (Theorem 3) | `Recovery.lean` | `theorem_3_lambda` | **A** |
| 11 | ψ formula (Theorem 3) | `Recovery.lean` | `theorem_3_psi` | **A** |
| 12 | π formula (Theorem 3) | `Recovery.lean` | `theorem_3_pi` | **A** |
| 13 | π* formula (Theorem 3) | `Recovery.lean` | `theorem_3_pi_star` | **A** |
| 14 | Ω formula (Theorem 3) | `Recovery.lean` | `theorem_3_omega` | **A** |
| 15 | DQ1Zero semifield | `Semifield.lean` | `CommSemiring DQ1Zero`, `mul_inv_cancel` | **A** |
| 16 | Hi-Hat surface | `HiHat.lean` | `hiHat_sign_invariant`, `hiHat_symm`, `mem_hiHatVisibleSpikes_iff` | **A** |
| 17 | Skeleton embedding | `Skeleton.lean` | `thomae_cylinder_embedding`, `thomae_torus_embedding` | **A** |
| 18 | Visible → top | `Skeleton.lean` | `visible_maps_to_top`, `visibleLattice_maps_to_top` | **A** |
| 19 | Torus/Farey quotient | `Torus.lean` | `farey_rel_is_equiv`, `FareyTorus` | **A** |
| 20 | Farey-rel projection | `Fibration.lean` | `farey_rel_proj_compat`, `torus_proj` | **A** |
| 21 | Concrete evaluations (g, χ, χ₁) | `Recovery.lean` | `g_prime`, `g_prime_sq`, `chi_prime`, `chi1_prime`, etc. | **A** |
| 22 | θ bridge → Mathlib `Chebyshev.theta` | `Recovery.lean` | `theorem_3_theta_eq_chebyshev` | **A** |
| 23 | ψ bridge → Mathlib `Chebyshev.psi` | `Recovery.lean` | `theorem_3_psi_eq_chebyshev` | **A** |
| 24 | π* bridge → Mathlib `Nat.count IsPrimePow` | `Recovery.lean` | `theorem_3_pi_star_eq_count` | **A** |
| 25 | Klein-four group K | `Substrate.lean` | `K.instCommGroup`, `K.card_eq`, `K.instMulActionD` | **A** |
| 26 | D substrate definition | `Substrate.lean` | `D`, `quadrantOf`, `D.add` | **A** |
| 27 | D coordinates + Q1 | `Substrate.lean` | `D.toCoords`, `D_toCoords_surjective`, `D_Q1` | **A** |
| 28a | K quotient C | `Substrate.lean` | `k_act_equiv`, `C` | **A** |
| 28b | exp(ψ(N)) = lcm(1..N) | `LcmVonMangoldt.lean` | `exp_chebyshevPsi_eq_lcm` | **A** |
| 29 | Fibration/torus surjectivity | `Fibration.lean` | `torus_proj_surjective`, `fibre_nonempty`, `torus_proj_of_thomae` | **A** |
| 30a | phi properties | `Closure.lean` | `phi_idempotent_on_S1`, `phi_mem_S1` | **A** |
| 30b | D_nz → S¹ surjection | `DNonzero.lean` | `D_nz.toS1`, `toS1_surjective` | **A** |
| 31 | Primitive dirs countable + measure zero | `Closure.lean` | `P_countable`, `primitive_dirs_countable`, `primitive_dirs_volume_zero` | **A** |
| 32 | Synthesis re-exports | `Synthesis.lean` | `synthesis_lambda`, `primitive_dirs_dense_in_S1` | **A** |
| 33 | Rot properties | `DMaps.lean` | `Rot_comp`, `Rot_neg_cancel`, `Rot_preserves_norm_sq`, `Rot_two_pi` | **A** |
| 34 | Fold properties | `DMaps.lean` | `Fold_involution`, `Fold_preserves_norm_sq` | **A** |
| 35 | Dsqrt properties | `DMaps.lean` | `Dsqrt_x_sq`, `Dsqrt_y_sq`, `Dsqrt_quadrant_preserving` | **A** |
| 36 | SL(2,ℤ) action | `Modular.lean` | `sl2Act`, `sl2_preserves_gcd`, `sl2Act_ne_zero` | **A** |
| 37 | τ SL(2,ℤ)-invariance | `Modular.lean` | `tau_sl2_invariant`, `sl2_preserves_visibleLattice` | **A** |
| 38 | S,T generators | `Modular.lean` | `S_gen`, `T_gen`, `sl2Act_S`, `sl2Act_T` | **A** |
| §3f(a) | `closure_embedding : D → S1` | `ClosureEmbedding.lean` | `closure_embedding`, `closure_embedding_surjective` | **A** |
| §3f(b) | `recovery_map : D → ℕ` | — | — | **D** |
| §3f(c) | Pythagorean-rational classification | `PythagoreanRational.lean` | `phi_rational_first_coord_iff`, `phi_rational_second_coord_iff` | **A** |
| §3f(d) | Pythagorean-rationality ↔ IsPrimePow bridge | — | — | **D** |
| χ helpers | chi/chi1 indicator lemmas | `Recovery.lean` | `chi_eq_isPrimePow_indicator`, `chi1_eq_prime_indicator` | **A** |
| tau evals | Concrete τ evaluations | `Thomae.lean` | `tau_two_zero`, `tau_two_three`, `tau_two_four` | **A** |
| vis-density | Visible lattice density 6/π² (3 steps) | `VisibleDensity.lean` | `count_coprime_pairs_eq_moebius_sum`, `moebius_sum_inv_sq_eq`, `visible_density` | **A** |
| coprime-pf | Coprimality ↔ disjoint prime factors | `CoprimePrimeFactors.lean` | `coprime_iff_primeFactors_disjoint`, `rat_reduced_primeFactors_disjoint` | **A** |
| ecdf | Empirical CDF convergence (analytic bridge) | `EmpiricalCDF.lean` | `empiricalCDF_tendsto`, `empiricalCDF_le`, `lt_empiricalCDF` | **A** |
| compact | Compactified product space (topological bridge) | `Compactification.lean` | `totalSpace_compact`, `height_tendsto_zero`, `height_tendsto_onepoint` | **A** |
| geom-unif | Geometric uniformity (continuous triangle) | `ContinuousTriangle.lean` | `geometric_uniformity`, `volume_fullTriangle`, `volume_subTriangle` | **A** |

**Summary:** All formalized ranks are **A** (fully proved, no sorry). Only §3f sub-blockers (b) and (d) remain **D** (not formalized). §3f(a) was resolved in Session 25.

---

## 2. What Was Moved to Category A This Session

### Session 25: Asymptotic Uniformity — Analytic Bridge, Geometric Bridge, Compactification, Closure Embedding

Based on two foundational papers on asymptotic uniformity of rational ratios and visible lattice structure.

**New files:** `Tommy/EmpiricalCDF.lean`, `Tommy/Compactification.lean`, `Tommy/ClosureEmbedding.lean`, `Tommy/ContinuousTriangle.lean`

#### Empirical CDF (Analytic Bridge)

| File | Theorem | Statement | Proof approach | Status |
|---|---|---|---|---|
| `EmpiricalCDF.lean` | `triangleSize_pos` | N*(N+1)/2 > 0 for N ≥ 1 | positivity | **A** |
| `EmpiricalCDF.lean` | `cdfCount_le_mul` | C_N(x) ≤ x·N(N+1)/2 | ⌊xq⌋ ≤ xq summed | **A** |
| `EmpiricalCDF.lean` | `mul_lt_cdfCount` | x·N(N+1)/2 - N < C_N(x) | ⌊xq⌋ > xq-1 summed | **A** |
| `EmpiricalCDF.lean` | `empiricalCDF_le` | F_N(x) ≤ x | From cdfCount_le_mul, divide by |S_N| | **A** |
| `EmpiricalCDF.lean` | `lt_empiricalCDF` | x - 2/(N+1) < F_N(x) | From mul_lt_cdfCount, divide by |S_N| | **A** |
| `EmpiricalCDF.lean` | `empiricalCDF_tendsto` | F_N(x) → x as N → ∞ | Squeeze theorem on the above bounds | **A** |

#### Compactification (Topological Bridge)

| File | Theorem | Statement | Proof approach | Status |
|---|---|---|---|---|
| `Compactification.lean` | `totalSpace_compact` | AddCircle(1) × OnePoint ℝ is compact | Tychonoff (inferInstance) | **A** |
| `Compactification.lean` | `height_tendsto_zero` | 1/(q+1) → 0 as q → ∞ | const_div_atTop | **A** |
| `Compactification.lean` | `height_tendsto_onepoint` | OnePoint.some(1/(q+1)) → some(0) | Continuous OnePoint.some composed with height_tendsto_zero | **A** |

#### Closure Embedding (§3f(a) D→A)

| File | Theorem | Statement | Proof approach | Status |
|---|---|---|---|---|
| `ClosureEmbedding.lean` | `closure_embedding` | D → ↥S1 (extends D_nz.toS1 to all D) | If-then-else on nonzero; zero maps to (1,0) | **A** |
| `ClosureEmbedding.lean` | `closure_embedding_eq_toS1` | Agrees with D_nz.toS1 on nonzero elements | By definition | **A** |
| `ClosureEmbedding.lean` | `closure_embedding_surjective` | Surjective onto S¹ | Lifts D_nz.toS1_surjective | **A** |

#### Geometric Uniformity (Continuous Triangle)

| File | Theorem | Statement | Proof approach | Status |
|---|---|---|---|---|
| `ContinuousTriangle.lean` | `subTriangle_subset` | subTriangle ⊆ fullTriangle for r ∈ [0,1] | Direct inequality | **A** |
| `ContinuousTriangle.lean` | `volume_fullTriangle` | volume({0≤x≤y≤N}) = N²/2 | Fubini: ∫₀ᴺ y dy | **A** |
| `ContinuousTriangle.lean` | `volume_subTriangle` | volume({0≤x≤ry, 0≤y≤N}) = rN²/2 | Fubini: ∫₀ᴺ ry dy | **A** |
| `ContinuousTriangle.lean` | `geometric_uniformity` | Area ratio = r (geometric proof X/Y ~ U(0,1)) | Ratio of volumes | **A** |

**Axioms (all theorems):** `propext`, `Classical.choice`, `Quot.sound` (standard only).

---

### Session 24: Visible Density 6/π² + Coprimality Characterizations

**New files:** `Tommy/VisibleDensity.lean`, `Tommy/CoprimePrimeFactors.lean`

#### Visible density (Rank 27): all 3 steps closed

| File | Theorem | Statement | Proof approach | Status |
|---|---|---|---|---|
| `VisibleDensity.lean` | `count_coprime_pairs_eq_moebius_sum` | ♯{coprime pairs in [1,N]²} = ∑ μ(d)·⌊N/d⌋² | Möbius inversion: ∑_{d\|n} μ(d) = [n=1], swap summation order, count multiples | **A** |
| `VisibleDensity.lean` | `moebius_sum_inv_sq_eq` | HasSum (λ d, μ(d)/d²) (6/π²) | `LSeries_one_mul_Lseries_moebius` at s=2 + `riemannZeta_two` + convert complex HasSum to real | **A** |
| `VisibleDensity.lean` | `visible_density` | Density of coprime pairs → 6/π² | Step 1 / N², bound |floor(N/d)² - N²/d²| ≤ 2N/d + 1, harmonic sum ≤ log N + 1, squeeze to 0 | **A** |

#### Coprimality ↔ disjoint prime factors

| File | Theorem | Statement | Proof approach | Status |
|---|---|---|---|---|
| `CoprimePrimeFactors.lean` | `coprime_iff_primeFactors_disjoint` | Nat.Coprime x y ↔ Disjoint x.primeFactors y.primeFactors | Direct from `Nat.disjoint_primeFactors` | **A** |
| `CoprimePrimeFactors.lean` | `rat_reduced_primeFactors_disjoint` | For q : ℚ with q.num ≠ 0, prime factors of num and den are disjoint | From `Rat.reduced` + `Nat.disjoint_primeFactors` | **A** |

**Axioms (all 5 theorems):** `propext`, `Classical.choice`, `Quot.sound` (standard only).

---

### Session 23: Rank 28 step 3 of 3 — CLOSED

**File:** `Tommy/LcmVonMangoldt.lean`

| File | Theorem/def | Statement | Proof approach | Status |
|---|---|---|---|---|
| `Tommy/LcmVonMangoldt.lean` | `sum_vonMangoldt_eq_sum_primes` | `∑_{n=2}^{N} Λ(n) = ∑_{p prime ≤ N} (Nat.log p N) · log p` | Filter to IsPrimePow terms, biUnion decomposition over prime base powers, vonMangoldt_apply_pow + vonMangoldt_apply_prime for each summand | **A** |
| `Tommy/LcmVonMangoldt.lean` | `exp_chebyshevPsi_eq_lcm` | `exp(ψ(N)) = lcm(1..N)` | Chain: theorem_3_psi_eq_chebyshev → sum_vonMangoldt_eq_sum_primes → log_lcm_range_eq_sum → exp_log on lcm_Icc_ne_zero | **A** |

**Axioms:** `propext`, `Classical.choice`, `Quot.sound` (standard only).

---

### Session 22: Rank 28 step 2 of 3 — log_lcm_range_eq_sum

**File:** `Tommy/LcmVonMangoldt.lean`

| File | Theorem/def | Statement | Proof approach | Status |
|---|---|---|---|---|
| `Tommy/LcmVonMangoldt.lean` | `lcm_Icc_ne_zero` | `(Finset.lcm (Finset.Icc 1 N) id : ℕ) ≠ 0` | lcm_eq_zero_iff gives element = 0, contradicts Icc 1 N membership | **A** |
| `Tommy/LcmVonMangoldt.lean` | `primeFactors_lcm_Icc` | `(lcm).primeFactors = filter Nat.Prime (Icc 2 N)` | Finset.ext: forward uses prime ∣ lcm ∣ N!, backward uses Finset.dvd_lcm | **A** |
| `Tommy/LcmVonMangoldt.lean` | `Real.log_natCast_eq_sum_factorization` | `log n = Σ_{p ∈ primeFactors n} factorization(n)(p) · log p` | factorization_prod_pow_eq_self + log_prod + log_pow | **A** |
| `Tommy/LcmVonMangoldt.lean` | `log_lcm_range_eq_sum` | `log(lcm(1..N)) = Σ_{p prime ≤ N} (Nat.log p N) · log p` | Combines the three helpers above with padic_val_lcm_range | **A** |

**Axioms:** `propext`, `Classical.choice`, `Quot.sound` (standard only).

---

### Session 21: Rank 28 step 1 of 3 — padic_val_lcm_range

**New file:** `Tommy/LcmVonMangoldt.lean`

| File | Theorem/def | Statement | Proof approach | Status |
|---|---|---|---|---|
| `Tommy/LcmVonMangoldt.lean` | `padic_val_lcm_range` | `padicValNat p (Finset.lcm (Finset.Icc 1 N) id) = Nat.log p N` | Show p^(log p N) divides lcm (since p^(log p N) ∈ Icc 1 N), then show p^(log p N + 1) does not divide lcm (since no element of Icc 1 N has p-adic val > log p N). Uses `padicValNat_dvd_iff_le`, `Finset.dvd_lcm`, `Nat.factorization_lcm`. | **A** |

This is step 1 of 3 for rank 28 (exp ψ = lcm). Steps 2 and 3 are NOT in scope this session.

**Axioms:** `propext`, `Classical.choice`, `Quot.sound` (standard only).

---

### Session 20: Stale-status reconciliation + Rank 24 π* bridge (C → A)

**Task 1 — Reconciliation sweep:** Swept all C/D items against the codebase. Found:
- **Rank 24** was C (π* bridge to Mathlib not yet built) → now **A** (proved in Task 2).
- §3f sub-blockers (a), (b), (d) remain **D** (no code exists for these).
- No other stale C/D items found — every formalized theorem builds without sorry.

**Task 2 — Rank 24 bridge theorem:**

| File | Theorem/def | Statement | Proof approach | Status |
|---|---|---|---|---|
| `Tommy/Recovery.lean` | `theorem_3_pi_star_eq_count` | `primePowerCount N = Nat.count IsPrimePow (N + 1)` | Unfold `primePowerCount`, rewrite `Nat.count` via `count_eq_card_filter_range`, then show the two finite sums agree (elements 0 and 1 contribute 0 since `¬IsPrimePow 0` and `¬IsPrimePow 1`). | **A** |

**Proof architecture:** Mirrors the π bridge (`theorem_3_pi`) and the θ/ψ bridges from Sessions 9/19:
1. `primePowerCount N` unfolds to `∑ n ∈ Finset.Icc 2 N, if IsPrimePow n then 1 else 0`.
2. `Nat.count IsPrimePow (N+1)` equals `(Finset.range (N+1)).filter IsPrimePow).card` via `Nat.count_eq_card_filter_range`.
3. The filter-card converts to a sum of indicators; elements 0 and 1 are filtered out since `¬IsPrimePow 0` and `¬IsPrimePow 1`.
4. The Mathlib counterpart is `Nat.count IsPrimePow`, which plays the same role as `Nat.primeCounting'` (= `Nat.count Nat.Prime`) for primes. No dedicated named prime-power counting function exists in Mathlib, but `Nat.count IsPrimePow` is the canonical composition.

**Axioms:** `propext`, `Classical.choice`, `Quot.sound` (standard only).

---

### Prior sessions (18–19)

### Session 18 (Pythagorean-rational classification, §3f sub-blocker (c) → A)

**New file:** `Tommy/PythagoreanRational.lean` (117 lines).

| File | Theorem/def | Statement | Proof approach | Status |
|---|---|---|---|---|
| `Tommy/PythagoreanRational.lean` | `phi_rational_first_coord_iff` | For integer pairs (x,y) ≠ (0,0), the first coordinate of phi(x,y) is rational iff (x,y) is an integer multiple of a Pythagorean pair | Three-step equivalence chain | **A** |
| `Tommy/PythagoreanRational.lean` | `phi_rational_second_coord_iff` | Same for second coordinate | Analogous | **A** |

### Session 19 (Rank 23: ψ bridge to Mathlib Chebyshev.psi, C → A)

| File | Theorem/def | Statement | Proof approach | Status |
|---|---|---|---|---|
| `Tommy/Recovery.lean` | `theorem_3_psi_eq_chebyshev` | `∑ n ∈ Finset.Icc 2 N, vonMangoldt n = Chebyshev.psi (N : ℝ)` | Unfold Chebyshev.psi, Nat.floor_natCast, Finset.sum_subset | **A** |

(Prior sessions 1–17 are documented in ARISTOTLE_SUMMARY.md.)

---

## 3a. Visible Density (6/π²) — Step Tracker

| Step | Description | Status | Notes |
|------|-------------|--------|-------|
| 1 | `count_coprime_pairs_eq_moebius_sum`: Möbius count identity | **A** | Session 24. `Tommy/VisibleDensity.lean`. |
| 2 | `moebius_sum_inv_sq_eq`: ∑ μ(d)/d² = 6/π² | **A** | Session 24. Uses `LSeries_one_mul_Lseries_moebius` + `riemannZeta_two`. |
| 3 | `visible_density`: density limit | **A** | Session 24. Combines steps 1–2 with asymptotic error bound. |

---

## 3b. Rank 28 (exp ψ = lcm) — Step Tracker

| Step | Description | Status | Notes |
|------|-------------|--------|-------|
| 1 | `padic_val_lcm_range`: padicValNat p (lcm 1..N) = Nat.log p N | **A** | Session 21. `Tommy/LcmVonMangoldt.lean`. |
| 2 | `log_lcm_range_eq_sum`: log(lcm) = Σ_p (log_p N) · log p | **A** | Session 22. `Tommy/LcmVonMangoldt.lean`. |
| 3 | `sum_vonMangoldt_eq_sum_primes` + `exp_chebyshevPsi_eq_lcm` | **A** | Session 23. `Tommy/LcmVonMangoldt.lean`. |

---

## 3f. Synthesis Instantiation — Sub-blocker Status

| Sub-blocker | Description | Status | Notes |
|---|---|---|---|
| (a) | `closure_embedding : D → S1` | **A** | Session 25. `closure_embedding` in `ClosureEmbedding.lean`. Maps nonzero via phi, zero to (1,0). Surjective. |
| (b) | `recovery_map : D → ℕ` | **D** | No honest formula available. |
| (c) | Pythagorean-rational classification | **A** | Session 18. `phi_rational_first_coord_iff`, `phi_rational_second_coord_iff`. |
| (d) | Pythagorean-rationality ↔ IsPrimePow bridge | **D** | Not formalized. |

---

## 4. Session 25 Status Changes

| Item | Old Status | New Status | Reason |
|------|-----------|------------|--------|
| §3f(a) | D | **A** | `closure_embedding` + `closure_embedding_surjective` proved in `Tommy/ClosureEmbedding.lean`. |
| ecdf | — (new) | **A** | `empiricalCDF_tendsto` + bounds proved in `Tommy/EmpiricalCDF.lean`. |
| compact | — (new) | **A** | `totalSpace_compact` + height convergence in `Tommy/Compactification.lean`. |
| geom-unif | — (new) | **A** | `geometric_uniformity` + volume computations in `Tommy/ContinuousTriangle.lean`. |

---

## 4prev. Session 24 Status Changes

| Item | Old Status | New Status | Reason |
|------|-----------|------------|--------|
| vis-density (all 3 steps) | — (new) | **A** | `count_coprime_pairs_eq_moebius_sum` + `moebius_sum_inv_sq_eq` + `visible_density` proved in `Tommy/VisibleDensity.lean`. |
| coprime-pf | — (new) | **A** | `coprime_iff_primeFactors_disjoint` + `rat_reduced_primeFactors_disjoint` proved in `Tommy/CoprimePrimeFactors.lean`. |

---

## 4prev. Session 23 Status Changes

| Item | Old Status | New Status | Reason |
|------|-----------|------------|--------|
| Rank 28 step 3 | D | **A** | `sum_vonMangoldt_eq_sum_primes` + `exp_chebyshevPsi_eq_lcm` proved in `Tommy/LcmVonMangoldt.lean`. |
| Rank 28 overall | D | **A** | All 3 steps complete. |

### Session 22 Status Changes

| Item | Old Status | New Status | Reason |
|------|-----------|------------|--------|
| Rank 28 step 2 | D (not formalized) | **A** | `log_lcm_range_eq_sum` + 3 helper lemmas proved in `Tommy/LcmVonMangoldt.lean`. |

### Session 21 Status Changes

| Item | Old Status | New Status | Reason |
|------|-----------|------------|--------|
| Rank 28 step 1 | D (not formalized) | **A** | `padic_val_lcm_range` proved in `Tommy/LcmVonMangoldt.lean`. |

### Session 20 Status Changes

| Rank | Old Status | New Status | Reason |
|------|-----------|------------|--------|
| 24 | C | **A** | `theorem_3_pi_star_eq_count` bridges `primePowerCount N` to `Nat.count IsPrimePow (N+1)`. Proved in `Tommy/Recovery.lean`. |

No other stale C/D items found during reconciliation sweep.

---

## 5. Build Verification

### Session 25 (Asymptotic Uniformity: Analytic Bridge, Geometric Bridge, Compactification, Closure Embedding)

```
lake build Tommy
✔ [8048/8048] Built Tommy
Build completed successfully (8048 jobs).
```

```
grep -n sorry Tommy/EmpiricalCDF.lean Tommy/Compactification.lean Tommy/ClosureEmbedding.lean Tommy/ContinuousTriangle.lean
(no output — zero sorry)
```

```
#print axioms empiricalCDF_tendsto
-- [propext, Classical.choice, Quot.sound]

#print axioms totalSpace_compact
-- [propext, Classical.choice, Quot.sound]

#print axioms closure_embedding_surjective
-- [propext, Classical.choice, Quot.sound]

#print axioms geometric_uniformity
-- [propext, Classical.choice, Quot.sound]

#print axioms volume_fullTriangle
-- [propext, Classical.choice, Quot.sound]
```

---

### Session 24 (Visible Density + Coprimality Characterizations)

```
lake build Tommy.VisibleDensity
✔ [8026/8026] Built Tommy.VisibleDensity
Build completed successfully (8026 jobs).
```

```
lake build Tommy.CoprimePrimeFactors
✔ [8026/8026] Built Tommy.CoprimePrimeFactors
Build completed successfully (8026 jobs).
```

```
grep -n sorry Tommy/VisibleDensity.lean Tommy/CoprimePrimeFactors.lean
(no output — zero sorry)
```

```
#print axioms count_coprime_pairs_eq_moebius_sum
-- [propext, Classical.choice, Quot.sound]

#print axioms moebius_sum_inv_sq_eq
-- [propext, Classical.choice, Quot.sound]

#print axioms visible_density
-- [propext, Classical.choice, Quot.sound]

#print axioms coprime_iff_primeFactors_disjoint
-- [propext, Classical.choice, Quot.sound]

#print axioms rat_reduced_primeFactors_disjoint
-- [propext, Classical.choice, Quot.sound]
```

---

### Session 23 (Rank 28 step 3: CLOSED — sum_vonMangoldt_eq_sum_primes + exp_chebyshevPsi_eq_lcm)

```
lake build Tommy
✔ [8041/8042] Built Tommy (8.2s)
Build completed successfully (8042 jobs).
```

```
grep -n sorry Tommy/LcmVonMangoldt.lean
(no output — zero sorry)
```

```
grep -n axiom Tommy/LcmVonMangoldt.lean
(no output — zero axiom)
```

```
grep -n constant Tommy/LcmVonMangoldt.lean
(no output — zero constant)
```

```
#print axioms sum_vonMangoldt_eq_sum_primes
-- 'sum_vonMangoldt_eq_sum_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```
#print axioms exp_chebyshevPsi_eq_lcm
-- 'exp_chebyshevPsi_eq_lcm' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Session 22 (Rank 28 step 2: log_lcm_range_eq_sum)

```
lake build Tommy
✔ [8026/8026] Built Tommy.LcmVonMangoldt (12s)
Build completed successfully (8026 jobs).
```

```
grep -n sorry Tommy/LcmVonMangoldt.lean
(no output — zero sorry)
```

```
grep -n axiom Tommy/LcmVonMangoldt.lean
(no output — zero axiom)
```

```
grep -n constant Tommy/LcmVonMangoldt.lean
(no output — zero constant)
```

```
#print axioms log_lcm_range_eq_sum
-- 'log_lcm_range_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Session 21 (Rank 28 step 1: padic_val_lcm_range)

```
lake build Tommy
✔ [8041/8042] Built Tommy (9.5s)
Build completed successfully (8042 jobs).
```

```
grep -n sorry Tommy/LcmVonMangoldt.lean
(no output — zero sorry)
```

```
#print axioms padic_val_lcm_range
-- 'padic_val_lcm_range' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Session 20 (Reconciliation + Rank 24 π* bridge)

```
lake build Tommy
✔ [8040/8041] Built Tommy (8.9s)
Build completed successfully (8041 jobs).
```

```
grep -RIn --include='*.lean' -E '\bsorry\b|^[[:space:]]*axiom |^[[:space:]]*constant ' Tommy/ Tommy.lean | grep -v TestCheck || true
```
(empty output — zero sorry, zero axiom declarations, zero constant declarations)

```
#print axioms theorem_3_pi_star_eq_count
-- 'theorem_3_pi_star_eq_count' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Session 19 (Rank 23: ψ bridge)
```
lake build Tommy → Build completed successfully (8041 jobs).
grep sorry/axiom/constant → (empty)
#print axioms theorem_3_psi_eq_chebyshev → [propext, Classical.choice, Quot.sound]
```

### Session 18 (Pythagorean-rational classification)
```
lake build Tommy → Build completed successfully (8041 jobs).
grep sorry/axiom/constant → (empty)
#print axioms phi_rational_first_coord_iff → [propext, Classical.choice, Quot.sound]
```
