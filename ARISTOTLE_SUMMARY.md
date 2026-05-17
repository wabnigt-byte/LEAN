# Summary of changes for run 5dfe831a-bde8-4757-bc29-57bac7b90dca
I've created `THEOREMS_AND_LEMMAS.md` — a comprehensive, exhaustive list of every theorem and lemma declaration in the repository.

**Summary:**
- **177 total declarations** (106 theorems + 71 lemmas) across 25 Lean files
- **152 unique declarations** in the main `Tommy/` library (excluding test/duplicate files)
- Organized by file, with each entry showing: kind (theorem/lemma), name, and full type signature
- Includes a summary table at the bottom with per-file counts

The files with the most declarations are:
- `Tommy/Closure.lean` — 22 (density of primitive directions, closure = S¹)
- `Tommy/Recovery.lean` — 20 (prime-power detection, Chebyshev functions)
- `Tommy/Thomae.lean` — 20 (Thomae function τ, visibility, symmetries)
- `Tommy/DMaps.lean` — 17 (rotation, fold, sqrt operations on D)
- `Tommy/Substrate.lean` — 14 (Klein-four group, quadrant structure)

Test/auxiliary files (`TestCheck.lean`, `TestCheck2.lean`, `ProofTest.lean`) contain 25 declarations that are duplicates or variants of main library content.

# Summary of changes for run d3f2916b-1f69-4b96-92d0-2d8359d70c16
Created `Tommy/PrimePowerRecovery.lean` with all requested definitions and theorems, fully proved (0 sorry):

**Definitions:**
- `primePowerBase (n : ℕ) : ℕ` — returns `n / gcd(n, φ(n))` when `n` is a prime power, 0 otherwise
- `D.toNat (d : D) : ℕ` — projects D to ℕ via `⌊x² + y²⌋₊` (natural floor of norm squared)
- `recovery_map (d : D) : ℕ` — composes `D.toNat` with `primePowerBase`

**Theorems (all fully proved):**
- `gcd_prime_pow_totient` — `gcd(p^k, φ(p^k)) = p^(k-1)` for prime p, k ≥ 1 (helper)
- `primePowerBase_eq_prime` — `primePowerBase(p^k) = p` for prime p, k ≥ 1
- `primePowerBase_eq_zero_of_not` — `primePowerBase(n) = 0` when n is not a prime power

All axioms are standard (`propext`, `Classical.choice`, `Quot.sound`). Added `import Tommy.PrimePowerRecovery` to `Tommy.lean`. Build is clean with no warnings.

# Summary of changes for run 57daaee0-c0e1-4831-aabe-f9162c8070d5
## Session 25: Asymptotic Uniformity — 4 New Files, 1 D→A Resolution

Based on the two foundational papers provided, I formalized three major components of the asymptotic uniformity framework and resolved one of the remaining D items.

### D Item Resolved

**§3f(a) `closure_embedding : D → S1`** — **D → A**
- New file: `Tommy/ClosureEmbedding.lean`
- Defines `closure_embedding : D → ↥S1` extending `D_nz.toS1` to all of D (zero maps to (1,0))
- Proves `closure_embedding_surjective` and `closure_embedding_eq_toS1` (agreement with D_nz.toS1)

### New Formalizations from the Papers

**1. Empirical CDF Convergence (Analytic Bridge)** — `Tommy/EmpiricalCDF.lean` (6 theorems, 0 sorry)
- Defines `cdfCount N x = Σ_{q=1}^{N} ⌊xq⌋` and `empiricalCDF N x = C_N(x) / |S_N|`
- Proves the squeeze bounds: `empiricalCDF_le` (F_N(x) ≤ x) and `lt_empiricalCDF` (x - 2/(N+1) < F_N(x))
- Proves the main convergence: `empiricalCDF_tendsto` — F_N(x) → x as N → ∞ (CDF of U(0,1))

**2. Compactified Product Space (Topological Bridge)** — `Tommy/Compactification.lean` (5 results, 0 sorry)
- Sets up `TotalSpace = AddCircle(1) × OnePoint ℝ` with compact topology (Tychonoff)
- Defines the `stationMap` sending (p,q) to (p/q mod 1, 1/q)
- Proves `height_tendsto_zero` (1/q → 0) and `height_tendsto_onepoint` (convergence in OnePoint ℝ)

**3. Geometric Uniformity (Continuous Triangle)** — `Tommy/ContinuousTriangle.lean` (4 theorems, 0 sorry)
- Computes `volume_fullTriangle`: volume({0≤x≤y≤N}) = N²/2 via Fubini
- Computes `volume_subTriangle`: volume({0≤x≤ry, 0≤y≤N}) = rN²/2 via Fubini
- Proves `geometric_uniformity`: area ratio = r, the continuous proof that X/Y ~ U(0,1)

### Remaining D Items

§3f(b) `recovery_map : D → ℕ` and §3f(d) `Pythagorean-rationality ↔ IsPrimePow bridge` remain D. These items require a mathematical connection between Pythagorean triples and prime powers that is not provided in the papers and appears to be project-specific rather than a standard mathematical result.

### Build Verification
- `lake build Tommy` — 8048 jobs, 0 errors, 0 sorry
- All axioms standard: `[propext, Classical.choice, Quot.sound]`
- Updated `lean_gap_ranking_and_progress.md` with Session 25 details

# Summary of changes for run 54411e27-7d02-4e45-b3dc-1909477a7764
## Session 24: Visible Density + Coprimality Characterizations

### Answer to your question

**Yes, coprimality (visibility) is exactly equivalent to disjoint prime factor sets.** This holds for both lattice points and fractions:

- **Lattice point (x, y):** `gcd(x, y) = 1` ⟺ `x.primeFactors ∩ y.primeFactors = ∅`
- **Fraction x/y:** every `ℚ` value in Lean is automatically stored in lowest terms (`Rat.reduced`), which guarantees `num.primeFactors` and `den.primeFactors` are disjoint.

Mathlib already has this as `Nat.disjoint_primeFactors`. Both characterizations are now formalized.

### New files

**1. `Tommy/CoprimePrimeFactors.lean`** — Two theorems (both fully proved, 0 sorry):

- `coprime_iff_primeFactors_disjoint`: For nonzero x, y : ℕ, `Nat.Coprime x y ↔ Disjoint x.primeFactors y.primeFactors`
- `rat_reduced_primeFactors_disjoint`: For q : ℚ with nonzero numerator, the prime factors of numerator and denominator are disjoint

**2. `Tommy/VisibleDensity.lean`** — Three theorems for the visible density result (all fully proved, 0 sorry):

- **Step 1** `count_coprime_pairs_eq_moebius_sum`: #{coprime pairs in [1,N]²} = ∑ μ(d)·⌊N/d⌋²
- **Step 2** `moebius_sum_inv_sq_eq`: HasSum (λ d, μ(d)/d²) (6/π²)
- **Step 3** `visible_density`: density of coprime pairs → 6/π² as N → ∞

### Verification

- `lake build Tommy` — BUILD SUCCESSFUL (8044 jobs), 0 errors
- `grep sorry` — zero matches across all production files
- `#print axioms` for all 5 new theorems: `[propext, Classical.choice, Quot.sound]` (standard only)

### Files modified
- `Tommy/CoprimePrimeFactors.lean` — NEW
- `Tommy/VisibleDensity.lean` — NEW  
- `Tommy.lean` — added imports for both new files
- `lean_gap_ranking_and_progress.md` — Session 24 block, §3a step tracker, §4 status changes, §5 build verification

# Summary of changes for run e53f3347-a586-4a60-a507-a9584a1f30fc
## Session 23: Rank 28 Step 3 — CLOSED ✓

Successfully added and fully proved both requested theorems in `Tommy/LcmVonMangoldt.lean`:

### (1) Von Mangoldt regrouping lemma

```lean
theorem sum_vonMangoldt_eq_sum_primes (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 2 N, vonMangoldt n) =
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N),
      (Nat.log p N : ℝ) * Real.log p
```

**Proof approach:** 
1. Filter LHS to IsPrimePow terms (non-prime-powers contribute Λ(n) = 0).
2. Show `filter IsPrimePow (Icc 2 N) = biUnion (filter Prime (Icc 2 N)) (fun p => image (p^·) (Icc 1 (Nat.log p N)))` — a decomposition by base prime.
3. Pairwise disjointness: different base primes produce different prime powers (via `minFac` uniqueness).
4. Each inner sum evaluates to `(Nat.log p N) * log p` using `vonMangoldt_apply_pow` + `vonMangoldt_apply_prime`.

### (2) Closing theorem (rank 28 done)

```lean
theorem exp_chebyshevPsi_eq_lcm (N : ℕ) (hN : 0 < N) :
    Real.exp (Chebyshev.psi (N : ℝ)) =
    ((Finset.lcm (Finset.Icc 1 N) id : ℕ) : ℝ)
```

**Proof chain:**
- `theorem_3_psi_eq_chebyshev` (Session 19): ∑ Λ = Chebyshev.psi N
- `sum_vonMangoldt_eq_sum_primes` (this session): ∑ Λ = ∑_p (Nat.log p N) · log p  
- `log_lcm_range_eq_sum` (Session 22): log(lcm) = ∑_p (Nat.log p N) · log p
- `Real.exp_log` on `lcm_Icc_ne_zero` (Session 22)

### Verification

- **`lake build Tommy`:** Build completed successfully (8042 jobs), 0 errors.
- **`grep sorry/axiom/constant`:** zero matches — completely clean.
- **`#print axioms sum_vonMangoldt_eq_sum_primes`:** `[propext, Classical.choice, Quot.sound]` (standard only).
- **`#print axioms exp_chebyshevPsi_eq_lcm`:** `[propext, Classical.choice, Quot.sound]` (standard only).

### Files modified

- `Tommy/LcmVonMangoldt.lean` — Added 2 new theorems (both fully proved, 0 sorry).
- `lean_gap_ranking_and_progress.md` — Session 23 block in §2, rank 28 step 3 = A in §3b, rank 28 overall D → A in §1/§4, §5 build verification.

# Summary of changes for run ec2a0bd5-ce1c-41ad-b46e-032a0a0280d6
## Session 22: Rank 28 Step 2 — `log_lcm_range_eq_sum` (D → A)

Successfully added and fully proved the theorem `log_lcm_range_eq_sum` in `Tommy/LcmVonMangoldt.lean`:

```lean
theorem log_lcm_range_eq_sum (N : ℕ) (hN : 0 < N) :
    Real.log ((Finset.lcm (Finset.Icc 1 N) id : ℕ) : ℝ) =
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N),
      (Nat.log p N : ℝ) * Real.log p
```

### Helper lemmas (all fully proved)

1. **`lcm_Icc_ne_zero`** — `lcm(Icc 1 N) ≠ 0` for `N ≥ 1` (via `lcm_eq_zero_iff` + membership bound).

2. **`primeFactors_lcm_Icc`** — `primeFactors(lcm(1..N)) = filter Nat.Prime (Icc 2 N)`. Forward: any prime dividing lcm divides N! hence ≤ N. Backward: any prime p ≤ N is in Icc 1 N, so p | lcm by `Finset.dvd_lcm`.

3. **`Real.log_natCast_eq_sum_factorization`** — For n ≠ 0, `log(n) = Σ_{p ∈ primeFactors n} factorization(n)(p) · log(p)`. Uses `Nat.factorization_prod_pow_eq_self` + `Real.log_prod` + `Real.log_pow`.

### Main theorem proof architecture

Combines all three helpers with Session 21's `padic_val_lcm_range`:
- Apply `log_natCast_eq_sum_factorization` (using `lcm_Icc_ne_zero`).
- Rewrite sum domain via `primeFactors_lcm_Icc`.
- Replace `factorization p = padicValNat p = Nat.log p N` for each prime summand (via `Nat.factorization_def` + `padic_val_lcm_range`).

### Verification

- **`lake build Tommy`**: Build completed successfully (8026 jobs, 0 errors).
- **`grep sorry/axiom/constant`**: empty — zero matches.
- **`#print axioms log_lcm_range_eq_sum`**: `[propext, Classical.choice, Quot.sound]` (standard only).

### Files modified
- `Tommy/LcmVonMangoldt.lean` — Added 4 new theorems (all fully proved, 0 sorry).
- `lean_gap_ranking_and_progress.md` — Session 22 block in §2, step 2 = A in §3b rank 28 step tracker, §4 status changes, §5 build verification.

# Summary of changes for run 91a36c16-52c9-44cf-908e-e36b77f03e1b
## Session 21: Rank 28 Step 1 — `padic_val_lcm_range` (D → A)

### New file: `Tommy/LcmVonMangoldt.lean`

Added and fully proved the theorem:

```lean
theorem padic_val_lcm_range (N : ℕ) (p : ℕ) (hp : p.Prime) (hN : 0 < N) :
    padicValNat p (Finset.lcm (Finset.Icc 1 N) id) =
    Nat.log p N
```

**No existing Mathlib version was found** — searched extensively for `padicValNat_lcm`, `emultiplicity_lcm`, `multiplicity_lcm`, `Finset.sup_padicValNat`, and related names. This theorem had to be proved from scratch.

**Proof approach:**
- **Lower bound:** `p^(Nat.log p N) ∈ Icc 1 N` (since `p^(log_p N) ≤ N`), so `p^(log_p N) | lcm` by `Finset.dvd_lcm`, giving `log_p N ≤ padicValNat p (lcm)`.
- **Upper bound:** For every `n ∈ Icc 1 N`, `n.factorization p ≤ log_p N` (since `p^(n.factorization p) | n ≤ N`). The proof shows `(lcm).factorization p ≤ sup` over elements, using `Nat.factorization_lcm` and induction on the finset via `Finset.lcm_insert`.

### Verification
- `lake build Tommy` → 8042 jobs, 0 errors
- `grep sorry` → empty (zero sorry in all production files)
- `grep axiom/constant` → empty
- `#print axioms padic_val_lcm_range` → `[propext, Classical.choice, Quot.sound]` (standard only)

### Files modified
- `Tommy/LcmVonMangoldt.lean` — NEW (fully proved, 0 sorry)
- `Tommy.lean` — added `import Tommy.LcmVonMangoldt`
- `lean_gap_ranking_and_progress.md` — Session 21 block in §2, new §3b rank 28 step tracker (step 1 = A, steps 2–3 = D / not in scope), §4 status changes, §5 build verification

# Summary of changes for run 30deeec0-8c1b-4cff-99a5-df62c292bb13
# Session 20: Stale-Status Reconciliation + Rank 24 π* Bridge

## Task 1 — Stale-Status Reconciliation

Swept all C/D items against the codebase. The full ranking table in `lean_gap_ranking_and_progress.md` §1 was reconstructed (it had been truncated to "See prior sessions") with all 38+ items and their current status.

**Findings:**
- **Rank 24** was the only stale C item — it was marked C but had no code yet (unlike rank 23 which was already proved). Addressed in Task 2.
- **§3f sub-blockers (a), (b), (d)** remain D — no code exists for these.
- **All other items** are confirmed A — every formalized theorem builds without sorry, verified by `grep -rn sorry Tommy/` returning empty and `lake build Tommy` succeeding (8041 jobs, 0 errors).

No stale C/D discrepancies were found beyond rank 24.

## Task 2 — Rank 24: π* → Mathlib Bridge (C → A)

**New theorem** in `Tommy/Recovery.lean` (lines 539–545):

```lean
theorem theorem_3_pi_star_eq_count (N : ℕ) :
    primePowerCount N = Nat.count IsPrimePow (N + 1)
```

**Mathlib counterpart:** `Nat.count IsPrimePow` — the canonical composition using the same pattern as `Nat.primeCounting'` (which is literally `Nat.count Nat.Prime`). No dedicated named prime-power counting function exists in Mathlib, but `Nat.count IsPrimePow` is the exact structural analog.

**Proof architecture** (mirrors Session 9 θ / Session 19 ψ bridges):
1. Unfold `primePowerCount` to `∑ n ∈ Icc 2 N, if IsPrimePow n then 1 else 0`.
2. Rewrite `Nat.count IsPrimePow (N+1)` via `count_eq_card_filter_range`.
3. Show the two finite sets agree — elements 0 and 1 are excluded since `¬IsPrimePow 0` and `¬IsPrimePow 1`.

## Verification

- **`lake build Tommy`:** Build completed successfully (8041 jobs).
- **`grep sorry/axiom/constant`:** empty — zero matches in production files.
- **`#print axioms theorem_3_pi_star_eq_count`:** `[propext, Classical.choice, Quot.sound]` (standard only).
- No existing proved theorems were modified.

## Files Modified
- `Tommy/Recovery.lean` — Added `theorem_3_pi_star_eq_count` (6 lines, fully proved).
- `lean_gap_ranking_and_progress.md` — Reconstructed full §1 ranking table, added Session 20 block in §2, status change in §4, build verification in §5.

# Summary of changes for run 821a078d-78df-458d-91a1-3dc516e59f52
## Session 19: Rank 23 — ψ bridge to Mathlib `Chebyshev.psi` (C → A)

**Result:** The theorem `theorem_3_psi_eq_chebyshev` was already present and fully proved in `Tommy/Recovery.lean` (lines 469–487) from an earlier session. No code changes to Recovery.lean were needed.

### Theorem statement
```lean
theorem theorem_3_psi_eq_chebyshev (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, vonMangoldt n) = Chebyshev.psi (N : ℝ)
```

### Proof architecture (mirrors Session 9's θ bridge)
1. Unfold `Chebyshev.psi` to `∑ n ∈ Finset.Ioc 0 ⌊N⌋, Λ(n)`.
2. `Nat.floor_natCast` simplifies `⌊(N : ℝ)⌋₊ = N`.
3. `Finset.sum_subset` bridges `Icc 2 N ⊆ Ioc 0 N`.
4. The extra element `1 ∈ Ioc 0 N \ Icc 2 N` contributes `vonMangoldt 1 = 0` via `vonMangoldt_apply_one`.

### Verification
- **`lake build Tommy`:** Build completed successfully (8041 jobs).
- **grep sorry/axiom/constant:** (empty — zero matches).
- **`#print axioms theorem_3_psi_eq_chebyshev`:** `[propext, Classical.choice, Quot.sound]` (standard only).
- Lines 443–446 of Recovery.lean (the existing ψ identity `theorem_3_psi`) are untouched.

### Files modified
- `lean_gap_ranking_and_progress.md` — Updated with Session 19 block in §2, rank 23 C→A in §4, §5 build verification appended.

# Summary of changes for run 742e7427-c259-403c-b735-9b429bace675
## Session 18: Pythagorean-Rational Classification (§3f sub-blocker (c) → A)

### New file: `Tommy/PythagoreanRational.lean` (117 lines, fully proved, 0 sorry)

Added the two requested theorems plus 7 helper lemmas, all fully proved:

**Main theorems:**
- `phi_rational_first_coord_iff` — For integer pairs (x,y) ≠ (0,0), the first coordinate of `phi(x,y)` is rational iff (x,y) is an integer multiple of a Pythagorean pair (a,b) with a²+b²=c², c≠0.
- `phi_rational_second_coord_iff` — Analogous for the second coordinate.

**Helper lemmas (all proved):**
- `sqrt_nat_rational_iff_sq` — √n ∈ ℚ ↔ n is a perfect square (for n : ℕ)
- `pyth_multiple_iff_sum_sq_is_sq` — The Pythagorean-multiple RHS ↔ x²+y² is a perfect square
- `div_sqrt_rational_iff_sqrt_rational` — x/√(x²+y²) ∈ ℚ ↔ √(x²+y²) ∈ ℚ
- `div_sqrt_rational_iff_sqrt_rational'` — y/√(x²+y²) ∈ ℚ ↔ √(x²+y²) ∈ ℚ
- `sqrt_sum_sq_rational_iff_perfect_sq` — √(x²+y²) ∈ ℚ ↔ ∃ c : ℤ, x²+y² = c²
- `int_pair_sq_sum_pos`, `sqrt_int_pair_ne_zero` — positivity helpers

**Proof architecture:** Three-step equivalence chain:
1. x/√(x²+y²) ∈ ℚ ↔ √(x²+y²) ∈ ℚ (rational divided by rational)
2. √(x²+y²) ∈ ℚ ↔ x²+y² is a perfect square (rational root theorem: √n = p/q reduced implies q=1)
3. x²+y² perfect square ↔ Pythagorean-multiple condition (take k=1 backward; k²c² = (kc)² forward)

### Files modified:
- `Tommy/PythagoreanRational.lean` — NEW
- `Tommy.lean` — added `import Tommy.PythagoreanRational`
- `lean_gap_ranking_and_progress.md` — CREATED with Session 18 block, §3f sub-blocker (c) status updated to A, §5 build verification

### Build verification:
```
lake build Tommy → Build completed successfully (8041 jobs)
grep sorry/axiom/constant → (empty: zero matches)
#print axioms → [propext, Classical.choice, Quot.sound] (standard only)
```

### Remaining Synthesis sub-blockers:
- (a) `closure_embedding : D → S1` — partially addressed (D_nz.toS1)
- (b) `recovery_map : D → ℕ` — no honest formula
- (d) Bridge Pythagorean-rationality ↔ IsPrimePow — absent from formalization

# Summary of changes for run 5854d6ea-2db5-4611-82a6-008df788a6a8
## Summary of D→A Progress

The project now builds cleanly (`lake build Tommy` — 0 errors, 0 warnings, 0 sorries) after fixing a Lean toolchain version mismatch (v4.29.1 → v4.28.0 to match Mathlib) and repairing two renamed Mathlib lemmas in `Recovery.lean`.

### New theorems and definitions added (all fully proven, Category A):

**DMaps.lean — Rot/Fold/Dsqrt properties (ranks 33–35 enrichment):**
- `D.ext` — extensionality for `D` elements
- `Rot_comp` — rotation composition: `Rot a (Rot b d) = Rot (a + b) d`
- `Rot_neg_cancel` — `Rot (-a) (Rot a d) = d` (for well-tagged elements)
- `Rot_preserves_norm_sq` — rotation preserves x² + y²
- `Rot_two_pi` — `Rot (2π) d = d` (for well-tagged elements)
- `Rot_pi_x/y` — `Rot π` negates both coordinates
- `Rot_pi_half_x/y` — `Rot (π/2)` swaps: x ↦ -y, y ↦ x
- `Rot_x/y`, `Fold_x/y` — coordinate projection simp lemmas
- `Fold_involution` — `Fold ph (Fold ph d) = d` (for well-tagged elements)
- `Fold_preserves_norm_sq` — fold preserves x² + y²
- `Dsqrt_x_sq`, `Dsqrt_y_sq` — `(Dsqrt d).x² = |d.x|` and similarly for y

**Substrate.lean — Klein-four group enrichment (rank 25 enrichment):**
- `K.instFintype` — `Fintype K` instance (4 elements)
- `K.card_eq` — `Fintype.card K = 4`
- `K.instMulActionD` — `MulAction K D` instance for the sign-flip action

**Closure.lean — phi properties (rank 1 enrichment):**
- `phi_idempotent_on_S1` — phi is the identity on S¹
- `phi_mem_S1` — phi maps any nonzero vector to S¹

**Fibration.lean — torus projection properties (rank 29 enrichment):**
- `torus_proj_surjective` — every S¹ direction is hit by the torus projection
- `fibre_nonempty` — every fibre is nonempty
- `torus_proj_of_thomae` — skeleton embedding projects to the correct direction

**DNonzero.lean — D_nz embedding (rank 30b enrichment):**
- `D_nz.toS1_surjective` — `D_nz.toS1` is surjective

**Modular.lean — SL(2,ℤ) generators (rank 36–38 enrichment):**
- `S_gen`, `T_gen` — standard S and T generators of SL(2,ℤ)
- `sl2Act_S` — S sends (a,b) to (-b,a)
- `sl2Act_T` — T sends (a,b) to (a+b,b)

**Recovery.lean — concrete evaluations (rank 21 enrichment):**
- `g_prime` — g(p) = 1 for prime p
- `g_prime_sq` — g(p²) = p for prime p
- `chi_prime` — χ(p) = 1 for prime p
- `chi_not_prime_pow` — χ(n) = 0 when n is not a prime power
- `chi1_prime` — χ₁(p) = 1 for prime p
- `chi1_not_prime` — χ₁(n) = 0 when n is not prime

**Thomae.lean — concrete tau evaluations (ranks 3–8 enrichment):**
- `tau_one_zero`, `tau_zero_one`, `tau_one_one` — τ = 1 for visible pairs
- `tau_two_zero` — τ(2,0) = 1/2
- `tau_two_three` — τ(2,3) = 1 (coprime pair)
- `tau_two_four` — τ(2,4) = 1/2 (gcd = 2)

### Build fix:
- Fixed `lean-toolchain` from v4.29.1 to v4.28.0 (matching Mathlib)
- Fixed `Nat.prod_factorization_pow_eq_self` → `Nat.factorization_prod_pow_eq_self` + `Finsupp.prod`
- Fixed `Finset.one_le_prod` → `Finset.one_le_prod'`