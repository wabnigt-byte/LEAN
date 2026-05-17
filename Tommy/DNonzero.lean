import Tommy.Substrate
import Tommy.Closure

/-!
## D_nz: nonzero subtype of D and embedding into S¹

Session 17 — partially addresses Synthesis blocker §3f field 1.

We define `D_nz` as the subtype of `D` consisting of elements whose coordinate
pair `(x, y)` is nonzero, and we construct a map `D_nz.toS1 : D_nz → ↥S1`
via the normalisation map `phi`.

**phi is real, not integer-only:** `phi : ℝ × ℝ → ℝ × ℝ` normalises any nonzero
real vector to the unit circle.  For `d : D_nz`, `(d.val.x, d.val.y) ≠ (0, 0)`,
so `phi (d.val.x, d.val.y) ∈ S1` is provable without extending phi.
-/

open Real Set

/-- The nonzero subtype of `D`: elements whose coordinate pair is not `(0, 0)`. -/
def D_nz : Type := { d : D // d.x ≠ 0 ∨ d.y ≠ 0 }

/-! ### Helper lemma: phi of a nonzero real pair lands in S¹ -/

/-- For any real pair `(x, y)` with `x ≠ 0 ∨ y ≠ 0`, the normalisation
    `phi (x, y)` lies on the unit circle `S1`. -/
lemma phi_real_mem_S1 (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) :
    phi (x, y) ∈ S1 := by
  simp only [phi, S1, Set.mem_setOf_eq]
  have hpos : 0 < x ^ 2 + y ^ 2 := by
    rcases h with hx | hy
    · have : x ^ 2 > 0 := by positivity
      linarith [sq_nonneg y]
    · have : y ^ 2 > 0 := by positivity
      linarith [sq_nonneg x]
  have hsqrt_ne : Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  rw [div_pow, div_pow, ← add_div,
      div_eq_one_iff_eq (pow_ne_zero _ hsqrt_ne),
      Real.sq_sqrt hpos.le]

/-! ### Embedding D_nz → ↥S1 -/

namespace D_nz

/-- Embed a nonzero `D`-element into `S¹` by normalising its coordinate pair. -/
noncomputable def toS1 (d : D_nz) : ↥S1 :=
  ⟨phi (d.val.x, d.val.y), phi_real_mem_S1 d.val.x d.val.y d.property⟩

/-! ### Sanity lemma -/

/-- The underlying `ℝ × ℝ`-value of the S¹ element produced by `toS1`
    is exactly `phi (d.val.x, d.val.y)`. -/
theorem toS1_val (d : D_nz) :
    (D_nz.toS1 d).val = phi (d.val.x, d.val.y) := rfl

/-- `toS1` is surjective: every point on S¹ is the normalisation of some nonzero D-element. -/
theorem toS1_surjective : Function.Surjective D_nz.toS1 := by
  intro ⟨v, hv⟩
  -- v ∈ S1, so v.1^2 + v.2^2 = 1, hence v ≠ (0,0)
  simp only [S1, Set.mem_setOf_eq] at hv
  have hne : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hv
  -- Construct a D element with coordinates v.1, v.2
  refine ⟨⟨⟨v.1, v.2, Quadrant.Q1⟩, hne⟩, ?_⟩
  -- Show toS1 of this element equals ⟨v, hv⟩
  apply Subtype.ext
  simp only [toS1, phi]
  have hsqrt : Real.sqrt (v.1 ^ 2 + v.2 ^ 2) = 1 := by
    rw [hv, Real.sqrt_one]
  simp [hsqrt]

end D_nz
