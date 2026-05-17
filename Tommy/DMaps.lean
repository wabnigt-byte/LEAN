import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Tommy.Substrate

/-!
# D-map definitions: Rot, Fold, Dsqrt  (v11 §Axiom 2–3)

This file defines three maps on the directional plane `D`:

* `Rot α d`   — rotation by angle `α` (rank 33)
* `Fold φ d`  — reflection across the line at angle `φ` (rank 34)
* `Dsqrt d`   — componentwise signed square root (rank 35)

Each definition sets `q = quadrantOf` of the output coordinates, as required by the `D`
structure.  Four sanity lemmas (zero-preservation) and one honest quadrant-preservation
theorem for `Dsqrt` are proved.

**File placement justification:** These are new operations *on* `D`.  They depend on
`quadrantOf` and the `D` structure which live in `Tommy/Substrate.lean`.  A dedicated file
avoids cluttering `Substrate.lean` with trigonometric and square-root imports that are
irrelevant to the algebraic-subtype content already there.

**`zeroD` element:** Defined here as the element with coordinates `(0, 0)` tagged to
`Quadrant.Q4`, consistent with `quadrantOf 0 0 = Q4` (the fallback branch of `quadrantOf`).
-/

open Real

/-- The zero element of D: coordinates (0, 0) tagged to Quadrant.Q4 (the fallback quadrant),
consistent with `quadrantOf 0 0 = Q4` as proved in `Substrate.lean`. -/
noncomputable def zeroD : D := ⟨0, 0, Quadrant.Q4⟩

-- We intentionally avoid a `0_D` notation: Lean 4's atom parser rejects notation strings
-- that begin with a digit.  Use `zeroD` directly in theorem statements.

/-! ## Rot: rotation by angle a -/

/-- Rotate a `D`-element by angle `a` (counter-clockwise).

The output coordinates follow the standard rotation matrix formula, and the quadrant tag is
recomputed from the result. -/
noncomputable def Rot (a : ℝ) (d : D) : D :=
  let x' := d.x * Real.cos a - d.y * Real.sin a
  let y' := d.x * Real.sin a + d.y * Real.cos a
  ⟨x', y', quadrantOf x' y'⟩

/-! ## Fold: reflection across line through origin at angle ph -/

/-- Reflect a `D`-element across the line through the origin at angle `ph`.

The output coordinates follow the standard reflection-across-angle formula, and the quadrant
tag is recomputed from the result. -/
noncomputable def Fold (ph : ℝ) (d : D) : D :=
  let x' := d.x * Real.cos (2 * ph) + d.y * Real.sin (2 * ph)
  let y' := d.x * Real.sin (2 * ph) - d.y * Real.cos (2 * ph)
  ⟨x', y', quadrantOf x' y'⟩

/-! ## Dsqrt: componentwise signed square root -/

/-- Componentwise signed square root on `D`.

Each coordinate is mapped by `Real.sign x * Real.sqrt |x|`, which is sign-preserving
(positive input → positive output, negative input → negative output, zero → zero).
The quadrant tag is recomputed from the result. -/
noncomputable def Dsqrt (d : D) : D :=
  let x' := Real.sign d.x * Real.sqrt |d.x|
  let y' := Real.sign d.y * Real.sqrt |d.y|
  ⟨x', y', quadrantOf x' y'⟩

/-! ## Zero-preservation sanity lemmas -/

/-- Rotation fixes the zero element. -/
theorem Rot_zero (a : ℝ) : Rot a zeroD = zeroD := by
  unfold Rot zeroD
  simp [quadrantOf]

/-- Fold fixes the zero element. -/
theorem Fold_zero (ph : ℝ) : Fold ph zeroD = zeroD := by
  unfold Fold zeroD
  simp [quadrantOf]

/-- Dsqrt fixes the zero element. -/
theorem Dsqrt_zero : Dsqrt zeroD = zeroD := by
  unfold Dsqrt zeroD
  simp [quadrantOf, Real.sign_zero]

/-! ## Quadrant preservation for Dsqrt -/

/-- Private helper: for `x > 0`, the signed square root is positive. -/
private lemma signSqrt_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.sign x * Real.sqrt |x| := by
  rw [Real.sign_of_pos hx, abs_of_pos hx, one_mul]
  exact Real.sqrt_pos_of_pos hx

/-- Private helper: for `x < 0`, the signed square root is negative. -/
private lemma signSqrt_neg {x : ℝ} (hx : x < 0) :
    Real.sign x * Real.sqrt |x| < 0 := by
  rw [Real.sign_of_neg hx, abs_of_neg hx]
  have h : 0 < Real.sqrt (-x) := Real.sqrt_pos_of_pos (by linarith)
  nlinarith

/-- The quadrantOf two values that are both positive equals Q1. -/
private lemma quadrantOf_Q1 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    quadrantOf x y = Quadrant.Q1 :=
  if_pos ⟨hx, hy⟩

/-- The quadrantOf falls to Q2 when x < 0 and y > 0. -/
private lemma quadrantOf_Q2 {x y : ℝ} (hx : x < 0) (hy : 0 < y) :
    quadrantOf x y = Quadrant.Q2 := by
  simp [quadrantOf, hx.not_gt, hx, hy]

/-- The quadrantOf falls to Q3 when x < 0 and y < 0. -/
private lemma quadrantOf_Q3 {x y : ℝ} (hx : x < 0) (hy : y < 0) :
    quadrantOf x y = Quadrant.Q3 := by
  simp [quadrantOf, hx.not_gt, hy.not_gt, hx, hy]

/-- The quadrantOf falls to Q4 when x > 0 and y < 0. -/
private lemma quadrantOf_Q4 {x y : ℝ} (hx : 0 < x) (hy : y < 0) :
    quadrantOf x y = Quadrant.Q4 := by
  have hxnlt : ¬x < 0 := not_lt.mpr hx.le
  simp [quadrantOf, hx, hy.not_gt, hxnlt, hy]

/-- The signed-sqrt map on `D` preserves the quadrant, provided the element's quadrant tag
equals the actual quadrant of its coordinates and both coordinates are nonzero.

The hypotheses are intentionally explicit:

* `hq` — the quadrant tag is faithful (no mismatch between `d.q` and the actual quadrant).
* `hx`, `hy` — both coordinates are nonzero (axes and the origin are excluded because
  `quadrantOf` assigns them to Q4 by its fallback branch, which may disagree with any
  intended tag for axis points).

Dropping these hypotheses would make the statement false in general. -/
theorem Dsqrt_quadrant_preserving (d : D)
    (hq : d.q = quadrantOf d.x d.y)
    (hx : d.x ≠ 0)
    (hy : d.y ≠ 0) :
    (Dsqrt d).q = d.q := by
  unfold Dsqrt
  simp only
  rw [hq]
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos
  · rcases lt_or_gt_of_ne hy with hy_neg | hy_pos
    · -- x < 0, y < 0 → Q3
      have hsx : Real.sign d.x * Real.sqrt |d.x| < 0 := signSqrt_neg hx_neg
      have hsy : Real.sign d.y * Real.sqrt |d.y| < 0 := signSqrt_neg hy_neg
      rw [quadrantOf_Q3 hx_neg hy_neg, quadrantOf_Q3 hsx hsy]
    · -- x < 0, y > 0 → Q2
      have hsx : Real.sign d.x * Real.sqrt |d.x| < 0 := signSqrt_neg hx_neg
      have hsy : 0 < Real.sign d.y * Real.sqrt |d.y| := signSqrt_pos hy_pos
      rw [quadrantOf_Q2 hx_neg hy_pos, quadrantOf_Q2 hsx hsy]
  · rcases lt_or_gt_of_ne hy with hy_neg | hy_pos
    · -- x > 0, y < 0 → Q4
      have hsx : 0 < Real.sign d.x * Real.sqrt |d.x| := signSqrt_pos hx_pos
      have hsy : Real.sign d.y * Real.sqrt |d.y| < 0 := signSqrt_neg hy_neg
      rw [quadrantOf_Q4 hx_pos hy_neg, quadrantOf_Q4 hsx hsy]
    · -- x > 0, y > 0 → Q1
      have hsx : 0 < Real.sign d.x * Real.sqrt |d.x| := signSqrt_pos hx_pos
      have hsy : 0 < Real.sign d.y * Real.sqrt |d.y| := signSqrt_pos hy_pos
      rw [quadrantOf_Q1 hx_pos hy_pos, quadrantOf_Q1 hsx hsy]

/-! ## D extensionality -/

/-- Two D elements are equal iff all three fields agree. -/
@[ext]
theorem D.ext {a b : D} (hx : a.x = b.x) (hy : a.y = b.y) (hq : a.q = b.q) : a = b := by
  cases a; cases b; simp_all

/-! ## Rot composition: Rot a (Rot b d) = Rot (a + b) d -/

/-- Rotation composition: applying `Rot b` then `Rot a` equals `Rot (a + b)`.
    This follows from the standard addition formulas for sin and cos. -/
theorem Rot_comp (a b : ℝ) (d : D) : Rot a (Rot b d) = Rot (a + b) d := by
  unfold Rot
  apply D.ext
  · -- x coordinates
    simp only
    rw [Real.cos_add, Real.sin_add]; ring
  · -- y coordinates
    simp only
    rw [Real.sin_add, Real.cos_add]; ring
  · -- quadrant tags: both sides are quadrantOf of the same expressions
    simp only
    congr 1
    · rw [Real.cos_add, Real.sin_add]; ring
    · rw [Real.sin_add, Real.cos_add]; ring

/-- Rotation by `(-a)` is the inverse of rotation by `a`, for elements whose
    quadrant tag matches `quadrantOf`. -/
theorem Rot_neg_cancel (a : ℝ) (d : D)
    (hq : d.q = quadrantOf d.x d.y) : Rot (-a) (Rot a d) = d := by
  rw [Rot_comp, neg_add_cancel]
  unfold Rot
  simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero, zero_add]
  exact D.ext rfl rfl hq.symm

/-- Rotation preserves the squared norm of the coordinate pair. -/
theorem Rot_preserves_norm_sq (a : ℝ) (d : D) :
    (Rot a d).x ^ 2 + (Rot a d).y ^ 2 = d.x ^ 2 + d.y ^ 2 := by
  simp only [Rot]
  have hc := Real.sin_sq_add_cos_sq a
  nlinarith [Real.sin_sq_add_cos_sq a, sq_nonneg d.x, sq_nonneg d.y,
             sq_nonneg (Real.sin a), sq_nonneg (Real.cos a)]

/-! ## Fold involution: Fold ph (Fold ph d) = d -/

/-- Fold is an involution for elements whose quadrant tag matches `quadrantOf`. -/
theorem Fold_involution (ph : ℝ) (d : D)
    (hq : d.q = quadrantOf d.x d.y) : Fold ph (Fold ph d) = d := by
  unfold Fold
  have c2 := Real.cos_sq_add_sin_sq (2 * ph)
  apply D.ext
  · simp only; linear_combination d.x * c2
  · simp only; linear_combination d.y * c2
  · simp only
    have hx : (d.x * Real.cos (2 * ph) + d.y * Real.sin (2 * ph)) * Real.cos (2 * ph) +
      (d.x * Real.sin (2 * ph) - d.y * Real.cos (2 * ph)) * Real.sin (2 * ph) = d.x := by
      linear_combination d.x * c2
    have hy : (d.x * Real.cos (2 * ph) + d.y * Real.sin (2 * ph)) * Real.sin (2 * ph) -
      (d.x * Real.sin (2 * ph) - d.y * Real.cos (2 * ph)) * Real.cos (2 * ph) = d.y := by
      linear_combination d.y * c2
    rw [hx, hy, hq]

/-- Fold preserves the squared norm of the coordinate pair. -/
theorem Fold_preserves_norm_sq (ph : ℝ) (d : D) :
    (Fold ph d).x ^ 2 + (Fold ph d).y ^ 2 = d.x ^ 2 + d.y ^ 2 := by
  simp only [Fold]
  nlinarith [Real.sin_sq_add_cos_sq (2 * ph), sq_nonneg d.x, sq_nonneg d.y,
             sq_nonneg (Real.sin (2 * ph)), sq_nonneg (Real.cos (2 * ph))]

/-! ## Rot and Fold on coordinates -/

/-- The x-coordinate of `Rot a d`. -/
@[simp] theorem Rot_x (a : ℝ) (d : D) :
    (Rot a d).x = d.x * Real.cos a - d.y * Real.sin a := rfl

/-- The y-coordinate of `Rot a d`. -/
@[simp] theorem Rot_y (a : ℝ) (d : D) :
    (Rot a d).y = d.x * Real.sin a + d.y * Real.cos a := rfl

/-- The x-coordinate of `Fold ph d`. -/
@[simp] theorem Fold_x (ph : ℝ) (d : D) :
    (Fold ph d).x = d.x * Real.cos (2 * ph) + d.y * Real.sin (2 * ph) := rfl

/-- The y-coordinate of `Fold ph d`. -/
@[simp] theorem Fold_y (ph : ℝ) (d : D) :
    (Fold ph d).y = d.x * Real.sin (2 * ph) - d.y * Real.cos (2 * ph) := rfl

/-! ## Rotation by 2π and π/2 -/

/-- Rotation by 2π is the identity (on well-tagged elements). -/
theorem Rot_two_pi (d : D) (hq : d.q = quadrantOf d.x d.y) :
    Rot (2 * Real.pi) d = d := by
  unfold Rot
  simp only [Real.cos_two_pi, Real.sin_two_pi, mul_one, mul_zero, sub_zero, zero_add]
  exact D.ext rfl rfl hq.symm

/-- Rotation by π negates both coordinates. -/
theorem Rot_pi_x (d : D) : (Rot Real.pi d).x = -d.x := by
  simp [Rot, Real.cos_pi, Real.sin_pi]

theorem Rot_pi_y (d : D) : (Rot Real.pi d).y = -d.y := by
  simp [Rot, Real.cos_pi, Real.sin_pi]

/-- Rotation by π/2 swaps and negates: x ↦ -y, y ↦ x. -/
theorem Rot_pi_half_x (d : D) : (Rot (Real.pi / 2) d).x = -d.y := by
  simp [Rot, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem Rot_pi_half_y (d : D) : (Rot (Real.pi / 2) d).y = d.x := by
  simp [Rot, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-! ## Dsqrt coordinate properties -/

/-- The squared x-coordinate of `Dsqrt d` equals `|d.x|`. -/
theorem Dsqrt_x_sq (d : D) :
    (Dsqrt d).x ^ 2 = |d.x| := by
  simp only [Dsqrt]
  rcases lt_trichotomy d.x 0 with hx | hx | hx
  · simp [Real.sign_of_neg hx, abs_of_neg hx, Real.sq_sqrt (neg_nonneg.mpr hx.le)]
  · simp [hx, Real.sign_zero]
  · simp [Real.sign_of_pos hx, abs_of_pos hx, Real.sq_sqrt hx.le]

/-- The squared y-coordinate of `Dsqrt d` equals `|d.y|`. -/
theorem Dsqrt_y_sq (d : D) :
    (Dsqrt d).y ^ 2 = |d.y| := by
  simp only [Dsqrt]
  rcases lt_trichotomy d.y 0 with hy | hy | hy
  · simp [Real.sign_of_neg hy, abs_of_neg hy, Real.sq_sqrt (neg_nonneg.mpr hy.le)]
  · simp [hy, Real.sign_zero]
  · simp [Real.sign_of_pos hy, abs_of_pos hy, Real.sq_sqrt hy.le]
