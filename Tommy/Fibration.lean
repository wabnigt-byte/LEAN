import Tommy.Torus
import Tommy.Closure
import Tommy.Skeleton

/-!
# Torus Fibration Setup (Claim 2.4 / Theorem 5)

We define the projection map from the Farey torus to S¹, the fibres over each
direction, and the notion of a rational direction.

## Main definitions

* `torus_proj` — the projection `FareyTorus → ↥S1`, defined via `Quotient.lift`
  from the cylinder's first-coordinate projection `fun c => c.1`.
* `Fibre θ` — the preimage `{ p | torus_proj p = θ }` in `FareyTorus`.
* `IsRationalDirection θ` — there exists a nonzero integer pair whose `phi`-image
  equals `θ` (as a point of `ℝ × ℝ`).

## Scope

Only the type-level setup is formalised here (Category A for these three
definitions and the surjectivity/nonemptiness lemmas below).
Fibre homeomorphism types, fibre classification, probability
measures, integrals, density, and any continuity/topology of `torus_proj`
remain **not attempted** (Category D).
-/

open Set Real

/-! ## Compatibility of the cylinder projection with `farey_rel` -/

/-- The first-coordinate projection `fun c => c.1` is invariant on `farey_rel`-classes:
    if `farey_rel a b` then `a.1 = b.1`. -/
lemma farey_rel_proj_compat : ∀ (a b : Cylinder), farey_rel a b → a.1 = b.1 := by
  intro a b hab
  rcases hab with rfl | ⟨hdir, _⟩
  · rfl
  · exact hdir

/-! ## The torus projection -/

/-- The projection `torus_proj : FareyTorus → ↥S1` sends each equivalence class
    `[c]` to the direction `c.1 ∈ S¹`.

    Well-definedness: `farey_rel_proj_compat` proves that `farey_rel`-related
    points have the same first coordinate, so `Quotient.lift` applies. -/
def torus_proj : FareyTorus → ↥S1 :=
  Quotient.lift (fun (c : Cylinder) => c.1) farey_rel_proj_compat

/-! ## Fibres -/

/-- The **fibre** over a direction `θ ∈ S¹` is the set of torus points that
    project to `θ`. -/
def Fibre (θ : ↥S1) : Set FareyTorus := { p | torus_proj p = θ }

/-! ## Rational directions -/

/-- A direction `θ ∈ S¹` is **rational** if it is the `phi`-image of some nonzero
    integer vector: i.e. there exists `(p, q) ∈ ℤ × ℤ` with `(p, q) ≠ (0, 0)`
    and `phi ((p : ℝ), (q : ℝ)) = (θ : ℝ × ℝ)`. -/
def IsRationalDirection (θ : ↥S1) : Prop :=
  ∃ (p : ℤ × ℤ), p ≠ (0, 0) ∧ phi ((p.1 : ℝ), (p.2 : ℝ)) = (θ : ℝ × ℝ)

/-! ## Surjectivity of torus_proj -/

/-- `torus_proj` is surjective: every direction `θ ∈ S¹` is the projection of some
    torus point (namely, the class of `(θ, 0)` in the cylinder). -/
theorem torus_proj_surjective : Function.Surjective torus_proj := by
  intro θ
  use Quotient.mk fareySetoid (θ, ⟨(0 : ℝ), le_refl 0, le_of_lt one_pos⟩)
  rfl

/-- Every fibre is nonempty. -/
theorem fibre_nonempty (θ : ↥S1) : (Fibre θ).Nonempty := by
  obtain ⟨p, hp⟩ := torus_proj_surjective θ
  exact ⟨p, hp⟩

/-! ## Skeleton-fibre compatibility -/

open ThomaeSkeleton in
/-- The torus projection of a skeleton embedding equals the direction. -/
theorem torus_proj_of_thomae
    (p : {p : ℤ × ℤ // p ≠ (0, 0)}) :
    torus_proj (thomae_torus_embedding p) =
      (thomae_cylinder_embedding p).1 := by
  simp only [thomae_torus_embedding, torus_proj]
  rfl
