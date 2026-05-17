import Tommy.Thomae
import Mathlib.Data.Real.Basic

/-!
# The Hi-Hat Solid — Graph of the Thomae Projection as a Surface of Revolution

The *hi-hat* is the graph of the Thomae projection `τ` over the integer lattice ℤ²,
embedded in ℝ³. Its symmetry under all four quadrant sign flips makes it a
*solid of revolution* (invariant under 90° rotations and reflections), analogous to
a bell curve rotated around the vertical axis.

## Definitions

- `hiHatGraph`: the graph {((a:ℝ), (b:ℝ), (τ(a,b):ℝ)) : a b : ℤ} in ℝ³.
- `hiHatRevSurface`: definitionally equal to `hiHatGraph` (the "surface of revolution" label).
- `hiHatVisibleSpikes`: the height-1 slice, corresponding to visible lattice points.

## Theorems

- `hiHat_flipX_invariant`: invariant under (x,y,z) ↦ (-x,y,z).
- `hiHat_flipY_invariant`: invariant under (x,y,z) ↦ (x,-y,z).
- `hiHat_neg_invariant`: invariant under (x,y,z) ↦ (-x,-y,z).
- `hiHat_sign_invariant`: invariant under all four sign combinations.
- `hiHat_symm`: invariant under (x,y,z) ↦ (y,x,z).
- `mem_hiHatVisibleSpikes_iff`: height-1 spikes ↔ visible lattice points.
-/

/-- The hi-hat graph: all triples ((a:ℝ), (b:ℝ), (τ(a,b):ℝ)) for integer pairs (a,b). -/
def hiHatGraph : Set (ℝ × ℝ × ℝ) :=
  {v : ℝ × ℝ × ℝ | ∃ (a b : ℤ), v = ((a : ℝ), (b : ℝ), (tau (a, b) : ℝ))}

/-- Membership in hiHatGraph. -/
@[simp]
lemma mem_hiHatGraph_iff (v : ℝ × ℝ × ℝ) :
    v ∈ hiHatGraph ↔ ∃ (a b : ℤ), v = ((a : ℝ), (b : ℝ), (tau (a, b) : ℝ)) :=
  Iff.rfl

/-! ## Symmetry theorems -/

/-- The hi-hat graph is invariant under sign flip in the first coordinate. -/
theorem hiHat_flipX_invariant :
    ∀ v ∈ hiHatGraph, (-v.1, v.2.1, v.2.2) ∈ hiHatGraph := by
  rintro v ⟨a, b, rfl⟩
  exact ⟨-a, b, by simp [tau_invariant_flipX]⟩

/-- The hi-hat graph is invariant under sign flip in the second coordinate. -/
theorem hiHat_flipY_invariant :
    ∀ v ∈ hiHatGraph, (v.1, -v.2.1, v.2.2) ∈ hiHatGraph := by
  rintro v ⟨a, b, rfl⟩
  exact ⟨a, -b, by simp [tau_invariant_flipY]⟩

/-- The hi-hat graph is invariant under negating both coordinates. -/
theorem hiHat_neg_invariant :
    ∀ v ∈ hiHatGraph, (-v.1, -v.2.1, v.2.2) ∈ hiHatGraph := by
  rintro v ⟨a, b, rfl⟩
  exact ⟨-a, -b, by simp [tau_invariant_neg]⟩

/-- The hi-hat graph is invariant under all four sign-flip combinations. -/
theorem hiHat_sign_invariant (v : ℝ × ℝ × ℝ) (hv : v ∈ hiHatGraph) (sx sy : Bool) :
    ((if sx then -v.1 else v.1), (if sy then -v.2.1 else v.2.1), v.2.2) ∈ hiHatGraph := by
  cases sx
  · -- sx = false
    cases sy
    · exact hv  -- (false, false) = identity
    · -- (false, true) = flipY
      have := hiHat_flipY_invariant v hv
      simpa using this
  · -- sx = true
    cases sy
    · -- (true, false) = flipX
      have := hiHat_flipX_invariant v hv
      simpa using this
    · -- (true, true) = neg both
      exact hiHat_neg_invariant v hv

/-- The hi-hat graph is symmetric under swapping x and y coordinates. -/
theorem hiHat_symm :
    ∀ v ∈ hiHatGraph, (v.2.1, v.1, v.2.2) ∈ hiHatGraph := by
  rintro v ⟨a, b, rfl⟩
  exact ⟨b, a, by simp [tau_symm]⟩

/-! ## Surface of revolution formulation -/

/-- The hi-hat as a surface of revolution equals the hi-hat graph (by definition).
    The "revolution" is witnessed by the four-fold symmetry theorems above. -/
def hiHatRevSurface : Set (ℝ × ℝ × ℝ) := hiHatGraph

@[simp]
lemma hiHatRevSurface_eq : hiHatRevSurface = hiHatGraph := rfl

/-! ## Visible spikes -/

/-- The visible spikes of the hi-hat: points in hiHatGraph at height 1. -/
def hiHatVisibleSpikes : Set (ℝ × ℝ × ℝ) :=
  {v ∈ hiHatGraph | v.2.2 = 1}

/-- A point (a, b, 1) is a visible spike iff (a, b) is a visible lattice point. -/
theorem mem_hiHatVisibleSpikes_iff (a b : ℤ) :
    ((a : ℝ), (b : ℝ), (1 : ℝ)) ∈ hiHatVisibleSpikes ↔
    (a, b) ∈ (visibleLattice : Set (ℤ × ℤ)) := by
  simp only [hiHatVisibleSpikes, hiHatGraph, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨a', b', heq⟩, _⟩
    have h1 : (a : ℝ) = a' := congr_arg Prod.fst heq
    have h2 : (b : ℝ) = b' := congr_arg Prod.fst (congr_arg Prod.snd heq)
    have h3 : (1 : ℝ) = (tau (a', b') : ℚ) := congr_arg Prod.snd (congr_arg Prod.snd heq)
    have ha' : a' = a := by exact_mod_cast h1.symm
    have hb' : b' = b := by exact_mod_cast h2.symm
    -- Rewrite a', b' as a, b in h3
    rw [ha', hb'] at h3
    have htau : tau (a, b) = 1 := by exact_mod_cast h3.symm
    have hne : (a, b) ≠ ((0 : ℤ), (0 : ℤ)) := by intro heq0; simp [heq0] at htau
    rwa [tau_eq_one_iff_visible hne] at htau
  · intro hvis
    have hne : (a, b) ≠ ((0 : ℤ), (0 : ℤ)) := hvis.1
    have htau : tau (a, b) = 1 := (tau_eq_one_iff_visible hne).mpr hvis
    exact ⟨⟨a, b, by simp [htau]⟩, by simp⟩
