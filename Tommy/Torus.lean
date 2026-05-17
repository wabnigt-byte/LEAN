import Tommy.Closure
import Mathlib.Data.Real.Basic

/-!
# Farey Torus Quotient (Claim 1.5)

We define the **Farey torus** as a quotient of the cylinder `S¹ × [0,1]` by the
Farey boundary identification: for each direction θ ∈ S¹, the bottom endpoint
`(θ, 0)` is identified with the top endpoint `(θ, 1)`.

## Main definitions

* `Cylinder` — the product `S1 × Set.Icc (0 : ℝ) 1`.
* `farey_rel` — the identification relation: two points are related iff they are
  equal, or they share the same direction and their heights are `{0, 1}`.
* `farey_rel_is_equiv` — `farey_rel` is an equivalence relation.
* `fareySetoid` — the corresponding `Setoid Cylinder`.
* `FareyTorus` — the quotient `Quotient fareySetoid`.

## Scope

Only the setoid and quotient type are formalised here (Category A).
Topology (homeomorphism with S¹ × S¹, continuity of the quotient map, etc.)
is not attempted and remains Category D.
-/

open Set Real

/-- The cylinder: the unit circle crossed with the unit interval [0, 1].
    Points are pairs `(θ, h)` where `θ ∈ S1` and `h ∈ [0, 1]`. -/
abbrev Cylinder := S1 × Set.Icc (0 : ℝ) 1

/-- The Farey boundary identification on the cylinder.

    Two points `p q : Cylinder` are related iff:
    * they are equal, **or**
    * they have the same direction (`p.1 = q.1`) and their heights are the two
      endpoints in some order (`{p.2.1, q.2.1} = {0, 1}`), i.e. one height is 0
      and the other is 1.

    This glues the bottom circle `S¹ × {0}` to the top circle `S¹ × {1}` pointwise,
    turning the cylinder into the torus. -/
def farey_rel (p q : Cylinder) : Prop :=
  p = q ∨
  (p.1 = q.1 ∧
   ((p.2.1 = 0 ∧ q.2.1 = 1) ∨ (p.2.1 = 1 ∧ q.2.1 = 0)))

/-- `farey_rel` is an equivalence relation. -/
theorem farey_rel_is_equiv : Equivalence farey_rel := by
  constructor
  · -- Reflexivity: p ~ p via the left disjunct.
    intro p
    exact Or.inl rfl
  · -- Symmetry: swap the two disjuncts.
    intro p q hpq
    rcases hpq with rfl | ⟨hdir, hends⟩
    · exact Or.inl rfl
    · rcases hends with ⟨hp0, hq1⟩ | ⟨hp1, hq0⟩
      · exact Or.inr ⟨hdir.symm, Or.inr ⟨hq1, hp0⟩⟩
      · exact Or.inr ⟨hdir.symm, Or.inl ⟨hq0, hp1⟩⟩
  · -- Transitivity: case split on which disjuncts hold for p~q and q~r.
    intro p q r hpq hqr
    rcases hpq with rfl | ⟨hpq_dir, hpq_ends⟩
    · exact hqr
    · rcases hqr with rfl | ⟨hqr_dir, hqr_ends⟩
      · exact Or.inr ⟨hpq_dir, hpq_ends⟩
      · -- p.1 = q.1 = r.1, and we need to check heights.
        -- p and q have endpoint heights in {0,1}; q and r have endpoint heights in {0,1}.
        -- If q.2.1 = 0, then from hpq_ends: p.2.1 = 1.
        --   From hqr_ends: r.2.1 = 1. So p.2.1 = 1 = r.2.1, and directions equal → equal.
        -- If q.2.1 = 1, then from hpq_ends: p.2.1 = 0.
        --   From hqr_ends: r.2.1 = 0. So p.2.1 = 0 = r.2.1, and directions equal → equal.
        have hdir : p.1 = r.1 := hpq_dir.trans hqr_dir
        rcases hpq_ends with ⟨hp0, hq1⟩ | ⟨hp1, hq0⟩
        · -- p.2.1 = 0, q.2.1 = 1
          rcases hqr_ends with ⟨hq0', _⟩ | ⟨hq1', hr0⟩
          · -- q.2.1 = 0, but we know q.2.1 = 1: contradiction
            exfalso; linarith [hq1.symm.trans hq0']
          · -- q.2.1 = 1, r.2.1 = 0
            -- p.2.1 = 0, r.2.1 = 0, directions equal → p = r
            -- We need p.2 = r.2 as subtypes of Icc 0 1
            have h2eq : p.2 = r.2 := by
              ext
              simp only [hp0, hr0]
            exact Or.inl (Prod.ext hdir h2eq)
        · -- p.2.1 = 1, q.2.1 = 0
          rcases hqr_ends with ⟨hq0', hr1⟩ | ⟨hq1', _⟩
          · -- q.2.1 = 0, r.2.1 = 1
            -- p.2.1 = 1, r.2.1 = 1, directions equal → p = r
            have h2eq : p.2 = r.2 := by
              ext
              simp only [hp1, hr1]
            exact Or.inl (Prod.ext hdir h2eq)
          · -- q.2.1 = 1, but we know q.2.1 = 0: contradiction
            exfalso; linarith [hq0.symm.trans hq1']

/-- The Farey setoid on the cylinder. -/
def fareySetoid : Setoid Cylinder :=
  ⟨farey_rel, farey_rel_is_equiv⟩

/-- The **Farey torus**: the cylinder `S¹ × [0,1]` with its top and bottom
    circles identified pointwise by `fareySetoid`. -/
def FareyTorus := Quotient fareySetoid
