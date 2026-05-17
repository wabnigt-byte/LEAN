import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Card

/-- The four quadrants of the plane. -/
inductive Quadrant
| Q1 | Q2 | Q3 | Q4
deriving DecidableEq, Repr

/-- The directional plane D, bundling a point in ℝ² with its quadrant tag. -/
structure D where
  x : ℝ
  y : ℝ
  q : Quadrant

/-- Helper to compute the quadrant from coordinates. -/
noncomputable def quadrantOf (x y : ℝ) : Quadrant :=
  if x > 0 ∧ y > 0 then Quadrant.Q1
  else if x < 0 ∧ y > 0 then Quadrant.Q2
  else if x < 0 ∧ y < 0 then Quadrant.Q3
  else Quadrant.Q4

/-- Addition in D explicitly computes the quadrant tag from the resulting coordinates. -/
noncomputable def D.add (a b : D) : D :=
  ⟨a.x + b.x, a.y + b.y, quadrantOf (a.x + b.x) (a.y + b.y)⟩

/-- Guardrail: Addition preserves the quadrant tag when both summands lie strictly inside the same quadrant. -/
lemma add_preserves_quadrant (a b : D) (ha : a.x > 0 ∧ a.y > 0) (hb : b.x > 0 ∧ b.y > 0) :
    (D.add a b).q = Quadrant.Q1 := by
  -- Unfold the addition definition.
  unfold D.add
  -- Unfold the quadrantOf helper.
  unfold quadrantOf
  -- The sum of positive coordinates is positive.
  have hx : a.x + b.x > 0 := add_pos ha.1 hb.1
  have hy : a.y + b.y > 0 := add_pos ha.2 hb.2
  -- Simplify the if-then-else.
  simp [hx, hy]

/-- The Klein-four group K acting by sign flips. -/
inductive K
| id | flipX | flipY | flipXY
deriving DecidableEq, Repr

/-- Action of K on D. -/
def K.act (k : K) (d : D) : D :=
  match k with
  | id => d
  | flipX => ⟨-d.x, d.y, match d.q with | .Q1 => .Q2 | .Q2 => .Q1 | .Q3 => .Q4 | .Q4 => .Q3⟩
  | flipY => ⟨d.x, -d.y, match d.q with | .Q1 => .Q4 | .Q2 => .Q3 | .Q3 => .Q2 | .Q4 => .Q1⟩
  | flipXY => ⟨-d.x, -d.y, match d.q with | .Q1 => .Q3 | .Q2 => .Q4 | .Q3 => .Q1 | .Q4 => .Q2⟩

/-- Guardrail: The Klein-four action moves points between quadrants. -/
lemma k_action_moves_quadrants (d : D) (hd : d.q = Quadrant.Q1) : (K.act K.flipX d).q = Quadrant.Q2 := by
  -- Unfold the action definition
  unfold K.act
  -- Rewrite the quadrant tag
  rw [hd]

/-- Multiplication in K. -/
def K.mul (k1 k2 : K) : K :=
  match k1, k2 with
  | id, k => k
  | k, id => k
  | flipX, flipX => id
  | flipY, flipY => id
  | flipXY, flipXY => id
  | flipX, flipY => flipXY
  | flipY, flipX => flipXY
  | flipX, flipXY => flipY
  | flipXY, flipX => flipY
  | flipY, flipXY => flipX
  | flipXY, flipY => flipX

/-- The action of K on D is compatible with multiplication. -/
lemma k_act_mul (k1 k2 : K) (d : D) : K.act k1 (K.act k2 d) = K.act (K.mul k1 k2) d := by
  cases k1 <;> cases k2 <;> cases d <;> rename_i x y q <;> cases q <;>
    simp [K.act, K.mul]

/-- The relation induced by the action of K is an equivalence relation. -/
theorem k_act_equiv : Equivalence (fun a b => ∃ k : K, K.act k a = b) := by
  constructor
  · intro x
    use K.id
    rfl
  · intro x y h
    rcases h with ⟨k, hk⟩
    use k
    rw [← hk]
    have h_inv : K.mul k k = K.id := by cases k <;> rfl
    rw [k_act_mul, h_inv]
    rfl
  · intro x y z h1 h2
    rcases h1 with ⟨k1, hk1⟩
    rcases h2 with ⟨k2, hk2⟩
    use K.mul k2 k1
    rw [← hk2, ← hk1, k_act_mul]

/-- The quotient C = D / K. -/
def C := Quotient (Setoid.mk (fun a b => ∃ k : K, K.act k a = b) k_act_equiv)

/-!
## Coordinate payload CommRing and D_Q1 blocker analysis

The paper claims a single fixed quadrant (Q1) carries a commutative ring while sharing the
global zero. We analyse this claim against the existing open-quadrant/tag semantics of `D`.

### What works: the coordinate payload ℝ × ℝ carries CommRing

Every `D`-element has an underlying coordinate pair `(x, y) : ℝ × ℝ`. The type `ℝ × ℝ` already
carries a full `CommRing` structure in Mathlib, with
  - zero  = (0, 0)
  - one   = (1, 1)
  - add   = pointwise
  - mul   = pointwise
  - neg   = pointwise negation
This is the canonical "honest" ring living inside D.

### Why `CommRing D_Q1` is impossible under open-quadrant semantics (Blocker)

Define `D_Q1 := { d : D // d.q = Quadrant.Q1 }`. The open first quadrant is
  Q1 = { (x, y) : ℝ × ℝ | x > 0 ∧ y > 0 }.

For `D_Q1` to be a `CommRing` (or even an `AddGroup`), we need:
  1. **Zero** — an element `0 : D_Q1` satisfying `0 + a = a` for all `a : D_Q1`.
     The only additive identity in ℝ × ℝ is `(0, 0)`, but `(0, 0)` is not in Q1
     (`quadrantOf 0 0 = Q4` by the fallback branch). So there is no zero element in D_Q1.
  2. **Additive inverses** — for each `a : D_Q1`, we need `-a : D_Q1`. But if `a = (x, y)`
     with `x > 0` and `y > 0`, then `-a = (-x, -y)` has `quadrantOf (-x) (-y) = Q3 ≠ Q1`.
     Thus negation takes Q1 elements to Q3, not back to Q1.

Conclusion: `D_Q1` with the global `D.add` and coordinate-derived `neg` is not an `AddGroup`,
hence not a `CommRing`. The ring structure lives on the coordinate payload `ℝ × ℝ`, not on
the tagged subtype.
-/

/-! ## Coordinate map and CommRing on the D payload -/

/-- The coordinate projection from D to ℝ × ℝ, discarding the quadrant tag. -/
def D.toCoords (d : D) : ℝ × ℝ := (d.x, d.y)

/-- The coordinate map is surjective (any (x,y) arises from some D element). -/
lemma D_toCoords_surjective : Function.Surjective D.toCoords :=
  fun ⟨x, y⟩ => ⟨⟨x, y, Quadrant.Q1⟩, rfl⟩

/-- The coordinate payload ℝ × ℝ carries a commutative ring structure.
    This is the correct algebraic structure associated to the D substrate:
    operations are pointwise on coordinates, zero is (0,0), one is (1,1). -/
example : CommRing (ℝ × ℝ) := inferInstance

/-! ## D_Q1 subtype and its add-closure (positive cone) -/

/-- The Q1 subtype: elements of D whose quadrant tag is Q1. -/
def D_Q1 := { d : D // d.q = Quadrant.Q1 }

/-- Q1 is closed under D.add: adding two strictly-positive elements stays in Q1. -/
lemma D_Q1_add_closed (a b : D) (ha : a.x > 0 ∧ a.y > 0) (hb : b.x > 0 ∧ b.y > 0)
    (_haq : a.q = Quadrant.Q1) (_hbq : b.q = Quadrant.Q1) :
    (D.add a b).q = Quadrant.Q1 :=
  add_preserves_quadrant a b ha hb

/-- Blocker: the global additive zero (0,0) has quadrant tag Q4, not Q1.
    Therefore D_Q1 cannot contain a zero element (as required by any AddMonoid/Ring). -/
lemma D_zero_not_Q1 : quadrantOf 0 0 ≠ Quadrant.Q1 := by
  unfold quadrantOf
  simp

/-- Blocker: if (x, y) is strictly in Q1 (x > 0, y > 0), then its coordinate negation
    (-x, -y) lies in Q3, not Q1. Hence D_Q1 cannot have additive inverses. -/
lemma D_Q1_neg_leaves_Q1 (x y : ℝ) (hx : x > 0) (hy : y > 0) :
    quadrantOf (-x) (-y) = Quadrant.Q3 := by
  have hx3 : -x < 0 := by linarith
  have hy3 : -y < 0 := by linarith
  simp [quadrantOf, hx3.not_gt, hy3.not_gt, hx3, hy3]

/-! ## CommGroup instance for K (Klein-four group) -/

/-- One instance: the identity element of K. -/
instance : One K := ⟨K.id⟩

/-- Mul instance: multiplication in K. -/
instance : Mul K := ⟨K.mul⟩

/-- Inv instance: every element of K is self-inverse. -/
instance : Inv K := ⟨fun k => k⟩

/-- Associativity of K.mul, proved by exhaustive case analysis on all 64 triples. -/
lemma K.mul_assoc (a b c : K) : K.mul (K.mul a b) c = K.mul a (K.mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Left identity in K. -/
lemma K.one_mul (a : K) : K.mul K.id a = a := by
  cases a <;> rfl

/-- Right identity in K. -/
lemma K.mul_one (a : K) : K.mul a K.id = a := by
  cases a <;> rfl

/-- Every element is self-inverse: k * k = id. -/
lemma K.inv_mul_cancel (a : K) : K.mul a a = K.id := by
  cases a <;> rfl

/-- Commutativity of K.mul. -/
lemma K.mul_comm (a b : K) : K.mul a b = K.mul b a := by
  cases a <;> cases b <;> rfl

/-- The full CommGroup instance for the Klein-four group K. -/
instance K.instCommGroup : CommGroup K where
  mul a b       := K.mul a b
  mul_assoc a b c := K.mul_assoc a b c
  one           := K.id
  one_mul a     := K.one_mul a
  mul_one a     := K.mul_one a
  inv a         := a
  inv_mul_cancel a := K.inv_mul_cancel a
  mul_comm a b  := K.mul_comm a b

/-- K has exactly four elements. -/
instance K.instFintype : Fintype K where
  elems := {K.id, K.flipX, K.flipY, K.flipXY}
  complete := fun k => by cases k <;> simp

/-- K has cardinality 4. -/
theorem K.card_eq : Fintype.card K = 4 := by decide

/-- K acts on D via sign flips: this is a group action (MulAction). -/
instance K.instMulActionD : MulAction K D where
  smul k d := K.act k d
  one_smul _ := rfl
  mul_smul k1 k2 d := (k_act_mul k1 k2 d).symm
