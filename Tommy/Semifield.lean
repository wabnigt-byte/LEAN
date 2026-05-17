import Tommy.DMaps
import Mathlib.Algebra.Order.Field.Basic

/-!
# DQ1Zero: the carrier for the first-quadrant-plus-zero semifield (v11 §26b)

This file defines the type `DQ1Zero` whose elements are pairs `(x, y) : ℝ × ℝ`
satisfying `(x > 0 ∧ y > 0) ∨ (x = 0 ∧ y = 0)`, together with `Zero`, `One`,
`Add`, and `Mul` instances.  Algebraic typeclass proofs (CommSemiring, etc.) are
deferred to Session 15.
-/

/-- A real pair that is either strictly positive (Q1) or the origin. -/
structure DQ1Zero where
  x : ℝ
  y : ℝ
  valid : (x > 0 ∧ y > 0) ∨ (x = 0 ∧ y = 0)

namespace DQ1Zero

-- ── basic instances ──────────────────────────────────────────────────────────

instance : Zero DQ1Zero := ⟨⟨0, 0, Or.inr ⟨rfl, rfl⟩⟩⟩

instance : One DQ1Zero := ⟨⟨1, 1, Or.inl ⟨one_pos, one_pos⟩⟩⟩

instance : Add DQ1Zero where
  add a b :=
    { x     := a.x + b.x
      y     := a.y + b.y
      valid := by
        rcases a.valid with ⟨hax, hay⟩ | ⟨hax, hay⟩ <;>
        rcases b.valid with ⟨hbx, hby⟩ | ⟨hbx, hby⟩
        · exact Or.inl ⟨add_pos hax hbx, add_pos hay hby⟩
        · simp [hbx, hby]; exact Or.inl ⟨hax, hay⟩
        · simp [hax, hay]; exact Or.inl ⟨hbx, hby⟩
        · simp [hax, hay, hbx, hby] }

instance : Mul DQ1Zero where
  mul a b :=
    { x     := a.x * b.x
      y     := a.y * b.y
      valid := by
        rcases a.valid with ⟨hax, hay⟩ | ⟨hax, hay⟩ <;>
        rcases b.valid with ⟨hbx, hby⟩ | ⟨hbx, hby⟩
        · exact Or.inl ⟨mul_pos hax hbx, mul_pos hay hby⟩
        · simp [hbx, hby]
        · simp [hax, hay]
        · simp [hax, hay] }

-- ── sanity lemmas ─────────────────────────────────────────────────────────────

@[simp] theorem zero_x : (0 : DQ1Zero).x = 0 := rfl
@[simp] theorem zero_y : (0 : DQ1Zero).y = 0 := rfl
@[simp] theorem one_x  : (1 : DQ1Zero).x = 1 := rfl
@[simp] theorem one_y  : (1 : DQ1Zero).y = 1 := rfl

theorem add_coords (a b : DQ1Zero) :
    (a + b).x = a.x + b.x ∧ (a + b).y = a.y + b.y :=
  ⟨rfl, rfl⟩

-- ── ext lemma and mul_coords ──────────────────────────────────────────────────

@[ext]
theorem ext {a b : DQ1Zero} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a; cases b; simp_all

-- Note: @[ext] auto-generates DQ1Zero.ext_iff; we expose it as eq_iff
theorem eq_iff {a b : DQ1Zero} : a = b ↔ a.x = b.x ∧ a.y = b.y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨hx, hy⟩ => ext hx hy⟩

theorem mul_coords (a b : DQ1Zero) :
    (a * b).x = a.x * b.x ∧ (a * b).y = a.y * b.y :=
  ⟨rfl, rfl⟩

-- ── coordinate-unfolding simp lemmas (used inside CommSemiring proofs) ──────────

@[simp] theorem add_x (a b : DQ1Zero) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : DQ1Zero) : (a + b).y = a.y + b.y := rfl
@[simp] theorem mul_x (a b : DQ1Zero) : (a * b).x = a.x * b.x := rfl
@[simp] theorem mul_y (a b : DQ1Zero) : (a * b).y = a.y * b.y := rfl

-- ── CommSemiring instance ─────────────────────────────────────────────────────

instance : CommSemiring DQ1Zero where
  -- AddCommMonoid fields
  add_assoc a b c     := by ext <;> simp <;> ring
  zero_add a          := by ext <;> simp
  add_zero a          := by ext <;> simp
  add_comm a b        := by ext <;> simp <;> ring
  nsmul               := nsmulRec
  -- Monoid fields
  mul_assoc a b c     := by ext <;> simp <;> ring
  one_mul a           := by ext <;> simp
  mul_one a           := by ext <;> simp
  npow                := npowRec
  -- Semiring fields
  left_distrib a b c  := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a          := by ext <;> simp
  mul_zero a          := by ext <;> simp
  -- CommSemiring field
  mul_comm a b        := by ext <;> simp <;> ring

-- ── Inv instance ────────────────────────────────────────────────────────────

noncomputable instance : Inv DQ1Zero where
  inv a :=
    if h : (a.x > 0 ∧ a.y > 0) then
      { x     := 1 / a.x
        y     := 1 / a.y
        valid := Or.inl ⟨one_div_pos.mpr h.1, one_div_pos.mpr h.2⟩ }
    else
      0

@[simp] theorem inv_x (a : DQ1Zero) :
    a⁻¹.x = if (a.x > 0 ∧ a.y > 0) then 1 / a.x else 0 := by
  simp only [Inv.inv]
  split_ifs <;> rfl

@[simp] theorem inv_y (a : DQ1Zero) :
    a⁻¹.y = if (a.x > 0 ∧ a.y > 0) then 1 / a.y else 0 := by
  simp only [Inv.inv]
  split_ifs <;> rfl

-- ── standalone inverse lemmas ─────────────────────────────────────────────────

theorem mul_inv_cancel (a : DQ1Zero) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  have hv : a.x > 0 ∧ a.y > 0 := by
    rcases a.valid with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨hx, hy⟩
    · exfalso; apply h; ext <;> simp_all
  ext
  · -- goal: (a * a⁻¹).x = (1 : DQ1Zero).x
    simp only [mul_x, inv_x, one_x, if_pos hv]
    exact mul_one_div_cancel (ne_of_gt hv.1)
  · simp only [mul_y, inv_y, one_y, if_pos hv]
    exact mul_one_div_cancel (ne_of_gt hv.2)

theorem inv_zero : (0 : DQ1Zero)⁻¹ = 0 := by
  ext
  · simp only [inv_x, zero_x, zero_y, if_neg (by norm_num : ¬((0 : ℝ) > 0 ∧ (0 : ℝ) > 0))]
  · simp only [inv_y, zero_x, zero_y, if_neg (by norm_num : ¬((0 : ℝ) > 0 ∧ (0 : ℝ) > 0))]

-- ── Semifield (= CommSemifield in Mathlib v4) instance ──────────────────────
-- Semifield extends CommSemiring + CommGroupWithZero. We build CommGroupWithZero
-- first (it needs Nontrivial, Inv, mul_inv_cancel, inv_zero, commutativity, ...),
-- then hand it together with the existing CommSemiring to Semifield.

noncomputable instance : Nontrivial DQ1Zero :=
  ⟨⟨1, 0, by intro h; have := congr_arg DQ1Zero.x h; simp at this⟩⟩

noncomputable instance : CommGroupWithZero DQ1Zero where
  -- CommMonoidWithZero (from CommSemiring already proved)
  mul_comm   := (inferInstance : CommSemiring DQ1Zero).mul_comm
  mul_assoc  := (inferInstance : CommSemiring DQ1Zero).mul_assoc
  mul_one    := (inferInstance : CommSemiring DQ1Zero).mul_one
  one_mul    := (inferInstance : CommSemiring DQ1Zero).one_mul
  npow       := (inferInstance : CommSemiring DQ1Zero).npow
  zero_mul   := (inferInstance : CommSemiring DQ1Zero).zero_mul
  mul_zero   := (inferInstance : CommSemiring DQ1Zero).mul_zero
  -- Nontrivial
  exists_pair_ne := (inferInstance : Nontrivial DQ1Zero).exists_pair_ne
  -- GroupWithZero inverse axioms
  inv_zero   := DQ1Zero.inv_zero
  mul_inv_cancel := fun a ha => DQ1Zero.mul_inv_cancel a ha

noncomputable instance : Semifield DQ1Zero where
  -- CommSemiring fields (delegate)
  __ := (inferInstance : CommSemiring DQ1Zero)
  -- GroupWithZero / CommGroupWithZero fields (delegate)
  __ := (inferInstance : CommGroupWithZero DQ1Zero)
  nnqsmul := _

end DQ1Zero
