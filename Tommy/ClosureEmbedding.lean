import Tommy.DNonzero

/-!
# Closure Embedding: D → S¹

Extends `D_nz.toS1` to all of `D` by sending the zero element to the
default point `(1, 0)` on S¹. This resolves §3f sub-blocker (a).

The zero element of D has `(x, y) = (0, 0)` and is mapped to `(1, 0) ∈ S¹`
by convention. All nonzero elements are mapped via normalisation `phi`.
-/

open Real Set

noncomputable section

/-- The default point on S¹ for the zero element of D. -/
lemma default_mem_S1 : ((1 : ℝ), (0 : ℝ)) ∈ S1 := by
  simp [S1]

/-- Closure embedding: maps any D element to S¹.
    Nonzero elements are normalised via phi; the zero element maps to (1, 0). -/
noncomputable def closure_embedding (d : D) : ↥S1 :=
  if h : d.x ≠ 0 ∨ d.y ≠ 0 then
    ⟨phi (d.x, d.y), phi_real_mem_S1 d.x d.y h⟩
  else
    ⟨(1, 0), default_mem_S1⟩

/-- On nonzero elements, `closure_embedding` agrees with `D_nz.toS1`. -/
theorem closure_embedding_eq_toS1 (d : D_nz) :
    closure_embedding d.val = D_nz.toS1 d := by
  simp [closure_embedding, D_nz.toS1, d.property]

/-
The closure embedding is surjective onto S¹.
-/
theorem closure_embedding_surjective : Function.Surjective closure_embedding := by
  intro s;
  -- By definition of $D_nz$, there exists $d \in D_nz$ such that $D_nz.toS1 d = s$.
  obtain ⟨d, hd⟩ : ∃ d : D_nz, D_nz.toS1 d = s := by
    -- By definition of surjectivity, for every s in S1, there exists a d in D_nz such that toS1 d = s.
    apply D_nz.toS1_surjective;
  exact ⟨ d.val, hd ▸ closure_embedding_eq_toS1 d ⟩

end