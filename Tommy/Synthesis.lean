import Tommy.Recovery
import Tommy.Substrate
import Tommy.Closure

/-- Theorem 5 (Three layers, one object): A structure bundling the three constructions
    of the paper: substrate D, closure embedding into S¹, arithmetic recovery map.
    The commutativity field asserts that rational fibres over S¹ correspond to
    prime-power content (χ > 0). -/
structure Synthesis where
  /-- A map from the directional plane to the unit circle (the closure embedding). -/
  closure_embedding : D → S1
  /-- A map from the directional plane to ℕ (the recovery map returning n). -/
  recovery_map : D → ℕ
  /-- Commutativity: a direction d has rational first coordinate in S¹ iff its
      arithmetic content χ(recovery_map d) is nonzero (i.e., recovery_map d is prime power). -/
  rational_fibres_match :
    ∀ (d : D), (∃ (q : ℚ), (closure_embedding d : ℝ × ℝ).1 = q) ↔
               (chi (recovery_map d) > 0)

/-- Re-export: the pointwise Λ recovery formula from Theorem 3. -/
theorem synthesis_lambda (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) = (chi n : ℝ) * Real.log ((n : ℝ) / (g n : ℝ)) :=
  theorem_3_lambda n

/-- The arithmetic skeleton (primitive integer directions ϕ(P)) is dense in S¹.
    Consequence of Theorem 1 from the closure layer. -/
theorem primitive_dirs_dense_in_S1 : closure (primitive_dirs : Set (ℝ × ℝ)) = S1 :=
  theorem_1
