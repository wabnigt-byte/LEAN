import Mathlib

/-!
# Compactified Product Space for Asymptotic Uniformity

We set up the compact ambient space for the topological bridge of the
asymptotic uniformity framework.

## The Total Space

The base is `AddCircle (1 : ℝ)` ≅ ℝ/ℤ, carrying the canonical normalized Haar measure.
The fiber is `OnePoint ℝ`, the one-point compactification of ℝ.
The total space is the product `AddCircle (1 : ℝ) × OnePoint ℝ`, which is compact
by Tychonoff's theorem.

## The Station Map

For coprime (p,q) with q > 0, the station map sends (p,q) to
  (p/q mod 1, 1/q)
in the total space. As q → ∞, the height 1/q → 0, a well-defined limit
in both ℝ and OnePoint ℝ.
-/

open scoped Topology
open Filter

noncomputable section

/-- The total space: product of the additive circle (base) and OnePoint ℝ (fiber). -/
abbrev TotalSpace := AddCircle (1 : ℝ) × OnePoint ℝ

/-- The base circle is compact. -/
instance : CompactSpace (AddCircle (1 : ℝ)) := inferInstance

/-- The one-point compactification of ℝ is compact. -/
instance : CompactSpace (OnePoint ℝ) := inferInstance

/-- The total space is compact (Tychonoff). -/
instance totalSpace_compact : CompactSpace TotalSpace := inferInstance

/-- The base circle has continuous addition and negation. -/
instance : ContinuousAdd (AddCircle (1 : ℝ)) := inferInstance
instance : ContinuousNeg (AddCircle (1 : ℝ)) := inferInstance

/-- The station map: sends (p, q) with q > 0 to a point on the total space.
    First coordinate: p/q mod 1 (projected to the additive circle).
    Second coordinate: 1/q (embedded into OnePoint ℝ). -/
def stationMap (p q : ℤ) (_hq : q ≠ 0) : TotalSpace :=
  (QuotientAddGroup.mk (p / q : ℝ),
   OnePoint.some (1 / (q : ℝ)))

/-
The height component 1/q → 0 as q → ∞, in ℝ.
-/
theorem height_tendsto_zero :
    Tendsto (fun q : ℕ => (1 : ℝ) / ((q : ℝ) + 1)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop )

/-
The embedded height 1/q → some 0 in OnePoint ℝ as q → ∞.
-/
theorem height_tendsto_onepoint :
    Tendsto (fun q : ℕ => (OnePoint.some ((1 : ℝ) / ((q : ℝ) + 1)) : OnePoint ℝ))
      atTop (nhds (OnePoint.some 0)) := by
  exact OnePoint.continuous_coe.tendsto _ |> fun h => h.comp ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) )

end