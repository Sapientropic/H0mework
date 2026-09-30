import H0mework.Chemistry.LAlanineContinuousGroupCache.BlocksB0
import H0mework.Chemistry.LAlanineContinuousGroupCache.BlocksB1
import H0mework.Chemistry.LAlanineContinuousGroupCache.BlocksB2
import H0mework.Chemistry.LAlanineContinuousGroupCache.BlocksB3
import H0mework.Chemistry.LAlanineContinuousGroupCache.BlocksB4
import H0mework.Chemistry.LAlanineContinuousGroupCache.BlocksB5
import H0mework.Chemistry.LAlanineContinuousGroupCache.BlocksB6
import H0mework.Chemistry.LAlanineContinuousGroupCache.BlocksB7

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGroupCache

open Lean Elab Tactic SourceRectangle SourceSignedEvaluator

elab "closeSourceGroupFamily " stem:ident : tactic => do
  let goals ← getGoals
  unless goals.length == 94 do throwError "complete group census required"
  let prefixName := "SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGroupCache.Blocks."
  for (goal, group) in goals.zipIdx do
    let name := (prefixName ++ s!"B{group / 12}." ++ stem.getId.toString ++ s!"_{group}").toName
    goal.assign (Lean.mkConst name)
  setGoals []

theorem relative_eq_source (g : Group) :
    ∀ axis : Fin 3, cachedRelative g axis = relative (groupTerm g) (actualBox 0) axis := by
  change ∀ axis : Fin 3, cachedRelative g axis = sourceRelative g axis
  fin_cases g
  closeSourceGroupFamily relative_all

theorem radial_eq_source (g : Group) :
    cachedRadial g = radialPair (groupTerm g) (actualBox 0) := by
  change cachedRadial g = sourceRadial g
  fin_cases g
  closeSourceGroupFamily radial

theorem exp_from_radial (g : Group) : cachedExp g = sourceExpFromRadial g := by
  fin_cases g
  closeSourceGroupFamily exp

theorem exp_eq_source (g : Group) :
    cachedExp g = exponential (radialPair (groupTerm g) (actualBox 0))
      (groupSteps 0 g).1 (groupSteps 0 g).2 := by
  rw [exp_from_radial]
  unfold sourceExpFromRadial
  rw [radial_eq_source]

theorem poly_from_relative (g : Group) :
    ∀ axis power : Fin 3, ∀ order : Fin 4,
      cachedPoly g axis power order = sourcePolyFromRelative g axis power order := by
  fin_cases g
  closeSourceGroupFamily poly_all

theorem poly_eq_source (g : Group) (axis power : Fin 3) (order : Fin 4) :
    cachedPoly g axis power order =
      jetHorner (groupTerm g).exponent power.val order.val (relative (groupTerm g) (actualBox 0) axis) := by
  have generated := poly_from_relative g axis power order
  unfold sourcePolyFromRelative at generated
  rw [relative_eq_source, ← (actual_group_terms g).2.1] at generated
  exact generated

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGroupCache
