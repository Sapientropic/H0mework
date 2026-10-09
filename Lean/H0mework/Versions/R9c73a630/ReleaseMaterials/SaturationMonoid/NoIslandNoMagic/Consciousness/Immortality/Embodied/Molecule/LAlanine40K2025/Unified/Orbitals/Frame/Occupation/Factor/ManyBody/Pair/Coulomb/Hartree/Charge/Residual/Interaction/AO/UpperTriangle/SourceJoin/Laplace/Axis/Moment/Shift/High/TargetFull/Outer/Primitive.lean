import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Compactify
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Quartet

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

def compactifiedHeatInner (left right nextLeft nextRight : Term) (u : ℝ) : ℝ :=
  TargetFull.targetFullHeatInner left right nextLeft nextRight (f u) /
    (1-u)^2

def compactifiedPrimitive (left right nextLeft nextRight : Term) : ℝ :=
  ∫ u in Ioo (0 : ℝ) 1,
    compactifiedHeatInner left right nextLeft nextRight u

theorem primitive_outer_compactified
    (left right nextLeft nextRight : Term)
    (hleftDegree : Shift.sourceLowDegree left)
    (hrightDegree : Shift.sourceLowDegree right)
    (hnextLeftDegree : Shift.sourceLowDegree nextLeft)
    (hnextRightDegree : Shift.sourceLowDegree nextRight)
    (hleftPos : 0 < left.exponent) (hrightPos : 0 < right.exponent)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent) :
    Laplace.primitiveHeatInteraction (left,right) (nextLeft,nextRight) =
      compactifiedPrimitive left right nextLeft nextRight := by
  calc
    Laplace.primitiveHeatInteraction (left,right) (nextLeft,nextRight) =
        ∫ t in Ioi (0 : ℝ),
          TargetFull.targetFullHeatInner left right nextLeft nextRight t :=
      TargetFull.target_full_primitive_outer left right nextLeft nextRight
        hleftDegree hrightDegree hnextLeftDegree hnextRightDegree
        hleftPos hrightPos hnextLeftPos hnextRightPos
    _ = compactifiedPrimitive left right nextLeft nextRight := by
      exact compactify_integral
        (TargetFull.targetFullHeatInner left right nextLeft nextRight)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
