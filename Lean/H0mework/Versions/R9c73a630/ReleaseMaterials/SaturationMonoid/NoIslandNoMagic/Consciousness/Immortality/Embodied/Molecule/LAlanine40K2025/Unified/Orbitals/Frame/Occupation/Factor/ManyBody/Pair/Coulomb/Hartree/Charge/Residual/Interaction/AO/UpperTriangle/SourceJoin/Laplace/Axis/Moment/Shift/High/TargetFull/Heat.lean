import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Pair
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Primitive

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

def targetFullHeatInner (left right nextLeft nextRight : Term) (t : ℝ) : ℝ :=
  Axis.sPairCoefficient left right *
    Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
      spatialTargetFullClosed
        left.powers right.powers nextLeft.powers nextRight.powers
        (fun _ => Axis.sPairRate left right)
        (fun _ => Axis.sPairRate nextLeft nextRight)
        (Axis.sPairCentre left right)
        (Axis.sPairCentre nextLeft nextRight)
        (fun i => (left.centre i : ℝ))
        (fun i => (right.centre i : ℝ))
        (fun i => (nextLeft.centre i : ℝ))
        (fun i => (nextRight.centre i : ℝ)) t

theorem target_full_heat_pointwise (left right nextLeft nextRight : Term)
    (z : Point × Point) (t : ℝ) :
    Laplace.heatIntegrand left right nextLeft nextRight z t =
      Axis.sPairCoefficient left right *
        Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
          spatialTargetFull
            left.powers right.powers nextLeft.powers nextRight.powers
            (fun _ => Axis.sPairRate left right)
            (fun _ => Axis.sPairRate nextLeft nextRight)
            (Axis.sPairCentre left right)
            (Axis.sPairCentre nextLeft nextRight)
            (fun i => (left.centre i : ℝ))
            (fun i => (right.centre i : ℝ))
            (fun i => (nextLeft.centre i : ℝ))
            (fun i => (nextRight.centre i : ℝ)) t z := by
  unfold Laplace.heatIntegrand Laplace.primitiveAmplitude
  rw [High.general_pair_shape left right z.1,
    High.general_pair_shape nextLeft nextRight z.2,
    Axis.heat_spatial_exp z t]
  unfold spatialTargetFull targetFullAxisIntegrand Axis.coupledAxis
  simp_rw [Finset.prod_mul_distrib]
  ring

theorem target_full_heat_inner_closed
    (left right nextLeft nextRight : Term) (t : ℝ)
    (hleftDegree : Shift.sourceLowDegree left)
    (hrightDegree : Shift.sourceLowDegree right)
    (hnextLeftDegree : Shift.sourceLowDegree nextLeft)
    (hnextRightDegree : Shift.sourceLowDegree nextRight)
    (hleftPos : 0 < left.exponent) (hrightPos : 0 < right.exponent)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent)
    (ht : 0 < t) :
    (∫ z : Point × Point,
      Laplace.heatIntegrand left right nextLeft nextRight z t) =
        targetFullHeatInner left right nextLeft nextRight t := by
  simp_rw [target_full_heat_pointwise left right nextLeft nextRight _ t]
  rw [integral_const_mul]
  have hfirst : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate left right) i := by
    intro i
    exact Axis.s_pair_rate_positive left right hleftPos hrightPos
  have hsecond : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate nextLeft nextRight) i := by
    intro i
    exact Axis.s_pair_rate_positive nextLeft nextRight hnextLeftPos hnextRightPos
  rw [spatial_target_full_factor
    left.powers right.powers nextLeft.powers nextRight.powers _ _
    (Axis.sPairCentre left right)
    (Axis.sPairCentre nextLeft nextRight)
    (fun i => (left.centre i : ℝ))
    (fun i => (right.centre i : ℝ))
    (fun i => (nextLeft.centre i : ℝ))
    (fun i => (nextRight.centre i : ℝ)) t
    hleftDegree hrightDegree hnextLeftDegree hnextRightDegree
    hfirst hsecond ht]
  rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
