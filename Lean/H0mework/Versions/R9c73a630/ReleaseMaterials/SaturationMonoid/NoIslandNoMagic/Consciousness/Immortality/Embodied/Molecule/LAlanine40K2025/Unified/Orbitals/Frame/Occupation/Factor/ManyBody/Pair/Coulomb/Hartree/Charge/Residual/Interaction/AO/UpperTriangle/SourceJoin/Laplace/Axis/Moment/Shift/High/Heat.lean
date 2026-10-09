import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Pair
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Primitive

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

def pairHeatInner (left right nextLeft nextRight : Term) (t : ℝ) : ℝ :=
  Axis.sPairCoefficient left right *
    Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
      spatialPairClosed left.powers right.powers
        (fun _ => Axis.sPairRate left right)
        (fun _ => Axis.sPairRate nextLeft nextRight)
        (Axis.sPairCentre left right)
        (Axis.sPairCentre nextLeft nextRight)
        (fun i => (left.centre i : ℝ))
        (fun i => (right.centre i : ℝ)) t

theorem pair_heat_pointwise (left right nextLeft nextRight : Term)
    (z : Point × Point) (t : ℝ)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight) :
    Laplace.heatIntegrand left right nextLeft nextRight z t =
      Axis.sPairCoefficient left right *
        Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
          spatialPair left.powers right.powers
            (fun _ => Axis.sPairRate left right)
            (fun _ => Axis.sPairRate nextLeft nextRight)
            (Axis.sPairCentre left right)
            (Axis.sPairCentre nextLeft nextRight)
            (fun i => (left.centre i : ℝ))
            (fun i => (right.centre i : ℝ)) t z := by
  unfold Laplace.heatIntegrand Laplace.primitiveAmplitude
  rw [general_pair_shape left right z.1,
    Axis.s_pair_shape nextLeft nextRight z.2 hnextLeft hnextRight,
    Axis.heat_spatial_exp z t]
  unfold spatialPair axisPairIntegrand Axis.coupledAxis
  simp_rw [Finset.prod_mul_distrib]
  ring

theorem pair_heat_inner_closed (left right nextLeft nextRight : Term) (t : ℝ)
    (hleftDegree : Shift.sourceLowDegree left)
    (hrightDegree : Shift.sourceLowDegree right)
    (hleftPos : 0 < left.exponent) (hrightPos : 0 < right.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent)
    (ht : 0 < t) :
    (∫ z : Point × Point,
      Laplace.heatIntegrand left right nextLeft nextRight z t) =
        pairHeatInner left right nextLeft nextRight t := by
  simp_rw [pair_heat_pointwise left right nextLeft nextRight _ t
    hnextLeft hnextRight]
  rw [integral_const_mul]
  have hfirst : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate left right) i := by
    intro i
    exact Axis.s_pair_rate_positive left right hleftPos hrightPos
  have hsecond : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate nextLeft nextRight) i := by
    intro i
    exact Axis.s_pair_rate_positive nextLeft nextRight hnextLeftPos hnextRightPos
  rw [spatial_pair_factor left.powers right.powers _ _
    (Axis.sPairCentre left right)
    (Axis.sPairCentre nextLeft nextRight)
    (fun i => (left.centre i : ℝ))
    (fun i => (right.centre i : ℝ)) t
    hleftDegree hrightDegree hfirst hsecond ht]
  rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
