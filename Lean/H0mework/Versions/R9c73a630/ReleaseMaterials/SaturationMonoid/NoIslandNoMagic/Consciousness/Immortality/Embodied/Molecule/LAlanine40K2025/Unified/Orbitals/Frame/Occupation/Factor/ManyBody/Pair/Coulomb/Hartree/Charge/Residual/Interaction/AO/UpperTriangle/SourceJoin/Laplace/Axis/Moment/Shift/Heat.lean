import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Pair
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Primitive

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

def shiftHeatInner (term nextLeft nextRight : Term) (t : ℝ) : ℝ :=
  Axis.sPairCoefficient term Axis.originalS *
    Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
      spatialShiftClosed term.powers
        (fun _ => Axis.sPairRate term Axis.originalS)
        (fun _ => Axis.sPairRate nextLeft nextRight)
        (Axis.sPairCentre term Axis.originalS)
        (Axis.sPairCentre nextLeft nextRight)
        (fun i => (term.centre i : ℝ)) t

theorem shift_heat_pointwise (term nextLeft nextRight : Term)
    (z : Point × Point) (t : ℝ)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight) :
    Laplace.heatIntegrand term Axis.originalS nextLeft nextRight z t =
      Axis.sPairCoefficient term Axis.originalS *
        Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
          spatialShift term.powers
            (fun _ => Axis.sPairRate term Axis.originalS)
            (fun _ => Axis.sPairRate nextLeft nextRight)
            (Axis.sPairCentre term Axis.originalS)
            (Axis.sPairCentre nextLeft nextRight)
            (fun i => (term.centre i : ℝ)) t z := by
  unfold Laplace.heatIntegrand Laplace.primitiveAmplitude
  rw [shifted_pair_shape term z.1,
    Axis.s_pair_shape nextLeft nextRight z.2 hnextLeft hnextRight,
    Axis.heat_spatial_exp z t]
  unfold spatialShift axisShiftIntegrand Axis.coupledAxis
  simp_rw [Finset.prod_mul_distrib]
  ring

theorem shift_heat_inner_closed (term nextLeft nextRight : Term) (t : ℝ)
    (hdegree : sourceLowDegree term) (positive : 0 < term.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent)
    (ht : 0 < t) :
    (∫ z : Point × Point,
      Laplace.heatIntegrand term Axis.originalS nextLeft nextRight z t) =
        shiftHeatInner term nextLeft nextRight t := by
  simp_rw [shift_heat_pointwise term nextLeft nextRight _ t hnextLeft hnextRight]
  rw [integral_const_mul]
  have hfirst : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate term Axis.originalS) i := by
    intro i
    exact Axis.s_pair_rate_positive term Axis.originalS positive Axis.original_s_exponent
  have hsecond : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate nextLeft nextRight) i := by
    intro i
    exact Axis.s_pair_rate_positive nextLeft nextRight hnextLeftPos hnextRightPos
  rw [spatial_shift_factor term.powers _ _
    (Axis.sPairCentre term Axis.originalS)
    (Axis.sPairCentre nextLeft nextRight)
    (fun i => (term.centre i : ℝ)) t hdegree hfirst hsecond ht]
  rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
