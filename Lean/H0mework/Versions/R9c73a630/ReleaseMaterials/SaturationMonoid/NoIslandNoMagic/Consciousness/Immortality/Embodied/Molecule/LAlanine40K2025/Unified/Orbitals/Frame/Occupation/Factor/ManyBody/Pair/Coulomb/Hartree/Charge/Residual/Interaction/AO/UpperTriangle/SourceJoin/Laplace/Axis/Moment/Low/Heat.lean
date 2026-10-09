import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Pair
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Primitive

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

def lowHeatInner (term nextLeft nextRight : Term) (t : ℝ) : ℝ :=
  (term.weight : ℝ) * Axis.originalWeight *
    Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
      spatialLowClosed term.powers
        (fun _ => Axis.sPairRate term Axis.originalS)
        (fun _ => Axis.sPairRate nextLeft nextRight)
        Axis.originalCentre (Axis.sPairCentre nextLeft nextRight) t

theorem low_heat_pointwise (term nextLeft nextRight : Term)
    (z : Point × Point) (t : ℝ)
    (hl : sourceLow term) (positive : 0 < term.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight) :
    Laplace.heatIntegrand term Axis.originalS nextLeft nextRight z t =
      (term.weight : ℝ) * Axis.originalWeight *
        Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
          spatialLow term.powers
            (fun _ => Axis.sPairRate term Axis.originalS)
            (fun _ => Axis.sPairRate nextLeft nextRight)
            Axis.originalCentre (Axis.sPairCentre nextLeft nextRight) t z := by
  unfold Laplace.heatIntegrand Laplace.primitiveAmplitude
  rw [low_pair_shape term z.1 hl positive,
    Axis.s_pair_shape nextLeft nextRight z.2 hnextLeft hnextRight,
    Axis.heat_spatial_exp z t]
  unfold spatialLow axisLowIntegrand Axis.coupledAxis
  simp_rw [Finset.prod_mul_distrib]
  unfold Axis.originalWeight
  ring

theorem low_heat_inner_closed (term nextLeft nextRight : Term) (t : ℝ)
    (hl : sourceLow term) (positive : 0 < term.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent)
    (ht : 0 < t) :
    (∫ z : Point × Point,
      Laplace.heatIntegrand term Axis.originalS nextLeft nextRight z t) =
        lowHeatInner term nextLeft nextRight t := by
  simp_rw [low_heat_pointwise term nextLeft nextRight _ t
    hl positive hnextLeft hnextRight]
  rw [integral_const_mul]
  have hfirst : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate term Axis.originalS) i := by
    intro i
    exact Axis.s_pair_rate_positive term Axis.originalS positive Axis.original_s_exponent
  have hsecond : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate nextLeft nextRight) i := by
    intro i
    exact Axis.s_pair_rate_positive nextLeft nextRight hnextLeftPos hnextRightPos
  rw [spatial_low_factor term.powers _ _ Axis.originalCentre
    (Axis.sPairCentre nextLeft nextRight) t
    (fun i => (hl i).1) hfirst hsecond ht]
  rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
