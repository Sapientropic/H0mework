import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.PairP0
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Primitive

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

theorem p0_heat_pointwise (term : Term) (z : Point × Point) (t : ℝ)
    (hp : sourceP0 term) (positive : 0 < term.exponent) :
    Laplace.heatIntegrand term Axis.originalS Axis.originalS Axis.originalS z t =
      (term.weight : ℝ) * Axis.originalWeight^3 *
        (2 / Real.sqrt Real.pi) *
          spatialP0Coupled (fun _ => Axis.sPairRate term Axis.originalS)
            (fun _ => 2*Axis.originalAlpha) Axis.originalCentre t z := by
  unfold Laplace.heatIntegrand Laplace.primitiveAmplitude
  rw [p0_pair_shape term z.1 hp positive,
    Axis.original_s_pair_field z.2,Axis.heat_spatial_exp z t]
  unfold spatialP0Coupled Axis.spatialSCoupled Axis.coupledAxis
  simp_rw [Finset.prod_mul_distrib]
  unfold Axis.originalWeight
  ring

theorem p0_heat_inner_zero (term : Term) (t : ℝ)
    (hp : sourceP0 term) (positive : 0 < term.exponent) (ht : 0 < t) :
    (∫ z : Point × Point,
      Laplace.heatIntegrand term Axis.originalS Axis.originalS Axis.originalS z t) = 0 := by
  simp_rw [p0_heat_pointwise term _ t hp positive]
  rw [integral_const_mul]
  have hfirst : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate term Axis.originalS) i := by
    intro i
    exact Axis.s_pair_rate_positive term Axis.originalS positive Axis.original_s_exponent
  have hsecond : ∀ i : Fin 3, 0 < (fun _ => 2*Axis.originalAlpha) i := by
    intro i
    have ha : 0 < Axis.originalAlpha := by
      unfold Axis.originalAlpha
      exact_mod_cast Axis.original_s_exponent
    exact mul_pos (by norm_num) ha
  rw [spatial_p0_same_centre_zero _ _ Axis.originalCentre t hfirst hsecond ht]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
