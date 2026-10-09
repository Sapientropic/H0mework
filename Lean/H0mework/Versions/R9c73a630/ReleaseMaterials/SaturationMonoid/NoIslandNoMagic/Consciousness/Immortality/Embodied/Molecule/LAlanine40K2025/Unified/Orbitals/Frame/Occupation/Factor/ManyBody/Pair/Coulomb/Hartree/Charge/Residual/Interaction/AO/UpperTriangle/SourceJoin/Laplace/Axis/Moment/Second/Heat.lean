import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second.Pair
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.GenericS
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Primitive

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

def dAxisSHeatInner (term nextLeft nextRight : Term) (t : ℝ) : ℝ :=
  (term.weight : ℝ) * Axis.originalWeight *
    Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
      spatialD2MixedClosed (dAxis term)
        (fun _ => Axis.sPairRate term Axis.originalS)
        (fun _ => Axis.sPairRate nextLeft nextRight)
        Axis.originalCentre (Axis.sPairCentre nextLeft nextRight) t

theorem d_axis_s_heat_pointwise (term nextLeft nextRight : Term)
    (z : Point × Point) (t : ℝ)
    (hd : sourceDAxis term) (positive : 0 < term.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight) :
    Laplace.heatIntegrand term Axis.originalS nextLeft nextRight z t =
      (term.weight : ℝ) * Axis.originalWeight *
        Axis.sPairCoefficient nextLeft nextRight * (2 / Real.sqrt Real.pi) *
          spatialD2Mixed (dAxis term)
            (fun _ => Axis.sPairRate term Axis.originalS)
            (fun _ => Axis.sPairRate nextLeft nextRight)
            Axis.originalCentre (Axis.sPairCentre nextLeft nextRight) t z := by
  unfold Laplace.heatIntegrand Laplace.primitiveAmplitude
  rw [d_axis_pair_shape term z.1 hd positive,
    Axis.s_pair_shape nextLeft nextRight z.2 hnextLeft hnextRight,
    Axis.heat_spatial_exp z t]
  unfold spatialD2Mixed Axis.spatialSCoupled Axis.coupledAxis
  simp_rw [Finset.prod_mul_distrib]
  unfold Axis.originalWeight
  ring

theorem d_axis_s_heat_inner_closed (term nextLeft nextRight : Term) (t : ℝ)
    (hd : sourceDAxis term) (positive : 0 < term.exponent)
    (hnextLeft : Axis.sPowers nextLeft) (hnextRight : Axis.sPowers nextRight)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent)
    (ht : 0 < t) :
    (∫ z : Point × Point,
      Laplace.heatIntegrand term Axis.originalS nextLeft nextRight z t) =
        dAxisSHeatInner term nextLeft nextRight t := by
  simp_rw [d_axis_s_heat_pointwise term nextLeft nextRight _ t
    hd positive hnextLeft hnextRight]
  rw [integral_const_mul]
  have hfirst : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate term Axis.originalS) i := by
    intro i
    exact Axis.s_pair_rate_positive term Axis.originalS positive Axis.original_s_exponent
  have hsecond : ∀ i : Fin 3, 0 < (fun _ => Axis.sPairRate nextLeft nextRight) i := by
    intro i
    exact Axis.s_pair_rate_positive nextLeft nextRight hnextLeftPos hnextRightPos
  rw [spatial_d2_mixed_factor (dAxis term) _ _ Axis.originalCentre
    (Axis.sPairCentre nextLeft nextRight) t hfirst hsecond ht]
  rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
