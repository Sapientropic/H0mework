import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.GenericS
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

def sHeatInner (left right nextLeft nextRight : Term) (t : ℝ) : ℝ :=
  sPairCoefficient left right * sPairCoefficient nextLeft nextRight *
    (2 / Real.sqrt Real.pi) *
      ∏ axis : Fin 3,
        (Real.pi / Real.sqrt
          (sPairRate left right * sPairRate nextLeft nextRight +
            (sPairRate left right + sPairRate nextLeft nextRight)*t^2)) *
          Real.exp
            (-(sPairRate left right*sPairRate nextLeft nextRight*t^2 /
                (sPairRate left right*sPairRate nextLeft nextRight +
                  (sPairRate left right+sPairRate nextLeft nextRight)*t^2) *
                  (sPairCentre left right axis-sPairCentre nextLeft nextRight axis)^2))

theorem s_heat_pointwise (left right nextLeft nextRight : Term)
    (z : Point × Point) (t : ℝ)
    (hl : sPowers left) (hr : sPowers right)
    (hnl : sPowers nextLeft) (hnr : sPowers nextRight) :
    Laplace.heatIntegrand left right nextLeft nextRight z t =
      sPairCoefficient left right * sPairCoefficient nextLeft nextRight *
        (2 / Real.sqrt Real.pi) *
          spatialSCoupled (fun _ => sPairRate left right)
            (fun _ => sPairRate nextLeft nextRight)
            (sPairCentre left right) (sPairCentre nextLeft nextRight) t z := by
  unfold Laplace.heatIntegrand Laplace.primitiveAmplitude
  rw [s_pair_shape left right z.1 hl hr,
    s_pair_shape nextLeft nextRight z.2 hnl hnr,
    heat_spatial_exp z t]
  unfold spatialSCoupled coupledAxis
  simp_rw [Finset.prod_mul_distrib]
  ring

theorem s_heat_inner_closed (left right nextLeft nextRight : Term) (t : ℝ)
    (hl : sPowers left) (hr : sPowers right)
    (hnl : sPowers nextLeft) (hnr : sPowers nextRight)
    (hleft : 0 < left.exponent) (hright : 0 < right.exponent)
    (hnextLeft : 0 < nextLeft.exponent) (hnextRight : 0 < nextRight.exponent)
    (ht : 0 < t) :
    (∫ z : Point × Point,
      Laplace.heatIntegrand left right nextLeft nextRight z t) =
        sHeatInner left right nextLeft nextRight t := by
  simp_rw [s_heat_pointwise left right nextLeft nextRight _ t hl hr hnl hnr]
  rw [integral_const_mul]
  rw [spatial_s_factor
    (fun _ => sPairRate left right)
    (fun _ => sPairRate nextLeft nextRight)
    (sPairCentre left right) (sPairCentre nextLeft nextRight) t
    (fun _ => s_pair_rate_positive left right hleft hright)
    (fun _ => s_pair_rate_positive nextLeft nextRight hnextLeft hnextRight) ht]
  rfl

theorem s_primitive_outer (left right nextLeft nextRight : Term)
    (hl : sPowers left) (hr : sPowers right)
    (hnl : sPowers nextLeft) (hnr : sPowers nextRight)
    (hleft : 0 < left.exponent) (hright : 0 < right.exponent)
    (hnextLeft : 0 < nextLeft.exponent) (hnextRight : 0 < nextRight.exponent) :
    Laplace.primitiveHeatInteraction (left,right) (nextLeft,nextRight) =
      ∫ t in Ioi (0 : ℝ), sHeatInner left right nextLeft nextRight t := by
  unfold Laplace.primitiveHeatInteraction
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact s_heat_inner_closed left right nextLeft nextRight t
    hl hr hnl hnr hleft hright hnextLeft hnextRight ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
