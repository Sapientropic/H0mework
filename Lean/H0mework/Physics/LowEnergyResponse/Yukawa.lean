import H0mework.Physics.SpinPair.Scalar
import H0mework.Physics.DualVariation.ConjugateMatterVariation

/-! Exact source-native Yukawa fluctuation block. The independent dual,
scalar and matter are all varied. No Hermitian-conjugate term is installed. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Response.Yukawa
open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7ExteriorBreakingYukawa StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineP286GaugeConnectionVariationDensity Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource
noncomputable section

/-- Every repaired Yukawa output has zero degree-two input slot. -/
theorem output_degree_two_zero (scalar : ExteriorBreakingScalarCarrier)
    (matter : DiracExteriorMatterCarrier) (spin : DiracSpinorIndex) :
    (diracDualRightChiralYukawaAction scalar matter spin).2.1 = 0 := rfl

/-- The whole repaired map vanishes on any matter with no degree-two slot. -/
theorem apply_eq_zero_of_degree_two_zero (scalar : ExteriorBreakingScalarCarrier)
    (matter : DiracExteriorMatterCarrier)
    (noInput : ∀ spin, (matter spin).2.1 = 0) :
    diracDualRightChiralYukawaAction scalar matter = 0 := by
  funext spin
  change (exteriorYukawaMassMap scalar
    (∑ column, rightChiralityProjector spin column • (matter column).2.1), (0, 0)) = 0
  simp only [noInput, smul_zero, Finset.sum_const_zero, map_zero]
  rfl

/-- Stronger than a fixed-vacuum nilpotence: every ordered pair is zero. -/
theorem ordered_product_zero (first second : ExteriorBreakingScalarCarrier) :
    (diracDualRightChiralYukawaAction first).comp
      (diracDualRightChiralYukawaAction second) = 0 := by
  apply LinearMap.ext
  intro matter
  exact apply_eq_zero_of_degree_two_zero first _
    (fun spin => output_degree_two_zero second matter spin)

/-- Complete scalar/matter/independent-dual affine path through the actual. -/
def path (eta : BasePoint → ScalarCoordinateCarrier)
    (xi : BasePoint → DiracExteriorMatterCarrier)
    (chi : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (parameter : ℝ) : StageNineHolonomicConfiguration :=
  { actual with
    scalar := fun p => actual.scalar p + (parameter : ℂ) • eta p
    matter := fun p => actual.matter p + (parameter : ℂ) • xi p
    conjugateMatter := fun p => actual.conjugateMatter p + (parameter : ℂ) • chi p }

/-- Actual degree-one Yukawa forcing, including the scalar/matter cross block. -/
def linearVector (point : BasePoint) (eta : ScalarCoordinateCarrier)
    (xi : DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier :=
  diracDualRightChiralYukawaAction
      (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) xi +
    diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm eta) (actual.matter point)

def quadraticVector (eta : ScalarCoordinateCarrier)
    (xi : DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier :=
  diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm eta) xi

/-- The background vector vanishes by its existing source equation. -/
theorem background_zero (point : BasePoint) :
    diracDualRightChiralYukawaAction
      (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) (actual.matter point) = 0 := by
  have h := actual_yukawaVector_zero point
  simpa only [generatedContinuumDiracDualYukawaVector, toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart,
    actual_scalar, sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply] using h

theorem vector_expansion (eta : BasePoint → ScalarCoordinateCarrier)
    (xi : BasePoint → DiracExteriorMatterCarrier)
    (chi : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (parameter : ℝ) (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (path eta xi chi parameter) point) =
      (parameter : ℂ) • linearVector point (eta point) (xi point) +
        (parameter : ℂ)^2 • quadraticVector (eta point) (xi point) := by
  simp only [generatedContinuumDiracDualYukawaVector, toContinuumPointField, path,
    scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart,
    actual_scalar, sourceGeneratedVacuumCoordinates, map_add, map_smul,
    scalarCoordinateEquiv.symm_apply_apply, diracDualRightChiralYukawaAction_add,
    diracDualRightChiralYukawaAction_smul, LinearMap.add_apply, LinearMap.smul_apply,
    background_zero, linearVector, quadraticVector]
  module

/-- Pure trilinear algebra; source equations discharge these hypotheses below. -/
private theorem paired_expansion (v eta : ExteriorBreakingScalarCarrier)
    (psi xi : DiracExteriorMatterCarrier)
    (dual chi : Module.Dual ℂ DiracExteriorMatterCarrier) (t : ℝ)
    (zeroVector : diracDualRightChiralYukawaAction v psi = 0)
    (zeroDual : ∀ s m, dual (diracDualRightChiralYukawaAction s m) = 0) :
    ((dual + (t : ℂ) • chi)
      (diracDualRightChiralYukawaAction (v + (t : ℂ) • eta) (psi + (t : ℂ) • xi))).re =
      t^2 * (chi (diracDualRightChiralYukawaAction v xi +
        diracDualRightChiralYukawaAction eta psi)).re +
      t^3 * (chi (diracDualRightChiralYukawaAction eta xi)).re := by
  simp only [diracDualRightChiralYukawaAction_add, diracDualRightChiralYukawaAction_smul,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    zeroVector, zeroDual, add_zero, zero_add, smul_eq_mul,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.mul_im]
  ring

/-- The native density is exactly quadratic plus cubic. No cross term is dropped. -/
theorem density_expansion (eta : BasePoint → ScalarCoordinateCarrier)
    (xi : BasePoint → DiracExteriorMatterCarrier)
    (chi : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (parameter : ℝ) (point : BasePoint) :
    generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (path eta xi chi parameter) point) =
      generatedVolumeDensity (toContinuumPointField actual point) *
        (parameter^2 * (chi point (linearVector point (eta point) (xi point))).re +
         parameter^3 * (chi point (quadraticVector (eta point) (xi point))).re) := by
  have annihilator : ∀ scalar matter,
      actual.conjugateMatter point (diracDualRightChiralYukawaAction scalar matter) = 0 := by
    intro scalar matter
    rw [actual_conjugateMatter]
    exact spinPairDual_yukawa_annihilates scalar matter _ _
  have paired := paired_expansion (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
    (scalarCoordinateEquiv.symm (eta point)) (actual.matter point) (xi point)
    (actual.conjugateMatter point) (chi point) parameter (background_zero point) annihilator
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
  simp only [generatedContinuumDiracDualYukawaVector, toContinuumPointField, path,
    scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart,
    matterDualFrameRelative_zeroChart, actual_scalar, sourceGeneratedVacuumCoordinates,
    scalarCoordinateEquiv.symm.map_add, scalarCoordinateEquiv.symm.map_smul,
    scalarCoordinateEquiv.symm_apply_apply]
  change generatedVolumeDensity (toContinuumPointField actual point) *
    ((actual.conjugateMatter point + (parameter : ℂ) • chi point)
      (diracDualRightChiralYukawaAction
        (sourceGeneratedVacuumBase positiveSmoothUnifiedSource +
          (parameter : ℂ) • scalarCoordinateEquiv.symm (eta point))
        (actual.matter point + (parameter : ℂ) • xi point))).re = _
  rw [paired]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.Response.Yukawa
