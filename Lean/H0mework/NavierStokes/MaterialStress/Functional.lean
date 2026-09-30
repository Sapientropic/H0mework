import H0mework.NavierStokes.MaterialStress.Inverse
import H0mework.Physics.Coframe.CoframeSectorStress
import H0mework.Physics.Matter.MatterVariation

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeMatterCoframeStress

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineCoframeVariation StageNineCoframeLocalDifferentiability
open StageNineCoframeHolonomicCauchySafeRealization StageNineCoframeSectorStress
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineMatterVariation SU7ExteriorBreakingYukawa
open StageNineDynamicBreakingVacuum StageNineP286GaugeConnectionVariationDensity
open NativeCoframeInverseAction

noncomputable section

def pairing (current : LorentzianCoframe) : LorentzianCoframe →L[ℝ] ℝ :=
  ∑ direction, ∑ internal, current direction internal • coframeEntryCLM direction internal

theorem pairing_apply (current frame : LorentzianCoframe) :
    pairing current frame = ∑ direction, ∑ internal, current direction internal * frame direction internal := by
  simp [pairing]

def density (current : LorentzianCoframe) (mass : ℝ) (frame : LorentzianCoframe) : ℝ :=
  |frame.det| * (pairing current frame⁻¹ + mass)

def kineticCoefficients (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (derivative : Fin 4 → DiracExteriorMatterCarrier) : LorentzianCoframe :=
  fun direction internal => (dual (Complex.I • diracMatrixMatterAction (diracGamma internal) (derivative direction))).re

def currentCoefficients (field : StageNineContinuumPointField) : LorentzianCoframe :=
  kineticCoefficients field.conjugateMatter field.matterCovariantDerivative

def massCoefficient (field : StageNineContinuumPointField) : ℝ :=
  (field.conjugateMatter (chiralExteriorYukawaAction (scalarCoordinateEquiv.symm field.scalar) field.matter)).re

theorem gamma_sum_action (coefficient : Fin 4 → ℂ) (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (∑ direction, coefficient direction • diracGamma direction) matter =
      ∑ direction, coefficient direction • diracMatrixMatterAction (diracGamma direction) matter := by
  let linear : DiracMatrix →ₗ[ℂ] DiracExteriorMatterCarrier := {
    toFun := fun matrix => diracMatrixMatterAction matrix matter
    map_add' := fun first second => coframeDiracMatrixMatterAction_add_matrix first second matter
    map_smul' := fun scalar matrix => coframeDiracMatrixMatterAction_smul_matrix scalar matrix matter }
  change linear (∑ direction, coefficient direction • diracGamma direction) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  exact linear.map_smul (coefficient direction) (diracGamma direction)

theorem pairing_eq_kinetic (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (derivative : Fin 4 → DiracExteriorMatterCarrier) (frame : LorentzianCoframe) :
    pairing (kineticCoefficients dual derivative) frame⁻¹ =
      (dual (Complex.I • ∑ direction, diracMatrixMatterAction
        (inverseCoframeDiracGamma {coframe := frame, derivative := 0} direction) (derivative direction))).re := by
  simp only [pairing_apply, kineticCoefficients, inverseCoframeDiracGamma, gamma_sum_action,
    map_sum, Finset.smul_sum, map_smul, smul_eq_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro direction _
  apply Finset.sum_congr rfl
  intro internal _
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Exact elimination of the existing full matter-sector action to its complete coframe coefficients. -/
theorem density_eq_mother (source : SmoothUnifiedSource) (point : ProofFreeRicherAnholonomicSource.BasePoint)
    (field : StageNineContinuumPointField) (frame : LorentzianCoframe) :
    density (currentCoefficients field) (massCoefficient field) frame =
      coframeMatterSectorLocalDensity source point field frame := by
  simp only [density, currentCoefficients, pairing_eq_kinetic, massCoefficient]
  unfold coframeMatterSectorLocalDensity generatedVolumeDensity generatedContinuumMatterDensity
  simp only [matterDualFrameRelative_zeroChart, generatedContinuumMatterVector,
    matterDerivativeFrameRelative_zeroChart, scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, withCoframe]
  rw [map_add, Complex.add_re]

/-- Vanishing is consumed only here, after the same source has generated its matter equation. -/
theorem density_hasFDerivAt_of_inner_zero (current : LorentzianCoframe) (mass : ℝ) (frame : LorentzianCoframe)
    (nondegenerate : frame.det ≠ 0) (innerZero : pairing current frame⁻¹ + mass = 0) :
    HasFDerivAt (density current mass)
      (|frame.det| • (pairing current).comp (inverseDerivative frame)) frame := by
  have volumeDerivative := ((coframe_volume_contDiffAt frame nondegenerate).differentiableAt (by simp)).hasFDerivAt
  have innerDerivative := ((pairing current).hasFDerivAt.comp frame (inverse_hasFDerivAt frame nondegenerate)).add_const mass
  have product := volumeDerivative.mul innerDerivative
  convert! product using 1
  simp only [Function.comp_apply, innerZero, zero_smul, add_zero]
  rfl

end
end SaturationMonoid.NavierStokes.NativeMatterCoframeStress
