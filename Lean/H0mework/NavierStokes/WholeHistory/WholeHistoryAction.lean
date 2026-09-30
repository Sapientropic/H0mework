import H0mework.NavierStokes.WholeHistory.WholeHistoryField

set_option autoImplicit false
open scoped Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeWholeHistoryAction

open Set Filter
open PhysicsCore.ProofFreeRicherAnholonomicSource
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open RationalVorticityEvaluator
open NativeFullOrderSynthesis NativeWholeHistoryClock NativeWholeHistoryField

noncomputable section

theorem velocity_locally (parameter : ℝ) : ∀ᶠ sample in 𝓝 parameter,
    velocity sample = NativeReceiptSpacetime.velocity (receipt (cover parameter)) (physicalTime sample) := by
  filter_upwards [physicalTime_contDiff.continuous.tendsto parameter (Iio_mem_nhds (cover_spec parameter))]
    with sample before
  exact velocity_read _ sample before.le

theorem vorticity_locally (parameter : ℝ) : ∀ᶠ sample in 𝓝 parameter,
    vorticity sample = NativeReceiptSpacetime.state (receipt (cover parameter)) (physicalTime sample) := by
  filter_upwards [physicalTime_contDiff.continuous.tendsto parameter (Iio_mem_nhds (cover_spec parameter))]
    with sample before
  exact vorticity_read _ sample before.le

def momentum (parameter : ℝ) : ComplexVorticityHilbertState :=
  NativeReceiptSpacetime.timeJet (window (cover parameter)) 1 (physicalTime parameter)

def vorticityAction (parameter : ℝ) : ComplexVorticityHilbertState :=
  NativeUnifiedVorticityAction.rate (window (cover parameter)) (physicalTime parameter)

theorem velocity_hasDerivAt (parameter : ℝ) :
    HasDerivAt velocity (clockRate parameter • momentum parameter) parameter := by
  have inside : physicalTime parameter ∈ Icc (window (cover parameter)).first (window (cover parameter)).last :=
    ⟨(physicalTime_pos parameter).le, (cover_spec parameter).le⟩
  have source := NativeReceiptSpacetime.timeJet_evolves (window (cover parameter)) 0 (physicalTime parameter) inside
  have original := source.congr_of_mem
    (fun time member => (NativeReceiptSpacetime.timeJet_zero (window (cover parameter)) time member).symm) inside
  have written := (original.hasDerivAt (Icc_mem_nhds (physicalTime_pos parameter) (cover_spec parameter))).scomp
    parameter (physicalTime_hasDerivAt parameter)
  exact written.congr_of_eventuallyEq (velocity_locally parameter)

theorem vorticity_hasDerivAt (parameter : ℝ) :
    HasDerivAt vorticity (clockRate parameter • vorticityAction parameter) parameter := by
  have source := NativeUnifiedVorticityAction.state_hasDerivAt (window (cover parameter))
    (physicalTime parameter) ⟨physicalTime_pos parameter, cover_spec parameter⟩
  exact (source.scomp parameter (physicalTime_hasDerivAt parameter)).congr_of_eventuallyEq
    (vorticity_locally parameter)

theorem vorticityAction_row (parameter : ℝ) (wave : IntegerWavevector) :
    vorticityAction parameter wave =
      wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (vorticity parameter) wave :=
  NativeUnifiedVorticityAction.rate_row (window (cover parameter)) (physicalTime parameter)
    ⟨physicalTime_pos parameter, cover_spec parameter⟩ wave

theorem momentum_row (parameter : ℝ) (wave : IntegerWavevector) :
    momentum parameter wave = biotSavartVelocityCoefficient wave
      (wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (vorticity parameter) wave) := by
  rw [momentum, NativeReceiptSpacetime.timeJet_one_row (window (cover parameter)) _
    ⟨(physicalTime_pos parameter).le, (cover_spec parameter).le⟩]
  rfl

theorem physical_velocity_hasDerivAt (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => spatialField (velocity sample) space)
      (clockRate parameter • spatialField (momentum parameter) space) parameter := by
  have source := NativeTimeChartPhysicalAction.receipt_physical_hasDerivAt (window (cover parameter))
    (physicalTime parameter) ⟨physicalTime_pos parameter, cover_spec parameter⟩ space
  apply (source.scomp parameter (physicalTime_hasDerivAt parameter)).congr_of_eventuallyEq
  filter_upwards [velocity_locally parameter] with sample same
  rw [same]
  rfl

theorem physical_vorticity_hasDerivAt (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => spatialField (vorticity sample) space)
      (clockRate parameter • spatialField (vorticityAction parameter) space) parameter := by
  have source := NativeUnifiedVorticityAction.physical_hasDerivAt (window (cover parameter))
    (physicalTime parameter) ⟨physicalTime_pos parameter, cover_spec parameter⟩ space
  apply (source.scomp parameter (physicalTime_hasDerivAt parameter)).congr_of_eventuallyEq
  filter_upwards [vorticity_locally parameter] with sample same
  rw [same]
  rfl

theorem velocity_action_unscale (parameter : ℝ) (space : PhysicalSpace) :
    (clockRate parameter)⁻¹ • deriv (fun sample => spatialField (velocity sample) space) parameter =
      spatialField (momentum parameter) space := by
  rw [(physical_velocity_hasDerivAt parameter space).deriv, smul_smul,
    inv_mul_cancel₀ (clockRate_pos parameter).ne', one_smul]

theorem vorticity_action_unscale (parameter : ℝ) (space : PhysicalSpace) :
    (clockRate parameter)⁻¹ • deriv (fun sample => spatialField (vorticity sample) space) parameter =
      spatialField (vorticityAction parameter) space := by
  rw [(physical_vorticity_hasDerivAt parameter space).deriv, smul_smul,
    inv_mul_cancel₀ (clockRate_pos parameter).ne', one_smul]

end
end SaturationMonoid.NavierStokes.NativeWholeHistoryAction
