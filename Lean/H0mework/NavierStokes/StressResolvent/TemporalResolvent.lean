import H0mework.NavierStokes.StressResolvent.ResolventResidual
import H0mework.NavierStokes.VelocityGalerkin.InitialConvergence

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeTemporalResolvent

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeSourceResolvent NativeFiniteActionResolvent NativeCommonAdvectorAction NativeRawStressAction
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeRecoveryTimeGramAction

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def zeroTime : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩

def transition (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (last : Icc (0 : ℝ) 1) :
    physicalSpace (modes stress index) ≃ₗ[ℝ] physicalSpace (modes stress index) :=
  physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index (.fixed last)) (advector_reality stress pointLe index (.fixed last)) last.1 last.2.1

def advance (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (last : Icc (0 : ℝ) 1) :
    physicalSpace (modes stress index) :=
  transition stress pointLe index last (load stress pointLe index (.fixed zeroTime))

def workRemainder (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (last : Icc (0 : ℝ) 1) :
    physicalSpace (modes stress index) :=
  load stress pointLe index (.fixed last) - load stress pointLe index (.fixed zeroTime) -
    last.1 • physicalOperator (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
      (advector stress pointLe index (.fixed last)) (advector_reality stress pointLe index (.fixed last))
      (load stress pointLe index (.fixed last))

theorem remainder_actual_work (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (last : Icc (0 : ℝ) 1) :
    (workRemainder stress pointLe index last).1 =
      (∫ time in (0 : ℝ)..last.1, rawRate stress index time) - last.1 • rawRate stress index last.1 := by
  have written : (∫ time in (0 : ℝ)..last.1, rawRate stress index time) =
      rawField stress index last.1 - rawField stress index 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun time inside => rawField_hasDerivAt stress index time
        ((uIcc_subset_Icc zeroTime.2 last.2) inside))
      (((rawRate_continuousOn stress index).mono (uIcc_subset_Icc zeroTime.2 last.2)).intervalIntegrable)
  rw [written]
  change rawField stress index last.1 - rawField stress index 0 - last.1 •
    sourceOperator stress index last.1 (rawField stress index last.1) = _
  rw [source_diagonal stress index last.1 last.2]

theorem transition_reconstructs (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (last : Icc (0 : ℝ) 1) :
    advance stress pointLe index last + transition stress pointLe index last (workRemainder stress pointLe index last) =
      load stress pointLe index (.fixed last) := by
  rw [advance, ← map_add]
  let A := physicalOperator (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index (.fixed last)) (advector_reality stress pointLe index (.fixed last))
  have sum : load stress pointLe index (.fixed zeroTime) + workRemainder stress pointLe index last =
      implicitMap A last.1 (load stress pointLe index (.fixed last)) := by
    dsimp only [workRemainder, implicitMap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, A]
    abel
  rw [sum]
  exact (LinearEquiv.ofInjectiveEndo (implicitMap A last.1)
    (implicitMap_injective A _ (pairing_faithful _) (physicalOperator_dissipative _ _ _ _ _ _) last.1 last.2.1)).symm_apply_apply _

def advancedEndpoint (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (last : Icc (0 : ℝ) 1) : State :=
  puncturedEuclideanize (advance stress pointLe index last).1

theorem advance_budget (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (last : Icc (0 : ℝ) 1) :
    ‖coefficients (modes stress index) (advance stress pointLe index last)‖ ^ 2 +
      ‖coefficients (modes stress index) (load stress pointLe index (.fixed zeroTime) - advance stress pointLe index last)‖ ^ 2 +
      2 * last.1 * nu.coeff * curlPair (modes stress index) (advance stress pointLe index last).1
        (advance stress pointLe index last).1 ≤ ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 :=
  (physicalResolver_balance (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index (.fixed last)) (advector_reality stress pointLe index (.fixed last)) last.1 last.2.1
    (load stress pointLe index (.fixed zeroTime))).symm.le.trans
      (pow_le_pow_left₀ (norm_nonneg _) (load_norm_le stress pointLe index (.fixed zeroTime)) 2)

theorem advance_strong_limit (stress : StressAt escape) (pointLe : point ≤ 1)
    (last : Icc (0 : ℝ) 1) (positive : 0 < last.1) :
    ∃ target : State, Tendsto (fun index => advancedEndpoint stress pointLe index last)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 / (2 * last.1 * nu.coeff) := by
  apply exists_strong_limit_of_sum (fun index => advancedEndpoint stress pointLe index last)
    (generated stress pointLe).refinement _
    (fun _ => physical_curl_summable _ _)
  intro index
  rw [advancedEndpoint, physical_curl_sum _ (modes_zero stress index)]
  apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) positive) nu.coeff_pos)).mpr
  have source := advance_budget stress pointLe index last
  nlinarith [sq_nonneg ‖coefficients (modes stress index) (advance stress pointLe index last)‖,
    sq_nonneg ‖coefficients (modes stress index) (load stress pointLe index (.fixed zeroTime) - advance stress pointLe index last)‖]

end
end SaturationMonoid.NavierStokes.NativeTemporalResolvent
