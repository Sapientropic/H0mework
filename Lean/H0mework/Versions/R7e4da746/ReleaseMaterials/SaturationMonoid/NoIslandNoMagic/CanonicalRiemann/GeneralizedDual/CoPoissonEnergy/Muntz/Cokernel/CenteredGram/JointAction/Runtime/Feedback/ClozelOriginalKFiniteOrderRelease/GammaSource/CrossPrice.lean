import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.LogAction

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace CenteredGram.IntegralGraphJointAction.OriginalRSourceJointContact
open Complex Filter FourierTransform MeasureTheory Set BurnolPhysicalState
open scoped InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.FiniteLogCounting
open OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.ConductorDual OriginalGamma.Source.KGamma
open OriginalGamma.Source.JointLogConductor
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource
open private log_pair_of_weak from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
open private log_pair_pairing from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorStrongSource
open private logPair_smul logPair_sub from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource

local notation "F" => fourierL2
local notation "K" => burnolCompletedMellinRieszVector

private theorem position_from_frequency (value gamma frequencyLog : BurnolL2)
    (graph : GammaPair value gamma)
    (frequency : LogPair (fourierL2.symm value) frequencyLog) :
    LogPair value (gamma - F frequencyLog) := by
  apply log_pair_of_weak
  intro test
  have source := graph test
  have paired := log_pair_pairing _ _ _ _
    (original_log_schwartz_domain (𝓕⁻ test)) frequency
  have inverseRead : (𝓕⁻ test).toLp 2 volume = fourierL2.symm (test.toLp 2 volume) := by
    apply fourierL2.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    change 𝓕 ((𝓕⁻ test).toLp 2 volume) = test.toLp 2 volume
    rw [SchwartzMap.toLp_fourier_eq, FourierTransform.fourier_fourierInv_eq]
  rw [wholeConductorTest, inner_add_left, fourierL2.inner_map_eq_flip,
    paired, inverseRead] at source
  have forwardRead := fourierL2.inner_map_map (fourierL2.symm (test.toLp 2 volume)) frequencyLog
  rw [LinearIsometryEquiv.apply_symm_apply] at forwardRead
  rw [inner_sub_right, forwardRead]
  linear_combination source

private theorem gammaField_power (coordinate : BurnolCompletedMellinCoordinate) (order : Nat) :
    gammaField coordinate order =
      ((burnolDirectRightResolventCLM coordinate)^order).adjoint (gammaCombo coordinate) := by
  induction order with
  | zero =>
    change gammaCombo coordinate =
      (star (1 : BurnolL2 →L[ℂ] BurnolL2)) (gammaCombo coordinate)
    rw [star_one]
    rfl
  | succ order previous =>
    rw [gammaField, ←sourceStep_actual, previous]
    change _ = (star ((burnolDirectRightResolventCLM coordinate)^(order+1))) (gammaCombo coordinate)
    rw [pow_succ, star_mul, mul_apply_eq_comp]
    rfl

def initialFrequencyLog (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  jQuarterAmplitude coordinate • actualKernelFrequencyLog coordinate -
    hQuarterAmplitude coordinate • actualKernelPositionLog coordinate

private theorem initial_frequency_source (coordinate : BurnolCompletedMellinCoordinate) :
    LogPair (fourierL2.symm (sourceField coordinate 0)) (initialFrequencyLog coordinate) := by
  rw [sourceField, sourceKernelCombo_actual, map_sub, map_smul, map_smul,
    fourierL2.symm_apply_apply]
  exact logPair_sub _ _ _ _
    (logPair_smul _ _ _ (actual_kernel_complete_log_sources coordinate).2)
    (logPair_smul _ _ _ (actual_kernel_complete_log_sources coordinate).1)

def frequencyLogField (coordinate : BurnolCompletedMellinCoordinate) : Nat → BurnolL2
  | 0 => initialFrequencyLog coordinate
  | next+1 => burnolDirectRightResolvent (star coordinate.value/2)
      (frequencyLogField coordinate next) -
    BurnolPhysicalState.OriginalRSourceJointContact.LogAction.directLogMoment
      (star coordinate.value/2) (fourierL2.symm (sourceField coordinate next))

def positionLogField (coordinate : BurnolCompletedMellinCoordinate) (order : Nat) : BurnolL2 :=
  gammaField coordinate order - F (frequencyLogField coordinate order)

private theorem frequency_source (coordinate : BurnolCompletedMellinCoordinate) (order : Nat) :
    LogPair (fourierL2.symm (sourceField coordinate order)) (frequencyLogField coordinate order) := by
  induction order with
  | zero => exact initial_frequency_source coordinate
  | succ order previous =>
    have right : 1/4 < (star coordinate.value/2).re := by
      rw [Complex.div_re]
      norm_num
      linarith [coordinate.rightHalf]
    have actual := BurnolPhysicalState.OriginalRSourceJointContact.LogAction.actual_direct_R_log
      (star coordinate.value/2) right _ _ previous
    change LogPair (fourierL2.symm (sourceStep coordinate (sourceField coordinate order)))
      (frequencyLogField coordinate (order+1))
    rw [sourceStep_inverseFourier]
    exact actual

/-- Both log domains and the time-moment fee are generated by the same original source recursion. -/
theorem actual_source_two_logs (coordinate : BurnolCompletedMellinCoordinate) (order : Nat) :
    LogPair (sourceField coordinate order) (positionLogField coordinate order) ∧
      LogPair (fourierL2.symm (sourceField coordinate order)) (frequencyLogField coordinate order) := by
  have frequency := frequency_source coordinate order
  exact ⟨position_from_frequency _ _ _ (actual_source_graph coordinate order) frequency, frequency⟩

private theorem complete_green (coordinate : BurnolCompletedMellinCoordinate) (order : Nat) :
    inner ℂ (actualGammaKernel coordinate) (sourceField coordinate order) =
      inner ℂ (((burnolDirectRightResolventCLM coordinate)^order) (K coordinate : BurnolL2))
        (gammaCombo coordinate) := by
  have actual := whole_conductor_dual
    (K coordinate : BurnolL2) (actualGammaKernel coordinate)
    (actualKernelPositionLog coordinate) (actualKernelFrequencyLog coordinate)
    (sourceField coordinate order) (gammaField coordinate order)
    (positionLogField coordinate order) (frequencyLogField coordinate order)
    (actual_gamma_original_kernel coordinate) (actual_source_graph coordinate order)
    (actual_kernel_complete_log_sources coordinate).1 (actual_kernel_complete_log_sources coordinate).2
    (actual_source_two_logs coordinate order).1 (actual_source_two_logs coordinate order).2
  rw [gammaField_power, ContinuousLinearMap.adjoint_inner_right] at actual
  exact actual

variable (observation : GeneratedRiemannZeroObservation)
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate

/-- The complete original-m cross action retains its Pa, Q, and every outside fee. -/
theorem actual_complete_cross_price :
    inner ℂ (actualGammaKernel c) (sourceQ observation half) -
      inner ℂ (((burnolDirectRightResolventCLM c)^m) (K c : BurnolL2))
        (OriginalKCombCofinalPaAction.Q (gammaCombo c) : BurnolL2) =
    -inner ℂ (actualGammaKernel c)
        (OriginalKFiniteOrderRelease.UnitPowerSource.paPowerField observation half : BurnolL2) -
      ∑ j ∈ Finset.range m, sourceCoefficient c m j *
        inner ℂ (actualGammaKernel c) (logOutsideColumn c j) +
      inner ℂ (((burnolDirectRightResolventCLM c)^m) (K c : BurnolL2))
        (gammaCombo c - (OriginalKCombCofinalPaAction.Q (gammaCombo c) : BurnolL2)) := by
  have actual := complete_green c m
  rw [actual_sourceField, source_full_inventory] at actual
  simp only [inner_add_right, sourceOutside, inner_sum, inner_smul_right] at actual
  rw [inner_sub_right]
  linear_combination actual

end CenteredGram.IntegralGraphJointAction.OriginalRSourceJointContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
