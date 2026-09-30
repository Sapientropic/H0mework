import H0mework.Versions.X.NavierStokes.WholeHistory.WholeHistoryPhysical

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeWholeHistoryPhysicalAction

open Set Filter
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineHolonomicField
open PhysicsCore.Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open NativeFullOrderSynthesis NativeWholeHistoryClock NativeWholeHistoryField NativeWholeHistoryAction
open NativeWholeHistoryCurrent (matter dual spatial_read temporal_read)
open NativeSourceUnifiedActionSplice (target target_is_original_next)
open RationalVorticityEvaluator

noncomputable section

theorem physical_cover (actual : ℝ) (inside : actual ∈ physicalDomain) :
    actual < duration (cover (inverseTime actual)) := by
  simpa only [physicalTime_inverse actual inside] using cover_spec (inverseTime actual)

theorem vorticity_physical_read (length : ℕ) (actual : ℝ) (inside : actual ∈ Ioc (0 : ℝ) (duration length)) :
    vorticity (inverseTime actual) = NativeReceiptSpacetime.state (receipt length) actual := by
  have domain := physicalDomain_of_le_duration length actual inside.1 inside.2
  have before : physicalTime (inverseTime actual) ≤ duration length := by
    rw [physicalTime_inverse actual domain]
    exact inside.2
  rw [vorticity_read length _ before, physicalTime_inverse actual domain]

theorem field_hasDerivAt (actual : ℝ) (inside : actual ∈ physicalDomain) (space : PhysicalSpace) :
    HasDerivAt (fun time => field (sourcePoint time space))
      (spatialField (momentum (inverseTime actual)) space) actual := by
  let length := cover (inverseTime actual)
  have source := NativeTimeChartPhysicalAction.receipt_physical_hasDerivAt (window length) actual
    ⟨inside.1, physical_cover actual inside⟩ space
  have rate : NativeReceiptSpacetime.timeJet (window length) 1 actual = momentum (inverseTime actual) := by
    rw [momentum, physicalTime_inverse actual inside]
  rw [rate] at source
  apply source.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds inside.1 (physical_cover actual inside)] with time member
  exact physical_read length time ⟨member.1, member.2.le⟩ space

theorem spatial_current_hasDerivAt (actual : ℝ) (inside : actual ∈ physicalDomain)
    (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivAt (fun time => current matter dual direction.succ (sourcePoint time space))
      (spatialField (momentum (inverseTime actual)) space direction) actual := by
  rw [spatial_read]
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) direction).hasFDerivAt.comp_hasDerivAt actual
    (field_hasDerivAt actual inside space)

theorem temporal_current_hasDerivAt (actual : ℝ) (inside : actual ∈ physicalDomain) (space : PhysicalSpace) :
    HasDerivAt (fun time => current matter dual 0 (sourcePoint time space))
      (inner ℝ (field (sourcePoint actual space)) (spatialField (momentum (inverseTime actual)) space) / 4) actual := by
  simp only [temporal_read]
  convert! ((field_hasDerivAt actual inside space).norm_sq.div_const 8).const_add 2 using 1
  ring

theorem unified_curl_hasDerivAt (actual : ℝ) (inside : actual ∈ physicalDomain) (space : PhysicalSpace) :
    HasDerivAt (fun time => PhysicsCore.Stage9CU.Fluid.curl field (sourcePoint time space))
      (spatialField (vorticityAction (inverseTime actual)) space) actual := by
  let length := cover (inverseTime actual)
  have source := NativeUnifiedVorticityAction.physical_hasDerivAt (window length) actual
    ⟨inside.1, physical_cover actual inside⟩ space
  have rate : NativeUnifiedVorticityAction.rate (window length) actual = vorticityAction (inverseTime actual) := by
    rw [vorticityAction, physicalTime_inverse actual inside]
  rw [rate] at source
  apply source.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds inside.1 (physical_cover actual inside)] with time member
  rw [NativeWholeHistoryCurl.unified_curl_original, sourcePoint_time, sourcePoint_space,
    vorticity_physical_read length time ⟨member.1, member.2.le⟩]

theorem target_initial_state (index : ℕ) :
    vorticity (inverseTime (duration index)) = (target index).initialState := by
  rw [vorticity_physical_read (index + 2) _
    ⟨duration_pos index, duration_strictMono.monotone (Nat.le_add_right index 2)⟩,
    NativeReceiptSpacetime.state_on_interval (receipt (index + 2))
      ⟨duration index, (duration_pos index).le, duration_strictMono.monotone (Nat.le_add_right index 2)⟩,
    target_is_original_next]
  exact NativeFinitePrefixTimeChart.contact_state index

theorem target_contact_state (index : ℕ) :
    vorticity (inverseTime (duration (index + 1))) = (target index).contact.physicalState := by
  rw [target_initial_state (index + 1), target_is_original_next, target_is_original_next]
  rfl

theorem target_initial_momentum (index : ℕ) (wave : IntegerWavevector) :
    momentum (inverseTime (duration index)) wave = biotSavartVelocityCoefficient wave
      (wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (target index).initialState wave) := by
  rw [momentum_row, target_initial_state]

theorem target_contact_momentum (index : ℕ) (wave : IntegerWavevector) :
    momentum (inverseTime (duration (index + 1))) wave = biotSavartVelocityCoefficient wave
      (wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (target index).contact.physicalState wave) := by
  rw [momentum_row, target_contact_state]

theorem target_initial_vorticityAction (index : ℕ) (wave : IntegerWavevector) :
    vorticityAction (inverseTime (duration index)) wave =
      wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (target index).initialState wave := by
  rw [vorticityAction_row, target_initial_state]

theorem target_contact_vorticityAction (index : ℕ) (wave : IntegerWavevector) :
    vorticityAction (inverseTime (duration (index + 1))) wave =
      wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (target index).contact.physicalState wave := by
  rw [vorticityAction_row, target_contact_state]

end
end SaturationMonoid.NavierStokes.NativeWholeHistoryPhysicalAction
