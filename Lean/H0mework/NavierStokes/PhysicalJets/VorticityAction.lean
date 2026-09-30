import H0mework.NavierStokes.PhysicalJets.VorticityControl
import H0mework.NavierStokes.Accumulation.WholeActionTube

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeUnifiedVorticityAction

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeActionTube
open NativeReceiptTimeProfile NativeMixedTimeSpace NativeTimeJetCarrier NativeFullOrderSynthesis NativeStressSource
open NativeTimeChartPhysicalAction

noncomputable section

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
  {receipt : WholeContinuousMildSerrinReceipt nu initial duration}

def rate (window : Window receipt) (actual : ℝ) : ComplexVorticityHilbertState :=
  (factor window)⁻¹ • readProfile (NativeReceiptSpacetime.vorticityFamily window 1)
    (NativeReceiptSpacetime.inverse window actual)

theorem state_hasDerivWithinAt (window : Window receipt) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) :
    HasDerivWithinAt (NativeReceiptSpacetime.state receipt) (rate window actual)
      (Icc window.first window.last) actual := by
  have source := NativePolynomialObservations.curl_evolves (jets window) (jets_evolve window) 0
    ⟨NativeReceiptSpacetime.inverse window actual, NativeReceiptSpacetime.inverse_mem window actual inside⟩
  have coordinate : HasDerivWithinAt (NativeReceiptSpacetime.inverse window) (factor window)⁻¹
      (Icc window.first window.last) actual := by
    convert! (((hasDerivAt_id actual).sub_const window.first).div_const (factor window)).hasDerivWithinAt using 1
    simp only [one_div]
  have written := source.scomp actual coordinate (NativeReceiptSpacetime.inverse_mem window)
  change HasDerivWithinAt (fun time => readProfile (NativeReceiptSpacetime.vorticityFamily window 0)
    (NativeReceiptSpacetime.inverse window time)) (rate window actual) (Icc window.first window.last) actual at written
  exact written.congr_of_mem
    (fun time member => (NativeReceiptSpacetime.vorticity_read window time member).symm) inside

theorem state_hasDerivAt (window : Window receipt) (actual : ℝ)
    (inside : actual ∈ Ioo window.first window.last) :
    HasDerivAt (NativeReceiptSpacetime.state receipt) (rate window actual) actual :=
  (state_hasDerivWithinAt window actual ⟨inside.1.le, inside.2.le⟩).hasDerivAt (Icc_mem_nhds inside.1 inside.2)

theorem rate_row (window : Window receipt) (actual : ℝ) (inside : actual ∈ Ioo window.first window.last)
    (wave : IntegerWavevector) :
    rate window actual wave =
      wholeLatticeVorticityFourierTangentAt nu.coeff (NativeReceiptSpacetime.state receipt actual) wave := by
  have source := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivAt
    actual (state_hasDerivAt window actual inside)
  have physical : actual ∈ Ioo (0 : ℝ) duration :=
    ⟨window.first_nonnegative.trans_lt inside.1, inside.2.trans_le window.last_le⟩
  by_cases nonzero : wave ≠ 0
  · have original := receipt_vorticity_hasDerivAt receipt wave nonzero ⟨actual, physical.1.le, physical.2.le⟩
    rw [← NativeReceiptSpacetime.state_on_interval receipt ⟨actual, physical.1.le, physical.2.le⟩] at original
    apply source.unique
    apply original.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds physical.1 physical.2] with time member
    change NativeReceiptSpacetime.state receipt time wave = _
    rw [NativeReceiptSpacetime.state_on_interval receipt ⟨time, member.1.le, member.2.le⟩]
    exact wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath receipt wave nonzero _
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    rw [wholeLatticeVorticityFourierTangentAt_zero _ _
      (NativeReceiptSpacetime.state_transverse receipt actual) (NativeReceiptSpacetime.state_zero receipt actual)]
    have constant : (fun time => NativeReceiptSpacetime.state receipt time 0) = fun _ => 0 :=
      funext (NativeReceiptSpacetime.state_zero receipt)
    change HasDerivAt (fun time => NativeReceiptSpacetime.state receipt time 0) (rate window actual 0) actual at source
    rw [constant] at source
    exact source.unique (hasDerivAt_const actual 0)

theorem physical_hasDerivWithinAt (window : Window receipt) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) (space : PhysicalSpace) :
    HasDerivWithinAt (fun time => spatialField (NativeReceiptSpacetime.state receipt time) space)
      (spatialField (rate window actual) space) (Icc window.first window.last) actual := by
  have source := profileWord_hasDerivWithinAt
    (NativeReceiptSpacetime.vorticityFamily window 0) (NativeReceiptSpacetime.vorticityFamily window 1)
    (NativePolynomialObservations.curl_evolves (jets window) (jets_evolve window) 0)
    0 (fun empty => Fin.elim0 empty) space
    ⟨NativeReceiptSpacetime.inverse window actual, NativeReceiptSpacetime.inverse_mem window actual inside⟩
  simp only [profileWord, profileField, iteratedFDeriv_zero_apply] at source
  have coordinate : HasDerivWithinAt (NativeReceiptSpacetime.inverse window) (factor window)⁻¹
      (Icc window.first window.last) actual := by
    convert! (((hasDerivAt_id actual).sub_const window.first).div_const (factor window)).hasDerivWithinAt using 1
    simp only [one_div]
  have written := source.scomp actual coordinate (NativeReceiptSpacetime.inverse_mem window)
  rw [rate, spatialField_real_smul]
  exact written.congr_of_mem
    (fun time member => by
      simp only [Function.comp_apply, profileWord, profileField, iteratedFDeriv_zero_apply]
      rw [NativeReceiptSpacetime.vorticity_read window time member]) inside

theorem physical_hasDerivAt (window : Window receipt) (actual : ℝ)
    (inside : actual ∈ Ioo window.first window.last) (space : PhysicalSpace) :
    HasDerivAt (fun time => spatialField (NativeReceiptSpacetime.state receipt time) space)
      (spatialField (rate window actual) space) actual :=
  (physical_hasDerivWithinAt window actual ⟨inside.1.le, inside.2.le⟩ space).hasDerivAt (Icc_mem_nhds inside.1 inside.2)

open NativeFinitePrefixTimeChart (field sourcePoint contactTime nextContactTime)
open NativeSourceUnifiedActionSplice (target target_is_original_next)
open RationalVorticityEvaluator

def sourceRate (index : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  rate (NativeFinitePrefixTimeChart.window index) actual

theorem source_rate_row (index : ℕ) (actual : ℝ)
    (inside : actual ∈ Ioo (0 : ℝ) (NativeFinitePrefixTimeChart.duration index)) (wave : IntegerWavevector) :
    sourceRate index actual wave = wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff
      (NativeReceiptSpacetime.state (NativeFinitePrefixTimeChart.receipt index) actual) wave :=
  rate_row (NativeFinitePrefixTimeChart.window index) actual inside wave

theorem unified_curl_physical_hasDerivAt (index : ℕ) (actual : ℝ)
    (inside : actual ∈ Ioo (0 : ℝ) (NativeFinitePrefixTimeChart.duration index)) (space : PhysicalSpace) :
    HasDerivAt (fun time => PhysicsCore.Stage9CU.Fluid.curl (field index) (sourcePoint index time space))
      (spatialField (sourceRate index actual) space) actual := by
  have source := physical_hasDerivAt (NativeFinitePrefixTimeChart.window index) actual inside space
  apply source.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds inside.1 inside.2] with time member
  rw [NativeTimeChartVorticityReadout.unified_curl_physical_read index time member,
    NativeReceiptSpacetime.state_on_interval (NativeFinitePrefixTimeChart.receipt index)
      ⟨time, member.1.le, member.2.le⟩]

theorem target_initial_rate (index : ℕ) (wave : IntegerWavevector) :
    sourceRate index (contactTime index) wave =
      wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (target index).initialState wave := by
  rw [source_rate_row index _ (NativeFinitePrefixTimeChart.contactTime_mem index),
    NativeReceiptSpacetime.state_on_interval (NativeFinitePrefixTimeChart.receipt index)
      ⟨contactTime index, (NativeFinitePrefixTimeChart.contactTime_mem index).1.le,
        (NativeFinitePrefixTimeChart.contactTime_mem index).2.le⟩,
    NativeFinitePrefixTimeChart.contact_state, target_is_original_next]
  rfl

theorem target_contact_rate (index : ℕ) (wave : IntegerWavevector) :
    sourceRate index (nextContactTime index) wave =
      wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (target index).contact.physicalState wave := by
  rw [source_rate_row index _ (NativeFinitePrefixTimeChart.nextContactTime_mem index),
    NativeReceiptSpacetime.state_on_interval (NativeFinitePrefixTimeChart.receipt index)
      ⟨nextContactTime index, (NativeFinitePrefixTimeChart.nextContactTime_mem index).1.le,
        (NativeFinitePrefixTimeChart.nextContactTime_mem index).2.le⟩,
    NativeFinitePrefixTimeChart.next_contact_state, target_is_original_next]

end
end SaturationMonoid.NavierStokes.NativeUnifiedVorticityAction
