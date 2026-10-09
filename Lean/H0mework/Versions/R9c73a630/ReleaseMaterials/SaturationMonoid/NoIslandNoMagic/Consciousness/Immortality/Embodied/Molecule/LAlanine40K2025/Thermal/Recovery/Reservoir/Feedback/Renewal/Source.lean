import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Dynamics

/-! # The feedback target supplies its next execution from retained resources

This fixed source continues the original seven-q full joint, applies the registered feedback
Hamiltonian once, and hands the resulting eight-q state to the original load action.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal

open Resource Propagation.Producer
noncomputable section

def received : Live.State := firstState
def supplied : Live.State := respondNext received
def executed : Live.State := Live.loadNext supplied

theorem received_clock : received.localClock = 7 * nativeClockStep := firstState_clock

theorem supplied_clock : supplied.localClock = 8 * nativeClockStep := by
  change received.localClock + nativeClockStep = _
  rw [received_clock]
  ring

theorem executed_clock : executed.localClock = 9 * nativeClockStep := by
  rw [executed, Live.loadNext_clock, supplied_clock]
  ring

theorem supplied_joint : supplied.joint =
    Quantum.conjugation (feedbackPulse (nativeClockStep : ℝ)) received.joint :=
  respondNext_joint received

theorem executed_joint : executed.joint =
    Quantum.conjugation (Pointer.loadPulse (nativeClockStep : ℝ)) supplied.joint :=
  Live.loadNext_joint supplied

theorem executed_body : bodyRead executed.joint =
    Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ)) (bodyRead supplied.joint) :=
  Live.loadNext_body supplied

theorem supplied_paid : supplyTransfer received ≤ donorRemainingOf (suppliedBlock received) :=
  response_paid_from_remaining received

theorem executed_remaining : donorRemainingOf (suppliedBlock executed) + supplyTransfer received =
    donorRemainingOf (suppliedBlock received) := execution_remaining_debit received

/-- Both actual feedback transfers are debited from the original conditional block exactly once. -/
theorem two_responses_paid :
    donorRemainingOf (suppliedBlock executed) + supplyTransfer received +
      supplyTransfer receivedState = donorRemainingOf (suppliedBlock receivedState) := by
  rw [executed_remaining]
  exact response_remaining_debit receivedState

theorem two_responses_bounded : supplyTransfer receivedState + supplyTransfer received ≤
    donorRemainingOf (suppliedBlock receivedState) := by
  linarith [two_responses_paid, (remaining_range executed).1]

theorem executed_net_account :
    (Live.freeEnergy executed - Live.freeEnergy received) +
      (Live.entropyProduction executed - Live.entropyProduction received) = responseWork received := by
  have supply := respondNext_netAccount received
  have load := Live.loadNext_net_account supplied
  change (Live.freeEnergy supplied - Live.freeEnergy received) +
    (Live.entropyProduction supplied - Live.entropyProduction received) = _ at supply
  change (Live.freeEnergy executed - Live.freeEnergy supplied) +
    (Live.entropyProduction executed - Live.entropyProduction supplied) = 0 at load
  linarith

theorem executed_complete_account :
    Live.entropyProduction executed + Live.freeEnergy executed =
      Live.entropyProduction Live.initial + Live.freeEnergy Live.initial +
        Live.measurementWork Live.initial + responseWork receivedState + responseWork received := by
  have old := firstState_completeAccount
  change Live.entropyProduction received + Live.freeEnergy received = _ at old
  linarith [executed_net_account]

theorem executed_pointer_memory : oneRead executed.joint = oneRead received.joint := by
  rw [executed, Live.loadNext_pointer_one, supplied, respondNext_one]

theorem executed_not_reset : executed.joint ≠ sourceInitial := by
  intro same
  have retained := executed_pointer_memory
  rw [same, sourceInitial, prepared_one_read] at retained
  have positive : 0 < oneRead received.joint := by
    rw [received, firstState, respondNext_one, receivedState_joint]
    exact sourceTarget_one_positive
  linarith

/-- Same-source material, payment, actual execution, and retained memory returned to the root. -/
structure RemainingRenewalClosure : Prop where
  inputClock : type_of% received_clock
  supplyClock : type_of% supplied_clock
  executionClock : type_of% executed_clock
  supplyJoint : type_of% supplied_joint
  executionJoint : type_of% executed_joint
  executionBody : type_of% executed_body
  supplyPayment : type_of% supplied_paid
  supplyBalance : type_of% (supply_branch_paid received)
  supplyEnvironment : type_of% (supply_branch_environment received)
  supplyBoundaryWork : type_of% (responseWork_supply_boundary received)
  loadPayment : type_of% (load_execution_account supplied)
  donorMaterial : type_of% (load_donor_material supplied)
  donorEnergy : type_of% (load_donor_total supplied)
  executionRemainder : type_of% executed_remaining
  completeDebit : type_of% two_responses_paid
  finiteBound : type_of% two_responses_bounded
  remainingRange : type_of% (remaining_range executed)
  completeEnergy : type_of% executed_complete_account
  retainedMemory : type_of% executed_pointer_memory
  noReset : type_of% executed_not_reset

theorem sourceGeneratedRemainingRenewal : RemainingRenewalClosure where
  inputClock := received_clock
  supplyClock := supplied_clock
  executionClock := executed_clock
  supplyJoint := supplied_joint
  executionJoint := executed_joint
  executionBody := executed_body
  supplyPayment := supplied_paid
  supplyBalance := supply_branch_paid received
  supplyEnvironment := supply_branch_environment received
  supplyBoundaryWork := responseWork_supply_boundary received
  loadPayment := load_execution_account supplied
  donorMaterial := load_donor_material supplied
  donorEnergy := load_donor_total supplied
  executionRemainder := executed_remaining
  completeDebit := two_responses_paid
  finiteBound := two_responses_bounded
  remainingRange := remaining_range executed
  completeEnergy := executed_complete_account
  retainedMemory := executed_pointer_memory
  noReset := executed_not_reset

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
