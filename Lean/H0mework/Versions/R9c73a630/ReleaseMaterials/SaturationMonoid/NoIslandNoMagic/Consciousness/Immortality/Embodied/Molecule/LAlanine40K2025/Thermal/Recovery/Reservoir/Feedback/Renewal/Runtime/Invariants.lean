import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Runtime.Runtime

/-! # Energy and the unspent donor remainder survive canonical continuation -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Resource
noncomputable section

def PaidBalance (state : process.State) : Prop :=
  Live.entropyProduction (currentState state.current) + Live.freeEnergy (currentState state.current) =
    Live.entropyProduction received + Live.freeEnergy received + accumulatedWork state.current

def RemainingBalance (state : process.State) : Prop :=
  donorRemainingOf (suppliedBlock (currentState state.current)) + accumulatedTransfer state.current =
    donorRemainingOf (suppliedBlock received)

def invariantLaw : SourceNativeGeneratedInvariantLaw process :=
  .create (fun state => PLift (PaidBalance state ∧ RemainingBalance state))
    ⟨⟨(add_zero _).symm, add_zero _⟩⟩
    (fun state previous => ⟨by
      constructor
      · change Live.entropyProduction (currentState (nextCurrent state.current)) +
          Live.freeEnergy (currentState (nextCurrent state.current)) =
          Live.entropyProduction received + Live.freeEnergy received +
            accumulatedWork (nextCurrent state.current)
        have paid := previous.down.1
        change Live.entropyProduction (currentState state.current) +
          Live.freeEnergy (currentState state.current) =
          Live.entropyProduction received + Live.freeEnergy received +
            accumulatedWork state.current at paid
        linarith [next_net_account state.current, accumulated_work_next state.current]
      · exact (next_remaining state.current).trans previous.down.2⟩)

theorem runtime_invariants (runtime : LivingRuntimeState process) :
    PaidBalance runtime.state ∧ RemainingBalance runtime.state := by
  have holds (state : process.State) (reachable : SourceNativeRuntimeReachableAt process state) :
      PaidBalance state ∧ RemainingBalance state := by
    induction reachable with
    | initial => exact invariantLaw.initialAt.down
    | @step state _ previous => exact (invariantLaw.advanceAt state ⟨previous⟩).down
  exact holds runtime.state runtime.reachable

theorem all_finite_paid (depth : Nat) :
    PaidBalance (process.stateAfter depth) ∧ RemainingBalance (process.stateAfter depth) :=
  (invariantLaw.generatedAt depth).down

theorem runtime_complete_account (runtime : LivingRuntimeState process) :
    Live.entropyProduction (currentState runtime.state.current) +
      Live.freeEnergy (currentState runtime.state.current) =
    Live.entropyProduction Live.initial + Live.freeEnergy Live.initial +
      Live.measurementWork Live.initial + responseWork receivedState +
        accumulatedWork runtime.state.current := by
  have paid := (runtime_invariants runtime).1
  have parent := firstState_completeAccount
  change Live.entropyProduction received + Live.freeEnergy received = _ at parent
  exact paid.trans (congrArg (fun value => value + accumulatedWork runtime.state.current) parent)

theorem runtime_complete_debit (runtime : LivingRuntimeState process) :
    donorRemainingOf (suppliedBlock (currentState runtime.state.current)) +
      accumulatedTransfer runtime.state.current + supplyTransfer receivedState =
      donorRemainingOf (suppliedBlock receivedState) := by
  have paid := (runtime_invariants runtime).2
  change donorRemainingOf (suppliedBlock (currentState runtime.state.current)) +
    accumulatedTransfer runtime.state.current = donorRemainingOf (suppliedBlock received) at paid
  rw [paid]
  exact response_remaining_debit receivedState

theorem runtime_finite_budget (runtime : LivingRuntimeState process) :
    accumulatedTransfer runtime.state.current + supplyTransfer receivedState ≤
      donorRemainingOf (suppliedBlock receivedState) := by
  linarith [runtime_complete_debit runtime, (remaining_range (currentState runtime.state.current)).1]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
