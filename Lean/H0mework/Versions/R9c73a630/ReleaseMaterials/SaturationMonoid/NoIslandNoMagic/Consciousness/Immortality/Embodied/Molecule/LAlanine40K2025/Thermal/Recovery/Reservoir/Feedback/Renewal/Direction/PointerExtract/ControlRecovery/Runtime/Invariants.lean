import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime.Runtime
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

def PaidBalance (state : process.State) : Prop :=
  Live.freeEnergy (currentMaterial state.current).quantum+Live.entropyProduction (currentMaterial state.current).quantum+
    receiverEnergy state.current=Live.freeEnergy ControlRecovery.origin+Live.entropyProduction ControlRecovery.origin+
      Extract.Port.kinetic ControlRecovery.material.momentum

def RemainingBalance (state : process.State) : Prop :=
  donorRemainingOf (historicalSupply state.current)=donorRemainingOf (suppliedBlock ControlRecovery.origin)

def MemoryBalance (state : process.State) : Prop := decodedMemory state.current=oneRead ControlRecovery.origin.joint

def ReceiverBalance (state : process.State) : Prop :=
  match state.current with
  | .ingress => ControlRecovery.material.momentum=0
  | .running material => material.momentum=Receiver.output.momentum

def invariantLaw : SourceNativeGeneratedInvariantLaw process :=
  .create (fun state => PLift (PaidBalance state ∧ RemainingBalance state ∧ MemoryBalance state ∧ ReceiverBalance state))
    ⟨⟨rfl,rfl,rfl,Receiver.source_zero⟩⟩
    (fun state previous => ⟨by
      refine ⟨?_,(next_remaining state.current).trans previous.down.2.1,
        (next_memory state.current).trans previous.down.2.2.1,?_⟩
      · change Live.freeEnergy (currentMaterial (nextCurrent state.current)).quantum+
          Live.entropyProduction (currentMaterial (nextCurrent state.current)).quantum+receiverEnergy (nextCurrent state.current)=
          Live.freeEnergy ControlRecovery.origin+Live.entropyProduction ControlRecovery.origin+
            Extract.Port.kinetic ControlRecovery.material.momentum
        have paid := previous.down.1
        unfold PaidBalance at paid
        linarith only [paid,next_net_account state.current]
      · have receiver := previous.down.2.2.2
        change match nextCurrent state.current with
          | .ingress => ControlRecovery.material.momentum=0
          | .running material => material.momentum=Receiver.output.momentum
        cases currentEq : state.current with
        | ingress => rfl
        | running material =>
          change material.momentum=Receiver.output.momentum
          unfold ReceiverBalance at receiver
          rw [currentEq] at receiver
          exact receiver⟩)

theorem runtime_invariants (runtime : LivingRuntimeState process) :
    PaidBalance runtime.state ∧ RemainingBalance runtime.state ∧ MemoryBalance runtime.state ∧ ReceiverBalance runtime.state := by
  have holds (state : process.State) (reachable : SourceNativeRuntimeReachableAt process state) :
      PaidBalance state ∧ RemainingBalance state ∧ MemoryBalance state ∧ ReceiverBalance state := by
    induction reachable with
    | initial => exact invariantLaw.initialAt.down
    | @step state _ previous => exact (invariantLaw.advanceAt state ⟨previous⟩).down
  exact holds runtime.state runtime.reachable

theorem all_finite_paid (depth : Nat) :
    PaidBalance (process.stateAfter depth) ∧ RemainingBalance (process.stateAfter depth) ∧
      MemoryBalance (process.stateAfter depth) ∧ ReceiverBalance (process.stateAfter depth) :=
  (invariantLaw.generatedAt depth).down

theorem runtime_complete_account (runtime : LivingRuntimeState process) :
    Live.freeEnergy (currentMaterial runtime.state.current).quantum+
      Live.entropyProduction (currentMaterial runtime.state.current).quantum+receiverEnergy runtime.state.current=
    Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+Live.measurementWork Live.initial+
      responseWork receivedState+responseWork received+Weak.pulseWork Weak.origin+Extract.pulseWork Weak.execution+
        responseWork Replenish.origin := by
  have paid := (runtime_invariants runtime).1
  have inherited := Replenish.Runtime.complete_account Replenish.Runtime.afterSecond
  change Live.freeEnergy ControlRecovery.origin+Live.entropyProduction ControlRecovery.origin+
    Extract.Port.kinetic ControlRecovery.material.momentum=_ at inherited
  exact paid.trans inherited

theorem runtime_complete_debit (runtime : LivingRuntimeState process) :
    donorRemainingOf (historicalSupply runtime.state.current)+Replenish.Registered.transfer+
      Weak.transfer+supplyTransfer received+supplyTransfer receivedState=donorRemainingOf (suppliedBlock receivedState) := by
  have paid := (runtime_invariants runtime).2.1
  change donorRemainingOf (historicalSupply runtime.state.current)=donorRemainingOf (suppliedBlock ControlRecovery.origin) at paid
  rw [paid]
  exact Replenish.Runtime.complete_debit Replenish.Runtime.afterSecond

theorem runtime_finite_budget (runtime : LivingRuntimeState process) :
    Replenish.Registered.transfer+Weak.transfer+supplyTransfer received+supplyTransfer receivedState ≤
      donorRemainingOf (suppliedBlock receivedState) := by
  have nonnegative := (remaining_range (currentMaterial runtime.state.current).quantum).1
  change 0 ≤ donorRemainingOf (historicalSupply runtime.state.current) at nonnegative
  linarith only [runtime_complete_debit runtime,nonnegative]

theorem runtime_receiver_stored (runtime : LivingRuntimeState process) :
    (currentMaterial runtime.tick.next.state.current).momentum=Receiver.output.momentum :=
  (runtime_invariants runtime.tick.next).2.2.2

theorem runtime_receiver_positive (runtime : LivingRuntimeState process) :
    (2/25 : ℝ) < receiverEnergy runtime.tick.next.state.current := by
  unfold receiverEnergy
  rw [runtime_receiver_stored]
  have source := Receiver.output_kinetic
  have zero : Extract.Port.kinetic ControlRecovery.material.momentum=0 := by
    rw [Receiver.source_zero]
    exact abs_zero
  rw [zero,sub_zero] at source
  exact source

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
