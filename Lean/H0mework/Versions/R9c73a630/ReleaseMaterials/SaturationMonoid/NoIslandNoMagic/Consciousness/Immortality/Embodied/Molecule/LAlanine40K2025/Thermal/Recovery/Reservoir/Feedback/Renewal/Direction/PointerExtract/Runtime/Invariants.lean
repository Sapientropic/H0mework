import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Runtime.Runtime

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

def PaidBalance (state : process.State) : Prop :=
  Live.freeEnergy (currentMaterial state.current).quantum+Live.entropyProduction (currentMaterial state.current).quantum+
    receiverEnergy state.current=Live.freeEnergy sourceEntry.quantum+Live.entropyProduction sourceEntry.quantum

def RemainingBalance (state : process.State) : Prop :=
  donorRemainingOf (historicalSupply state.current)=donorRemainingOf (suppliedBlock sourceEntry.quantum)

def MemoryBalance (state : process.State) : Prop :=
  decodedMemory state.current=oneRead sourceEntry.quantum.joint

theorem initial_receiver_zero : receiverEnergy .ingress=0 := by
  simp only [receiverEnergy,currentMaterial,sourceEntry,Extract.Port.kinetic,abs_zero]

def ReceiverProperty : ReceiverCurrent → Prop
  | .ingress => (currentMaterial .ingress).momentum=0
  | .running material => material.momentum=(advance sourceEntry).momentum

def ReceiverBalance (state : process.State) : Prop := ReceiverProperty state.current

theorem receiver_property_next (current : ReceiverCurrent) (previous : ReceiverProperty current) :
    ReceiverProperty (nextCurrent current) := by
  cases current with
  | ingress => rfl
  | running material => exact previous

def invariantLaw : SourceNativeGeneratedInvariantLaw process :=
  .create (fun state => PLift (PaidBalance state ∧ RemainingBalance state ∧ MemoryBalance state ∧ ReceiverBalance state))
    ⟨⟨by
        change Live.freeEnergy sourceEntry.quantum+Live.entropyProduction sourceEntry.quantum+receiverEnergy .ingress=_
        rw [initial_receiver_zero,add_zero],rfl,rfl,rfl⟩⟩
    (fun state previous => ⟨by
      exact ⟨(next_net_account state.current).trans previous.down.1,
        (next_remaining state.current).trans previous.down.2.1,
        (next_memory state.current).trans previous.down.2.2.1,
        receiver_property_next state.current previous.down.2.2.2⟩⟩)

theorem runtime_invariants (runtime : LivingRuntimeState process) :
    PaidBalance runtime.state ∧ RemainingBalance runtime.state ∧ MemoryBalance runtime.state ∧ ReceiverBalance runtime.state := by
  have holds (state : process.State) (reachable : SourceNativeRuntimeReachableAt process state) :
      PaidBalance state ∧ RemainingBalance state ∧ MemoryBalance state ∧ ReceiverBalance state := by
    induction reachable with
    | initial => exact invariantLaw.initialAt.down
    | @step state _ previous => exact (invariantLaw.advanceAt state ⟨previous⟩).down
  exact holds runtime.state runtime.reachable

theorem all_finite_paid (depth : Nat) :
    PaidBalance (process.stateAfter depth) ∧ RemainingBalance (process.stateAfter depth) ∧ MemoryBalance (process.stateAfter depth) ∧ ReceiverBalance (process.stateAfter depth) :=
  (invariantLaw.generatedAt depth).down

theorem runtime_complete_account (runtime : LivingRuntimeState process) :
    Live.freeEnergy (currentMaterial runtime.state.current).quantum+
      Live.entropyProduction (currentMaterial runtime.state.current).quantum+receiverEnergy runtime.state.current=
    Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+Live.measurementWork Live.initial+
      responseWork receivedState+responseWork received+Weak.pulseWork Weak.origin+Extract.pulseWork Weak.execution := by
  have paid := (runtime_invariants runtime).1
  have inherited := Extract.Runtime.complete_account Extract.Runtime.afterFirst
  change Live.entropyProduction sourceEntry.quantum+Live.freeEnergy sourceEntry.quantum=_ at inherited
  have work : Extract.Runtime.accumulatedWork Extract.Runtime.afterFirst.state.current=Extract.pulseWork Weak.execution := rfl
  rw [work] at inherited
  change Live.freeEnergy (currentMaterial runtime.state.current).quantum+
    Live.entropyProduction (currentMaterial runtime.state.current).quantum+receiverEnergy runtime.state.current=
    Live.freeEnergy sourceEntry.quantum+Live.entropyProduction sourceEntry.quantum at paid
  linarith only [paid,inherited]

theorem runtime_complete_debit (runtime : LivingRuntimeState process) :
    donorRemainingOf (historicalSupply runtime.state.current)+Weak.transfer+supplyTransfer received+supplyTransfer receivedState=
      donorRemainingOf (suppliedBlock receivedState) := by
  have paid := (runtime_invariants runtime).2.1
  change donorRemainingOf (historicalSupply runtime.state.current)=donorRemainingOf (suppliedBlock sourceEntry.quantum) at paid
  rw [paid]
  exact Extract.Runtime.complete_debit Extract.Runtime.afterFirst


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
