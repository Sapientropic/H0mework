import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime.Runtime
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

def PaidBalance (state : process.State) : Prop :=
  Live.freeEnergy (currentMaterial state.current).quantum+Live.entropyProduction (currentMaterial state.current).quantum+
    receiverEnergy state.current=Live.freeEnergy Replenish.origin+Live.entropyProduction Replenish.origin+
      Extract.Port.kinetic Replenish.material.momentum+accumulatedWork state.current

def RemainingBalance (state : process.State) : Prop :=
  donorRemainingOf (historicalSupply state.current)+accumulatedTransfer state.current=
    donorRemainingOf (suppliedBlock Replenish.origin)

def MemoryBalance (state : process.State) : Prop :=
  decodedMemory state.current=oneRead Replenish.origin.joint

def ReceiverBalance (state : process.State) : Prop :=
  (currentMaterial state.current).momentum=Replenish.material.momentum

def invariantLaw : SourceNativeGeneratedInvariantLaw process :=
  .create (fun state => PLift (PaidBalance state ∧ RemainingBalance state ∧ MemoryBalance state ∧ ReceiverBalance state))
    ⟨⟨(add_zero _).symm,add_zero _,rfl,rfl⟩⟩
    (fun state previous => ⟨by
      refine ⟨?_,(next_remaining state.current).trans previous.down.2.1,
        (next_memory state.current).trans previous.down.2.2.1,
        (next_receiver state.current).trans previous.down.2.2.2⟩
      change Live.freeEnergy (currentMaterial (nextCurrent state.current)).quantum+
        Live.entropyProduction (currentMaterial (nextCurrent state.current)).quantum+receiverEnergy (nextCurrent state.current)=
        Live.freeEnergy Replenish.origin+Live.entropyProduction Replenish.origin+
          Extract.Port.kinetic Replenish.material.momentum+accumulatedWork (nextCurrent state.current)
      have paid := previous.down.1
      change Live.freeEnergy (currentMaterial state.current).quantum+
        Live.entropyProduction (currentMaterial state.current).quantum+receiverEnergy state.current=
        Live.freeEnergy Replenish.origin+Live.entropyProduction Replenish.origin+
          Extract.Port.kinetic Replenish.material.momentum+accumulatedWork state.current at paid
      linarith only [paid,next_net_account state.current,receiver_energy_next state.current,accumulated_work_next state.current]⟩)

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
      responseWork receivedState+responseWork received+Weak.pulseWork Weak.origin+Extract.pulseWork Weak.execution+
        accumulatedWork runtime.state.current := by
  have paid := (runtime_invariants runtime).1
  have inherited := Restore.Runtime.complete_account Restore.Runtime.afterFirst
  change Live.freeEnergy Replenish.origin+Live.entropyProduction Replenish.origin+Extract.Port.kinetic Replenish.material.momentum=_ at inherited
  exact paid.trans (congrArg (fun value => value+accumulatedWork runtime.state.current) inherited)

theorem runtime_complete_debit (runtime : LivingRuntimeState process) :
    donorRemainingOf (historicalSupply runtime.state.current)+accumulatedTransfer runtime.state.current+
      Weak.transfer+supplyTransfer received+supplyTransfer receivedState=donorRemainingOf (suppliedBlock receivedState) := by
  have paid := (runtime_invariants runtime).2.1
  change donorRemainingOf (historicalSupply runtime.state.current)+accumulatedTransfer runtime.state.current=
    donorRemainingOf (suppliedBlock Replenish.origin) at paid
  rw [paid]
  exact Restore.Runtime.complete_debit Restore.Runtime.afterFirst

theorem runtime_finite_budget (runtime : LivingRuntimeState process) :
    accumulatedTransfer runtime.state.current+Weak.transfer+supplyTransfer received+supplyTransfer receivedState ≤
      donorRemainingOf (suppliedBlock receivedState) := by
  have nonnegative := (remaining_range (currentMaterial runtime.state.current).quantum).1
  change 0 ≤ donorRemainingOf (historicalSupply runtime.state.current) at nonnegative
  linarith only [runtime_complete_debit runtime,nonnegative]

theorem runtime_receiver_empty (runtime : LivingRuntimeState process) :
    (currentMaterial runtime.state.current).momentum=0 :=
  (runtime_invariants runtime).2.2.2.trans Replenish.receiver_empty

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
