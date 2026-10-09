import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Runtime.Parent

/-! The original nine-q occurrence supplies once, then continues with the original load. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
noncomputable section

inductive WeakCurrent
  | ingress
  | running (state : Live.State)

def currentState : WeakCurrent → Live.State
  | .ingress => origin
  | .running state => state

def nextCurrent (current : WeakCurrent) : WeakCurrent :=
  .running (match current with
    | .ingress => target
    | .running state => Live.loadNext state)

def action : WeakCurrent → Matrix.unitaryGroup PointerIndex ℂ
  | .ingress => pointerPulse (nativeClockStep : ℝ)
  | .running _ => Pointer.loadPulse (nativeClockStep : ℝ)

def eventWork : WeakCurrent → ℝ
  | .ingress => pulseWork origin
  | .running _ => 0

def accumulatedWork : WeakCurrent → ℝ
  | .ingress => 0
  | .running _ => pulseWork origin

def accumulatedTransfer : WeakCurrent → ℝ
  | .ingress => 0
  | .running _ => transfer

theorem next_joint (current : WeakCurrent) :
    (currentState (nextCurrent current)).joint =
      Quantum.conjugation (action current) (currentState current).joint := by
  cases current with
  | ingress => exact Weak.next_joint origin
  | running state => exact Live.loadNext_joint state

theorem next_clock (current : WeakCurrent) :
    (currentState (nextCurrent current)).localClock =
      (currentState current).localClock + nativeClockStep := by
  cases current <;> rfl

theorem next_net_account (current : WeakCurrent) :
    (Live.freeEnergy (currentState (nextCurrent current)) - Live.freeEnergy (currentState current)) +
      (Live.entropyProduction (currentState (nextCurrent current)) -
        Live.entropyProduction (currentState current)) = eventWork current := by
  cases current with
  | ingress => exact Weak.next_net_account origin
  | running state => exact Live.loadNext_net_account state

theorem accumulated_work_next (current : WeakCurrent) :
    accumulatedWork (nextCurrent current) = accumulatedWork current + eventWork current := by
  cases current with
  | ingress => exact (zero_add _).symm
  | running _ => exact (add_zero _).symm

theorem next_remaining (current : WeakCurrent) :
    donorRemainingOf (suppliedBlock (currentState (nextCurrent current))) +
      accumulatedTransfer (nextCurrent current) =
    donorRemainingOf (suppliedBlock (currentState current)) + accumulatedTransfer current := by
  cases current with
  | ingress => exact remaining_debit.trans (add_zero _).symm
  | running state => exact congrArg (fun r => r + transfer) (load_remaining state)

theorem next_resource_balance (current : WeakCurrent) :
    (pcEnergyOf (bodyRead (currentState (nextCurrent current)).joint) -
      pcEnergyOf (bodyRead (currentState current).joint)) +
    (donorEnergyOf (bodyRead (currentState (nextCurrent current)).joint) -
      donorEnergyOf (bodyRead (currentState current).joint)) +
    (environmentEnergyOf (bodyRead (currentState (nextCurrent current)).joint) -
      environmentEnergyOf (bodyRead (currentState current).joint)) +
    (boundaryEnergyOf (bodyRead (currentState (nextCurrent current)).joint) -
      boundaryEnergyOf (bodyRead (currentState current).joint)) = eventWork current := by
  cases current with
  | ingress => exact Weak.next_resource_balance origin
  | running state =>
    dsimp only [nextCurrent, currentState, eventWork]
    rw [load_donor_total]
    linarith [load_execution_account state]

def vocabulary : ConstructiveRoot.Vocabulary where
  Current := WeakCurrent
  Anchor := RecoveryN.Anchor
  Incidence := RecoverySupport
  Lineage := RecoveryN.Lineage
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := fun _ => reservoirSupport
  lineageAt := fun _ => LAlanine40K2025.Source.key
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => nextCurrent current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev WeakV := vocabulary

def eventLaw : SourceNativeEventAlgebra RecoveryN WeakV where
  EventAt := fun _ support => PLift (support = reservoirSupport)
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.down
    exact recoveryInventory _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.down.symm
  lineage_commutes := fun _ => rfl

def source : SourceNativeSource RecoveryN WeakV where
  initial := .ingress
  law := eventLaw

def emitted (current : WeakCurrent) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport, ⟨rfl⟩⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
