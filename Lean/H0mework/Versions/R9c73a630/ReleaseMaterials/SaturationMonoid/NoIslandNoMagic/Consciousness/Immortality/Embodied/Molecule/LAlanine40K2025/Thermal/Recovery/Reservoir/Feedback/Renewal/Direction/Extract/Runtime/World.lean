import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Extract.Runtime.Parent

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

inductive ExtractCurrent
  | ingress
  | running (state : Live.State)

def currentState : ExtractCurrent → Live.State
  | .ingress => Weak.execution
  | .running state => state

def nextCurrent (current : ExtractCurrent) : ExtractCurrent :=
  .running (match current with
    | .ingress => Extract.next Weak.execution
    | .running state => Live.loadNext state)

def action : ExtractCurrent → Matrix.unitaryGroup PointerIndex ℂ
  | .ingress => Extract.pointerPulse (nativeClockStep : ℝ)
  | .running _ => Pointer.loadPulse (nativeClockStep : ℝ)

def eventWork : ExtractCurrent → ℝ
  | .ingress => Extract.pulseWork Weak.execution
  | .running _ => 0

def accumulatedWork : ExtractCurrent → ℝ
  | .ingress => 0
  | .running _ => Extract.pulseWork Weak.execution

theorem next_joint (current : ExtractCurrent) :
    (currentState (nextCurrent current)).joint =
      Quantum.conjugation (action current) (currentState current).joint := by
  cases current with
  | ingress => exact Extract.next_joint Weak.execution
  | running state => exact Live.loadNext_joint state

theorem next_clock (current : ExtractCurrent) :
    (currentState (nextCurrent current)).localClock =
      (currentState current).localClock + nativeClockStep := by
  cases current <;> rfl

theorem next_net_account (current : ExtractCurrent) :
    (Live.freeEnergy (currentState (nextCurrent current)) - Live.freeEnergy (currentState current)) +
      (Live.entropyProduction (currentState (nextCurrent current)) -
        Live.entropyProduction (currentState current)) = eventWork current := by
  cases current with
  | ingress => exact Extract.next_net_account Weak.execution
  | running state => exact Live.loadNext_net_account state

theorem accumulated_work_next (current : ExtractCurrent) :
    accumulatedWork (nextCurrent current) = accumulatedWork current + eventWork current := by
  cases current with
  | ingress => exact (zero_add _).symm
  | running _ => exact (add_zero _).symm

theorem next_remaining (current : ExtractCurrent) :
    donorRemainingOf (suppliedBlock (currentState (nextCurrent current))) =
      donorRemainingOf (suppliedBlock (currentState current)) := by
  cases current with
  | ingress => exact Extract.next_remaining Weak.execution
  | running state => exact load_remaining state

theorem next_resource_balance (current : ExtractCurrent) :
    (pcEnergyOf (bodyRead (currentState (nextCurrent current)).joint) -
      pcEnergyOf (bodyRead (currentState current).joint)) +
    (donorEnergyOf (bodyRead (currentState (nextCurrent current)).joint) -
      donorEnergyOf (bodyRead (currentState current).joint)) +
    (environmentEnergyOf (bodyRead (currentState (nextCurrent current)).joint) -
      environmentEnergyOf (bodyRead (currentState current).joint)) +
    (boundaryEnergyOf (bodyRead (currentState (nextCurrent current)).joint) -
      boundaryEnergyOf (bodyRead (currentState current).joint)) = eventWork current := by
  cases current with
  | ingress =>
    dsimp only [currentState,nextCurrent,eventWork]
    have work := Extract.pulse_work_resources Weak.execution
    unfold Extract.extractedPCWork at work
    unfold donorEnergyOf environmentEnergyOf
    rw [Extract.next_donor,Extract.next_environment]
    linarith only [work]
  | running state =>
    dsimp only [nextCurrent, currentState, eventWork]
    rw [load_donor_total]
    linarith [load_execution_account state]

def vocabulary : ConstructiveRoot.Vocabulary where
  Current := ExtractCurrent
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

abbrev ExtractV := vocabulary

def eventLaw : SourceNativeEventAlgebra RecoveryN ExtractV where
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

def source : SourceNativeSource RecoveryN ExtractV where
  initial := .ingress
  law := eventLaw

def emitted (current : ExtractCurrent) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport, ⟨rfl⟩⟩

theorem extraction_event_output : (7/5 : ℝ) < -eventWork .ingress :=
  Extract.original_net_output_lower

theorem first_clock : (currentState (nextCurrent .ingress)).localClock = 12*nativeClockStep := by
  change Weak.execution.localClock+nativeClockStep=12*nativeClockStep
  rw [Weak.clocks.2.2]
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
