import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime.Parent
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

inductive ControlCurrent
  | ingress
  | running (material : Material)

def currentMaterial : ControlCurrent → Material
  | .ingress => ControlRecovery.material
  | .running material => material

def controlledMaterial : Material := Receiver.output
def loadNext (material : Material) : Material := ⟨Live.loadNext material.quantum,material.momentum⟩

def nextCurrent (current : ControlCurrent) : ControlCurrent :=
  .running (match current with
    | .ingress => controlledMaterial
    | .running material => loadNext material)

def action : ControlCurrent → Matrix.unitaryGroup PointerIndex ℂ
  | .ingress => Receiver.coupledPulse (nativeClockStep : ℝ)
  | .running _ => Pointer.loadPulse (nativeClockStep : ℝ)

def historicalSupply (current : ControlCurrent) : Current.FullJoint :=
  suppliedBlock (currentMaterial current).quantum
def decodedMemory (current : ControlCurrent) : ℝ := oneRead (currentMaterial current).quantum.joint
def receiverEnergy (current : ControlCurrent) : ℝ := Extract.Port.kinetic (currentMaterial current).momentum

theorem next_joint (current : ControlCurrent) :
    (currentMaterial (nextCurrent current)).quantum.joint=
      Quantum.conjugation (action current) (currentMaterial current).quantum.joint := by
  cases current with
  | ingress => exact Receiver.next_joint ControlRecovery.origin
  | running material => exact Live.loadNext_joint _

theorem next_clock (current : ControlCurrent) :
    (currentMaterial (nextCurrent current)).quantum.localClock=
      (currentMaterial current).quantum.localClock+nativeClockStep := by
  cases current with
  | ingress => rfl
  | running material => exact Live.loadNext_clock material.quantum

theorem next_baseline_account (current : ControlCurrent) :
    Live.baselineEnergy (currentMaterial (nextCurrent current)).quantum+receiverEnergy (nextCurrent current)=
      Live.baselineEnergy (currentMaterial current).quantum+receiverEnergy current := by
  cases current with
  | ingress => exact Receiver.source_energy_conserved
  | running material =>
    change Live.baselineEnergy (Live.loadNext material.quantum)+Extract.Port.kinetic material.momentum=
      Live.baselineEnergy material.quantum+Extract.Port.kinetic material.momentum
    rw [Live.loadNext_preserves_baseline]

theorem next_net_account (current : ControlCurrent) :
    (Live.freeEnergy (currentMaterial (nextCurrent current)).quantum-Live.freeEnergy (currentMaterial current).quantum)+
      (Live.entropyProduction (currentMaterial (nextCurrent current)).quantum-
        Live.entropyProduction (currentMaterial current).quantum)+
      (receiverEnergy (nextCurrent current)-receiverEnergy current)=0 := by
  have first := Live.complete_account (currentMaterial current).quantum
  have last := Live.complete_account (currentMaterial (nextCurrent current)).quantum
  linarith only [first,last,next_baseline_account current]

theorem next_remaining (current : ControlCurrent) :
    donorRemainingOf (historicalSupply (nextCurrent current))=donorRemainingOf (historicalSupply current) := by
  cases current with
  | ingress => exact Receiver.output_remaining
  | running material => exact load_remaining material.quantum

theorem next_memory (current : ControlCurrent) : decodedMemory (nextCurrent current)=decodedMemory current := by
  cases current with
  | ingress => exact Receiver.output_memory
  | running material => exact Live.loadNext_pointer_one _

theorem next_donor (current : ControlCurrent) :
    donorEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)=
      donorEnergyOf (bodyRead (currentMaterial current).quantum.joint) := by
  cases current with
  | ingress => exact congrArg (Collision.energy Powered.Producer.poweredTotalHamiltonian) Receiver.output_donor
  | running material => exact load_donor_total _

theorem next_resource_balance (current : ControlCurrent) :
    (pcEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-pcEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (donorEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-donorEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (environmentEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-environmentEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (boundaryEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-boundaryEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
      (receiverEnergy (nextCurrent current)-receiverEnergy current)=0 := by
  have paid := next_baseline_account current
  rw [Live.baselineEnergy_split,Live.baselineEnergy_split,baseline_energy_split,baseline_energy_split] at paid
  have memory := next_memory current
  unfold decodedMemory at memory
  unfold pointerEnergy at paid
  rw [memory] at paid
  linarith only [paid]

theorem first_output_gain : (2/25 : ℝ) < receiverEnergy (nextCurrent .ingress)-receiverEnergy .ingress :=
  Receiver.output_kinetic

theorem first_not_old_load : controlledMaterial.quantum ≠ Live.loadNext ControlRecovery.origin := Receiver.output_not_load

def vocabulary : ConstructiveRoot.Vocabulary where
  Current := ControlCurrent
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

abbrev ControlV := vocabulary

def eventLaw : SourceNativeEventAlgebra RecoveryN ControlV where
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

def source : SourceNativeSource RecoveryN ControlV where
  initial := .ingress
  law := eventLaw

def emitted (current : ControlCurrent) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport,⟨rfl⟩⟩

theorem first_clock : (currentMaterial (nextCurrent .ingress)).quantum.localClock=17*nativeClockStep := Receiver.output_clock

theorem second_material : currentMaterial (nextCurrent (nextCurrent .ingress))=loadNext Receiver.output := rfl

theorem second_clock : (currentMaterial (nextCurrent (nextCurrent .ingress))).quantum.localClock=18*nativeClockStep := by
  rw [next_clock,first_clock]
  ring

theorem running_receiver (material : Material) :
    (currentMaterial (nextCurrent (.running material))).momentum=material.momentum := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
