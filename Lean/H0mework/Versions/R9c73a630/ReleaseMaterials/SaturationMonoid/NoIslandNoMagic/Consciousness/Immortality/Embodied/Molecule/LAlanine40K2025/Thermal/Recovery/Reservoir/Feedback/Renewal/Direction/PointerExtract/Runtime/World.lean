import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Runtime.Parent

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

inductive ReceiverCurrent
  | ingress
  | running (material : Material)

def currentMaterial : ReceiverCurrent → Material
  | .ingress => sourceEntry
  | .running material => material

def loadNext (material : Material) : Material := ⟨Live.loadNext material.quantum,material.momentum⟩

def nextCurrent (current : ReceiverCurrent) : ReceiverCurrent :=
  .running (match current with
    | .ingress => advance sourceEntry
    | .running material => loadNext material)

def action : ReceiverCurrent → Matrix.unitaryGroup PointerIndex ℂ
  | .ingress => pulse (nativeClockStep : ℝ)
  | .running _ => Pointer.loadPulse (nativeClockStep : ℝ)

def historicalSupply : ReceiverCurrent → Current.FullJoint
  | .ingress => suppliedBlock sourceEntry.quantum
  | .running material => loadBlock material.quantum

def decodedMemory (current : ReceiverCurrent) : ℝ :=
  match current with
  | .ingress => oneRead (currentMaterial current).quantum.joint
  | .running _ => zeroRead (currentMaterial current).quantum.joint

def receiverEnergy (current : ReceiverCurrent) : ℝ := Extract.Port.kinetic (currentMaterial current).momentum

theorem next_joint (current : ReceiverCurrent) :
    (currentMaterial (nextCurrent current)).quantum.joint=
      Quantum.conjugation (action current) (currentMaterial current).quantum.joint := by
  cases current with
  | ingress => exact quantumNext_joint _
  | running material => exact Live.loadNext_joint _

theorem next_clock (current : ReceiverCurrent) :
    (currentMaterial (nextCurrent current)).quantum.localClock=
      (currentMaterial current).quantum.localClock+nativeClockStep := by
  cases current <;> rfl

theorem next_energy (current : ReceiverCurrent) :
    Live.baselineEnergy (currentMaterial (nextCurrent current)).quantum+receiverEnergy (nextCurrent current)=
      Live.baselineEnergy (currentMaterial current).quantum+receiverEnergy current := by
  cases current with
  | ingress => exact source_energy_conserved
  | running material =>
    change Live.baselineEnergy (Live.loadNext material.quantum)+Extract.Port.kinetic material.momentum=
      Live.baselineEnergy material.quantum+Extract.Port.kinetic material.momentum
    rw [Live.loadNext_preserves_baseline]

theorem next_net_account (current : ReceiverCurrent) :
    Live.freeEnergy (currentMaterial (nextCurrent current)).quantum+
      Live.entropyProduction (currentMaterial (nextCurrent current)).quantum+receiverEnergy (nextCurrent current)=
      Live.freeEnergy (currentMaterial current).quantum+
      Live.entropyProduction (currentMaterial current).quantum+receiverEnergy current := by
  have first := Live.complete_account (currentMaterial current).quantum
  have last := Live.complete_account (currentMaterial (nextCurrent current)).quantum
  linarith only [first,last,next_energy current]

theorem load_load_block (current : Live.State) : loadBlock (Live.loadNext current)=
    Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ)) (loadBlock current) := by
  unfold loadBlock
  rw [Live.loadNext_joint]
  exact controlled_block_left _ _ _

theorem next_remaining (current : ReceiverCurrent) :
    donorRemainingOf (historicalSupply (nextCurrent current))=donorRemainingOf (historicalSupply current) := by
  cases current with
  | ingress =>
    change donorRemainingOf (loadBlock (advance sourceEntry).quantum)=donorRemainingOf (suppliedBlock sourceEntry.quantum)
    rw [next_load_branch]
  | running material =>
    change donorRemainingOf (loadBlock (Live.loadNext material.quantum))=donorRemainingOf (loadBlock material.quantum)
    rw [load_load_block]
    simp only [donorRemainingOf,load_donor_energy,Quantum.conjugation_trace]

theorem next_memory (current : ReceiverCurrent) : decodedMemory (nextCurrent current)=decodedMemory current := by
  cases current with
  | ingress => exact next_pointer_zero _
  | running material => exact Live.loadNext_pointer_zero _

theorem next_donor (current : ReceiverCurrent) :
    donorEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)=
      donorEnergyOf (bodyRead (currentMaterial current).quantum.joint) := by
  cases current with
  | ingress => exact congrArg donorEnergyOf (next_body sourceEntry)
  | running material => exact load_donor_total _

theorem next_resource_balance (current : ReceiverCurrent) :
    (pcEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-pcEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (donorEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-donorEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (environmentEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-environmentEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (boundaryEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-boundaryEnergyOf (bodyRead (currentMaterial current).quantum.joint))=0 := by
  cases current with
  | ingress =>
    change (pcEnergyOf (bodyRead (advance sourceEntry).quantum.joint)-pcEnergyOf (bodyRead sourceEntry.quantum.joint))+
      (donorEnergyOf (bodyRead (advance sourceEntry).quantum.joint)-donorEnergyOf (bodyRead sourceEntry.quantum.joint))+
      (environmentEnergyOf (bodyRead (advance sourceEntry).quantum.joint)-environmentEnergyOf (bodyRead sourceEntry.quantum.joint))+
      (boundaryEnergyOf (bodyRead (advance sourceEntry).quantum.joint)-boundaryEnergyOf (bodyRead sourceEntry.quantum.joint))=0
    rw [next_body]
    ring
  | running material =>
    have paid := load_execution_account material.quantum
    change (pcEnergyOf (bodyRead (Live.loadNext material.quantum).joint)-pcEnergyOf (bodyRead material.quantum.joint))+
      (donorEnergyOf (bodyRead (Live.loadNext material.quantum).joint)-donorEnergyOf (bodyRead material.quantum.joint))+
      (environmentEnergyOf (bodyRead (Live.loadNext material.quantum).joint)-environmentEnergyOf (bodyRead material.quantum.joint))+
      (boundaryEnergyOf (bodyRead (Live.loadNext material.quantum).joint)-boundaryEnergyOf (bodyRead material.quantum.joint))=0
    rw [load_donor_total]
    linarith only [paid]

def vocabulary : ConstructiveRoot.Vocabulary where
  Current := ReceiverCurrent
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

abbrev ReceiverV := vocabulary

def eventLaw : SourceNativeEventAlgebra RecoveryN ReceiverV where
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

def source : SourceNativeSource RecoveryN ReceiverV where
  initial := .ingress
  law := eventLaw

def emitted (current : ReceiverCurrent) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport, ⟨rfl⟩⟩

theorem first_clock : (currentMaterial (nextCurrent .ingress)).quantum.localClock=13*nativeClockStep := source_clock

theorem receiver_event_output : 0 < receiverEnergy (nextCurrent .ingress)-receiverEnergy .ingress := source_output


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
