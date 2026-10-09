import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime.Parent

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

inductive PaymentCurrent
  | ingress
  | running (material : Material)

def currentMaterial : PaymentCurrent → Material
  | .ingress => input
  | .running material => material

def loadNext (material : Material) : Material := ⟨Live.loadNext material.quantum,material.momentum⟩

def nextCurrent (current : PaymentCurrent) : PaymentCurrent :=
  .running (match current with
    | .ingress => advance input
    | .running material => loadNext material)

def action : PaymentCurrent → Matrix.unitaryGroup PointerIndex ℂ
  | .ingress => pulse (nativeClockStep : ℝ)
  | .running _ => Pointer.loadPulse (nativeClockStep : ℝ)

def historicalSupply : PaymentCurrent → Current.FullJoint
  | .ingress => loadBlock input.quantum
  | .running material => suppliedBlock material.quantum

def decodedMemory (current : PaymentCurrent) : ℝ :=
  match current with
  | .ingress => zeroRead (currentMaterial current).quantum.joint
  | .running _ => oneRead (currentMaterial current).quantum.joint

def receiverEnergy (current : PaymentCurrent) : ℝ := Extract.Port.kinetic (currentMaterial current).momentum

theorem next_joint (current : PaymentCurrent) :
    (currentMaterial (nextCurrent current)).quantum.joint=
      Quantum.conjugation (action current) (currentMaterial current).quantum.joint := by
  cases current with
  | ingress => exact quantumNext_joint _
  | running material => exact Live.loadNext_joint _

theorem next_clock (current : PaymentCurrent) :
    (currentMaterial (nextCurrent current)).quantum.localClock=
      (currentMaterial current).quantum.localClock+nativeClockStep := by
  cases current <;> rfl

theorem next_energy (current : PaymentCurrent) :
    Live.baselineEnergy (currentMaterial (nextCurrent current)).quantum+receiverEnergy (nextCurrent current)=
      Live.baselineEnergy (currentMaterial current).quantum+receiverEnergy current := by
  cases current with
  | ingress => exact paid_energy
  | running material =>
    change Live.baselineEnergy (Live.loadNext material.quantum)+Extract.Port.kinetic material.momentum=
      Live.baselineEnergy material.quantum+Extract.Port.kinetic material.momentum
    rw [Live.loadNext_preserves_baseline]

theorem next_net_account (current : PaymentCurrent) :
    Live.freeEnergy (currentMaterial (nextCurrent current)).quantum+
      Live.entropyProduction (currentMaterial (nextCurrent current)).quantum+receiverEnergy (nextCurrent current)=
      Live.freeEnergy (currentMaterial current).quantum+
      Live.entropyProduction (currentMaterial current).quantum+receiverEnergy current := by
  have first := Live.complete_account (currentMaterial current).quantum
  have last := Live.complete_account (currentMaterial (nextCurrent current)).quantum
  linarith only [first,last,next_energy current]

theorem next_remaining (current : PaymentCurrent) :
    donorRemainingOf (historicalSupply (nextCurrent current))=donorRemainingOf (historicalSupply current) := by
  cases current with
  | ingress =>
    change donorRemainingOf (suppliedBlock (advance input).quantum)=donorRemainingOf (loadBlock input.quantum)
    rw [next_supply_branch]
  | running material => exact load_remaining material.quantum

theorem next_memory (current : PaymentCurrent) : decodedMemory (nextCurrent current)=decodedMemory current := by
  cases current with
  | ingress => exact next_pointer_one _
  | running material => exact Live.loadNext_pointer_one _

theorem next_donor (current : PaymentCurrent) :
    donorEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)=
      donorEnergyOf (bodyRead (currentMaterial current).quantum.joint) := by
  cases current with
  | ingress => exact congrArg donorEnergyOf (next_body input)
  | running material => exact load_donor_total _

theorem next_resource_balance (current : PaymentCurrent) :
    (pcEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-pcEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (donorEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-donorEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (environmentEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-environmentEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (boundaryEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-boundaryEnergyOf (bodyRead (currentMaterial current).quantum.joint))=0 := by
  cases current with
  | ingress =>
    change (pcEnergyOf (bodyRead (advance input).quantum.joint)-pcEnergyOf (bodyRead input.quantum.joint))+
      (donorEnergyOf (bodyRead (advance input).quantum.joint)-donorEnergyOf (bodyRead input.quantum.joint))+
      (environmentEnergyOf (bodyRead (advance input).quantum.joint)-environmentEnergyOf (bodyRead input.quantum.joint))+
      (boundaryEnergyOf (bodyRead (advance input).quantum.joint)-boundaryEnergyOf (bodyRead input.quantum.joint))=0
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
  Current := PaymentCurrent
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

abbrev PaymentV := vocabulary

def eventLaw : SourceNativeEventAlgebra RecoveryN PaymentV where
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

def source : SourceNativeSource RecoveryN PaymentV where
  initial := .ingress
  law := eventLaw

def emitted (current : PaymentCurrent) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport, ⟨rfl⟩⟩

theorem first_clock : (currentMaterial (nextCurrent .ingress)).quantum.localClock=14*nativeClockStep := output_clock

theorem payment_event_demand : 0 < receiverEnergy .ingress-receiverEnergy (nextCurrent .ingress) := positive_demand

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime
