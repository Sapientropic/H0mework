import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime.Parent
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

inductive ReplenishCurrent
  | ingress
  | running (material : Material)

def currentMaterial : ReplenishCurrent → Material
  | .ingress => Replenish.material
  | .running material => material

def responseMaterial (material : Material) : Material := ⟨respondNext material.quantum,material.momentum⟩
def suppliedMaterial : Material := responseMaterial Replenish.material

private theorem response_clock (material : Material) :
    (responseMaterial material).quantum.localClock=material.quantum.localClock+nativeClockStep := rfl

private theorem response_receiver (material : Material) :
    (responseMaterial material).momentum=material.momentum := rfl
def loadNext (material : Material) : Material := ⟨Live.loadNext material.quantum,material.momentum⟩

def nextCurrent (current : ReplenishCurrent) : ReplenishCurrent :=
  .running (match current with
    | .ingress => suppliedMaterial
    | .running material => loadNext material)

def action : ReplenishCurrent → Matrix.unitaryGroup PointerIndex ℂ
  | .ingress => feedbackPulse (nativeClockStep : ℝ)
  | .running _ => Pointer.loadPulse (nativeClockStep : ℝ)

def eventWork : ReplenishCurrent → ℝ
  | .ingress => responseWork Replenish.origin
  | .running _ => 0

def accumulatedWork : ReplenishCurrent → ℝ
  | .ingress => 0
  | .running _ => responseWork Replenish.origin

def eventTransfer : ReplenishCurrent → ℝ
  | .ingress => Registered.transfer
  | .running _ => 0

def accumulatedTransfer : ReplenishCurrent → ℝ
  | .ingress => 0
  | .running _ => Registered.transfer

def historicalSupply (current : ReplenishCurrent) : Current.FullJoint :=
  suppliedBlock (currentMaterial current).quantum

def decodedMemory (current : ReplenishCurrent) : ℝ := oneRead (currentMaterial current).quantum.joint

def receiverEnergy (current : ReplenishCurrent) : ℝ := Extract.Port.kinetic (currentMaterial current).momentum

theorem next_joint (current : ReplenishCurrent) :
    (currentMaterial (nextCurrent current)).quantum.joint=
      Quantum.conjugation (action current) (currentMaterial current).quantum.joint := by
  cases current with
  | ingress => exact respondNext_joint Replenish.origin
  | running material => exact Live.loadNext_joint _

theorem next_clock (current : ReplenishCurrent) :
    (currentMaterial (nextCurrent current)).quantum.localClock=
      (currentMaterial current).quantum.localClock+nativeClockStep := by
  cases current with
  | ingress => exact response_clock Replenish.material
  | running material => exact Live.loadNext_clock material.quantum

theorem next_receiver (current : ReplenishCurrent) :
    (currentMaterial (nextCurrent current)).momentum=(currentMaterial current).momentum := by
  cases current with
  | ingress => exact response_receiver Replenish.material
  | running material => rfl

theorem receiver_energy_next (current : ReplenishCurrent) : receiverEnergy (nextCurrent current)=receiverEnergy current :=
  congrArg Extract.Port.kinetic (next_receiver current)

theorem next_net_account (current : ReplenishCurrent) :
    (Live.freeEnergy (currentMaterial (nextCurrent current)).quantum-Live.freeEnergy (currentMaterial current).quantum)+
      (Live.entropyProduction (currentMaterial (nextCurrent current)).quantum-
        Live.entropyProduction (currentMaterial current).quantum)=eventWork current := by
  cases current with
  | ingress => exact respondNext_netAccount Replenish.origin
  | running material => exact Live.loadNext_net_account _

theorem accumulated_work_next (current : ReplenishCurrent) :
    accumulatedWork (nextCurrent current)=accumulatedWork current+eventWork current := by
  cases current with
  | ingress => exact (zero_add _).symm
  | running _ => exact (add_zero _).symm

theorem next_remaining (current : ReplenishCurrent) :
    donorRemainingOf (historicalSupply (nextCurrent current))+accumulatedTransfer (nextCurrent current)=
      donorRemainingOf (historicalSupply current)+accumulatedTransfer current := by
  cases current with
  | ingress => exact (response_remaining_debit Replenish.origin).trans (add_zero _).symm
  | running material => exact congrArg (fun r => r+Registered.transfer) (load_remaining material.quantum)

theorem next_memory (current : ReplenishCurrent) : decodedMemory (nextCurrent current)=decodedMemory current := by
  cases current with
  | ingress => exact respondNext_one Replenish.origin
  | running material => exact Live.loadNext_pointer_one _

theorem next_donor (current : ReplenishCurrent) :
    donorEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)+eventTransfer current=
      donorEnergyOf (bodyRead (currentMaterial current).quantum.joint) := by
  cases current with
  | ingress =>
    have debit := response_donor_from_supply Replenish.origin
    have balance := supply_branch_paid Replenish.origin
    change donorEnergyOf (bodyRead (respondNext Replenish.origin).joint)+supplyTransfer Replenish.origin=
      donorEnergyOf (bodyRead Replenish.origin.joint)
    unfold supplyTransfer
    linarith only [debit,balance]
  | running material =>
    change donorEnergyOf (bodyRead (Live.loadNext material.quantum).joint)+0=donorEnergyOf (bodyRead material.quantum.joint)
    rw [load_donor_total,add_zero]

theorem next_resource_balance (current : ReplenishCurrent) :
    (pcEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-pcEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (donorEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-donorEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (environmentEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-environmentEnergyOf (bodyRead (currentMaterial current).quantum.joint))+
    (boundaryEnergyOf (bodyRead (currentMaterial (nextCurrent current)).quantum.joint)-boundaryEnergyOf (bodyRead (currentMaterial current).quantum.joint))=eventWork current := by
  cases current with
  | ingress => exact response_resource_balance Replenish.origin
  | running material =>
    dsimp only [nextCurrent,currentMaterial,loadNext,eventWork]
    rw [load_donor_total]
    linarith only [load_execution_account material.quantum]

theorem first_pc_gain : (69/100 : ℝ) < pcEnergyOf (bodyRead suppliedMaterial.quantum.joint)-
    pcEnergyOf (bodyRead Replenish.origin.joint) := by
  have split := response_pc_account Replenish.origin
  change pcEnergyOf (bodyRead suppliedMaterial.quantum.joint)-pcEnergyOf (bodyRead Replenish.origin.joint)=
    Gain.firstLoad+Registered.transfer at split
  linarith only [split,Gain.source_transfer_positive,(abs_le.mp Gain.first_load_error).1]

theorem first_not_old_load : suppliedMaterial.quantum.joint ≠ (Live.loadNext Replenish.origin).joint := by
  intro same
  have positive : (bodyRead Replenish.origin.joint).PosSemidef :=
    (Replenish.origin.positive.submatrix Sum.inl).add (Replenish.origin.positive.submatrix Sum.inr)
  have trace : (bodyRead Replenish.origin.joint).trace=1 := by
    rw [bodyRead,Matrix.trace_add]
    have h := trace_fromBlocks Replenish.origin.joint.toBlocks₁₁ Replenish.origin.joint.toBlocks₁₂
      Replenish.origin.joint.toBlocks₂₁ Replenish.origin.joint.toBlocks₂₂
    rw [Matrix.fromBlocks_toBlocks,Replenish.origin.normalized] at h
    exact h.symm
  have bound := Gain.load_error (bodyRead Replenish.origin.joint) positive
  rw [trace,Complex.one_re,mul_one,← Live.loadNext_body] at bound
  have bounded : |pcEnergyOf (bodyRead (Live.loadNext Replenish.origin).joint)-
      pcEnergyOf (bodyRead Replenish.origin.joint)| ≤ (101/2000 : ℝ) :=
    bound.trans (by nlinarith only [Load.Producer.StrictThermal.nativeClock_small.2])
  have gain := first_pc_gain
  rw [same] at gain
  linarith only [gain,(abs_le.mp bounded).2]

def vocabulary : ConstructiveRoot.Vocabulary where
  Current := ReplenishCurrent
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

abbrev ReplenishV := vocabulary

def eventLaw : SourceNativeEventAlgebra RecoveryN ReplenishV where
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

def source : SourceNativeSource RecoveryN ReplenishV where
  initial := .ingress
  law := eventLaw

def emitted (current : ReplenishCurrent) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport, ⟨rfl⟩⟩

theorem first_clock : (currentMaterial (nextCurrent .ingress)).quantum.localClock=15*nativeClockStep := Account.clocks.1

private theorem response_then_load (material : Material) :
    loadNext (responseMaterial material)=Account.advance material := by
  cases material
  rfl

theorem second_material : currentMaterial (nextCurrent (nextCurrent .ingress))=Account.output := by
  change loadNext (responseMaterial Replenish.material)=Account.advance Replenish.material
  exact response_then_load Replenish.material

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
