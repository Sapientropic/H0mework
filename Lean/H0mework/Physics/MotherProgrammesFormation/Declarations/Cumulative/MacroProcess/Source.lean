import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Family
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Runtime.Canonical

/-! One joined mother material retains every complete node source and the
whole state/operation material. The native process is its actual factory
output, followed by the original registry's faithful inverse restriction. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

structure Origin (original : SourceNativeInquiryEngineProcess.{0}) where
  lower : Ordinal.{0}
  domain : MotherArenaHigher.Material lower
  state : MotherMacroOperations.State domain ≃ original.State
  nodes : (index : original.State) → MotherMacroNodes.Origin (original.stateAt index)
  event : MotherMacroOperations.Event (domain := domain) (fun index => (nodes (state index)).read) ↪
    MotherArenaHigher.Base lower
  operations : MotherArenaHigher.Material lower
  formed : MotherMacroOperations.formProcess domain (fun index => (nodes (state index)).read) event operations =
    some (MotherRegistryRecovery.rechart original state)

variable {original : SourceNativeInquiryEngineProcess.{0}} (origin : Origin original)

def Origin.localNodes : MotherMacroOperations.Nodes origin.domain :=
  fun index => (origin.nodes (origin.state index)).read

def Origin.highRank (index : original.State) : Ordinal.{3} := (origin.nodes index).rank

def Origin.highMaterials (index : original.State) : MotherReceiptHigher.Material (origin.highRank index) :=
  (origin.nodes index).material

def Origin.lowRank (_index : Unit) : Ordinal.{0} := origin.lower

def Origin.lowMaterials (_index : Unit) : MotherArenaHigher.Material origin.lower :=
  MotherArenaHigher.pack origin.lower (origin.domain, origin.operations)

def Origin.rank : Ordinal.{3} := MotherMaterialJoin.Mixed.sharedRank origin.highRank origin.lowRank

def Origin.material : MotherReceiptHigher.Material origin.rank :=
  MotherMaterialJoin.Mixed.combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials

def Origin.readParts : MotherArenaHigher.Material origin.lower × MotherArenaHigher.Material origin.lower :=
  MotherArenaHigher.split origin.lower
    (MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank () origin.material)

theorem Origin.readParts_eq : origin.readParts = (origin.domain, origin.operations) := by
  change MotherArenaHigher.split origin.lower
    (MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank ()
      (MotherMaterialJoin.Mixed.combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials)) = _
  exact (congrArg (MotherArenaHigher.split origin.lower)
    (MotherMaterialJoin.Mixed.restrictLow_combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials ())).trans
    (MotherArenaHigher.split_pack origin.lower (origin.domain, origin.operations))

def Origin.readDomain : MotherArenaHigher.Material origin.lower := origin.readParts.1

theorem Origin.domain_eq : origin.readDomain = origin.domain := congrArg Prod.fst origin.readParts_eq

def Origin.readOperations : MotherArenaHigher.Material origin.lower := origin.readParts.2

theorem Origin.operations_eq : origin.readOperations = origin.operations := congrArg Prod.snd origin.readParts_eq

def Origin.nodeReaders (index : original.State) :
    MotherReceiptHigher.Material (origin.highRank index) → Option RootInquiryProcessNode :=
  MotherMacroFamily.readNode (origin.nodes index)

theorem Origin.nodes_formed :
    MotherMacroFamily.formNodes origin.highRank origin.lowRank origin.nodeReaders origin.material =
      some (fun index => (origin.nodes index).read) :=
  MotherMacroFamily.formNodes_formed origin.highRank origin.lowRank origin.nodeReaders
    origin.highMaterials origin.lowMaterials _ (fun index => MotherMacroFamily.readNode_formed (origin.nodes index))

/-- This complete node family executes the original child readers on their
actual projections from the joint material; no target node table is read. -/
def Origin.nodeFamily : original.State → RootInquiryProcessNode :=
  (MotherMacroFamily.formNodes origin.highRank origin.lowRank origin.nodeReaders origin.material).get
    (by rw [origin.nodes_formed]; rfl)

theorem Origin.nodeFamily_eq : origin.nodeFamily = fun index => (origin.nodes index).read :=
  Option.some.inj ((Option.some_get _).trans origin.nodes_formed)

def Origin.readNodes : MotherMacroOperations.Nodes origin.readDomain := fun index =>
  origin.nodeFamily (origin.state (Equiv.cast (congrArg MotherMacroOperations.State origin.domain_eq) index))

theorem Origin.readNodes_heq : HEq origin.readNodes origin.localNodes := by
  unfold Origin.readNodes
  rw [origin.nodeFamily_eq]
  exact MotherMacroFamily.nodes_heq origin.domain_eq origin.localNodes

def Origin.readEvent : MotherMacroOperations.Event origin.readNodes ↪ MotherArenaHigher.Base origin.lower :=
  MotherMacroFamily.transportEvent origin.domain_eq origin.readNodes_heq origin.event

/-- The original registry factory reads the full actual domain, node
family and operation graph. Its checks reuse the original Prop contracts. -/
def Origin.form : Option SourceNativeInquiryEngineProcess :=
  MotherMacroOperations.formProcess origin.readDomain origin.readNodes origin.readEvent origin.readOperations

theorem Origin.form_formed : origin.form = some (MotherRegistryRecovery.rechart original origin.state) := by
  unfold Origin.form Origin.readEvent
  exact (MotherMacroFamily.operations_commute origin.domain_eq origin.readNodes_heq origin.event origin.readOperations).trans
    ((congrArg (MotherMacroOperations.formProcess origin.domain origin.localNodes origin.event) origin.operations_eq).trans
      origin.formed)

def Origin.process : SourceNativeInquiryEngineProcess :=
  origin.form.get (by rw [origin.form_formed]; rfl)

theorem Origin.process_eq : origin.process = MotherRegistryRecovery.rechart original origin.state :=
  Option.some.inj ((Option.some_get _).trans origin.form_formed)

def Origin.presentation : MotherRegistryRecovery.Presentation origin.process original :=
  origin.process_eq.symm ▸ MotherRegistryRecovery.rechartPresentation original origin.state

def Origin.restrict : SourceNativeInquiryEngineProcess := MotherMacroOperations.restrict origin.presentation

theorem Origin.restrict_eq : origin.restrict = original := MotherMacroOperations.restrict_eq origin.presentation

theorem Origin.successorAt_recovers : HEq origin.restrict.successorAt original.successorAt :=
  MotherMacroOperations.successorAt_recovers origin.presentation

/-- The whole spaces of every node material and the complete low state/
operation material survive the join, not just their selected evaluations. -/
theorem Origin.retained :
    (∀ index, MotherMaterialJoin.Mixed.restrictHigh origin.highRank origin.lowRank index origin.material =
      (origin.nodes index).material) ∧
    MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank () origin.material =
      MotherArenaHigher.pack origin.lower (origin.domain, origin.operations) :=
  ⟨MotherMaterialJoin.Mixed.restrictHigh_combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials,
    MotherMaterialJoin.Mixed.restrictLow_combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials ()⟩

theorem Origin.whole_material_spaces :
    Function.LeftInverse
      (fun material =>
        ((fun index => MotherMaterialJoin.Mixed.restrictHigh origin.highRank origin.lowRank index material),
          (fun index => MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank index material)))
      (fun materials => MotherMaterialJoin.Mixed.combine origin.highRank origin.lowRank materials.1 materials.2) :=
  MotherMaterialJoin.Mixed.whole_family_leftInverse origin.highRank origin.lowRank

/-- Every state, including answered, duplicate and unvisited states, pays
its own complete node source before the one joint material is formed. -/
theorem every_source (original : SourceNativeInquiryEngineProcess.{0}) : Nonempty (Origin original) := by
  let nodes := fun index => Classical.choice (MotherMacroNodes.every_node (original.stateAt index))
  let Events := Σ index : original.State, (original.stateAt index).Query
  let Total := original.State ⊕ Events
  let lower := MotherArenaHigher.carrierRank Total
  let shared := MotherArenaHigher.carrierAddress Total
  let stateCode : original.State ↪ MotherArenaHigher.Base lower :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let eventCode : Events ↪ MotherArenaHigher.Base lower :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨domain, ⟨indices⟩⟩ := MotherAuthorityFamilies.every_index original.State stateCode
  let state : MotherMacroOperations.State domain ≃ original.State := indices.symm
  let actualNodes : MotherMacroOperations.Nodes domain := fun index => (nodes (state index)).read
  have nodeSame : ∀ index, actualNodes index = original.stateAt (state index) :=
    fun index => (nodes (state index)).read_eq
  let queries := fun index => Equiv.cast (congrArg RootInquiryProcessNode.Query (nodeSame index))
  let event : MotherMacroOperations.Event actualNodes ↪ MotherArenaHigher.Base lower :=
    (Equiv.sigmaCongr state queries).toEmbedding.trans eventCode
  obtain ⟨operations, formed⟩ := MotherMacroOperations.every_original_on_nodes
    domain actualNodes event original state nodeSame
  exact ⟨⟨lower, domain, state, nodes, event, operations, formed⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroSource
