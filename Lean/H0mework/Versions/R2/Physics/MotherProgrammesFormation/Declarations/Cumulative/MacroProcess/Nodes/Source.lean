import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Nodes.Presentation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroNodes
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

def headerOf : RootInquiryProcessNode.{0} → RootInquiryStatePresentation
  | .active header => header
  | .answered header _ => header

def selectionOf : (node : RootInquiryProcessNode.{0}) → Selection (headerOf node)
  | .active _ => .inl ()
  | .answered _ query => .inr query

theorem nodeAt_headerOf (node : RootInquiryProcessNode.{0}) : nodeAt (headerOf node) (selectionOf node) = node := by
  cases node <;> rfl

/-- A full node consists of the complete inquiry source and an actual
active/answered selector. Its prior query is retained as data when answered. -/
structure Origin (node : RootInquiryProcessNode.{0}) where
  inquiry : MotherCompleteInquiry.Origin (headerOf node).state.base
  selector : MotherArenaHigher.Material inquiry.answerRank
  formed : form inquiry.readWorld (queryCode (headerOf node) inquiry) selector = some node

variable {node : RootInquiryProcessNode.{0}} (origin : Origin node)

def Origin.highRank (_index : Unit) : Ordinal.{3} := origin.inquiry.rank

def Origin.lowRank (_index : Unit) : Ordinal.{0} := origin.inquiry.answerRank

def Origin.highMaterials (index : Unit) : MotherReceiptHigher.Material (origin.highRank index) := origin.inquiry.material

def Origin.lowMaterials (index : Unit) : MotherArenaHigher.Material (origin.lowRank index) := origin.selector

def Origin.rank : Ordinal.{3} := MotherMaterialJoin.Mixed.sharedRank origin.highRank origin.lowRank

def Origin.material : MotherReceiptHigher.Material origin.rank :=
  MotherMaterialJoin.Mixed.combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials

def Origin.read : RootInquiryProcessNode :=
  MotherMaterialJoin.Mixed.getLow origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials ()
    (form origin.inquiry.readWorld (queryCode (headerOf node) origin.inquiry))
    (by change (form _ _ origin.selector).isSome; rw [origin.formed]; rfl)

theorem Origin.read_eq : origin.read = node := by
  unfold Origin.read
  erw [MotherMaterialJoin.Mixed.getLow_eq]
  exact Option.some.inj ((Option.some_get _).trans origin.formed)

theorem every_node (node : RootInquiryProcessNode.{0}) : Nonempty (Origin node) := by
  obtain ⟨inquiry⟩ := MotherCompleteInquiry.every_source (headerOf node).N (headerOf node).V (headerOf node).state.base
  obtain ⟨selector, formed⟩ := node_on_formed_presentation (headerOf node) inquiry (selectionOf node)
  exact ⟨⟨inquiry, selector, formed.trans (congrArg some (nodeAt_headerOf node))⟩⟩

/-- Material preservation concerns the complete inquiry input, not only
queries that happen to be enabled at this process node. -/
theorem Origin.retained :
    MotherMaterialJoin.Mixed.restrictHigh origin.highRank origin.lowRank () origin.material = origin.inquiry.material ∧
    MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank () origin.material = origin.selector :=
  ⟨MotherMaterialJoin.Mixed.restrictHigh_combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials (),
    MotherMaterialJoin.Mixed.restrictLow_combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials ()⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroNodes
