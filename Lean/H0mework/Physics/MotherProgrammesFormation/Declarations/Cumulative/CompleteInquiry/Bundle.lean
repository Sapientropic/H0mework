import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.CompleteInquiry.Branches
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AnswerQueries.Consumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MaterialJoin.Consumers

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

inductive LowPart where
  | answer | revision | routing

structure Origin {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryStateAt N V) where
  answerRank : Ordinal.{0}
  answer : MotherAnswerQueries.Origin (rank := answerRank) state
    (Subtype.val : AnswerIndex state → state.Query)
  actionLower : Ordinal.{0}
  actionUpper : Ordinal.{3}
  actionTargets : MotherActionQueries.Targets state (Subtype.val : MotherActionQueries.ActionIndex state → state.Query)
  action : MotherActionQueries.Origin actionLower actionUpper state Subtype.val actionTargets
  actionMaterial : MotherReceiptHigher.Material actionUpper
  action_parent : MotherActionQueries.readLower action.originalAddress actionMaterial = MotherActionQueries.packLower action.materials
  action_children : ∀ index, MotherActionQueries.readChild actionMaterial
    (action.originalAddress (action.queries index).val) = action.targetMaterials index
  revisionRank : Ordinal.{0}
  revisionData : (index : MotherU8Compiler.U8Index state) → MotherU8Compiler.Data (MotherNativeClause.ofState state index.val)
  revision : MotherU8Compiler.Origin revisionRank state Subtype.val revisionData
  routingRank : Ordinal.{0}
  queryCode : state.Query ↪ MotherArenaHigher.Base routingRank
  indexCode : BranchIndex state ↪ MotherArenaHigher.Base routingRank
  routingMaterial : MotherArenaHigher.Material routingRank
  routed : formMixed state answer.readClauses action.readClauses revision.readClause
    queryCode indexCode routingMaterial = some (MotherNativeClause.ofState state)
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {state : RootInquiryStateAt N V} (origin : Origin state)

def Origin.highRank (_index : Unit) : Ordinal.{3} := origin.actionUpper

def Origin.lowRank : LowPart → Ordinal.{0}
  | .answer => origin.answerRank
  | .revision => origin.revisionRank
  | .routing => origin.routingRank

def Origin.highMaterials (index : Unit) : MotherReceiptHigher.Material (origin.highRank index) := origin.actionMaterial

def Origin.lowMaterials : (index : LowPart) → MotherArenaHigher.Material (origin.lowRank index)
  | .answer => MotherAnswerQueries.pack origin.answer.materials
  | .revision => origin.revision.material
  | .routing => origin.routingMaterial

def Origin.rank : Ordinal.{3} := MotherMaterialJoin.Mixed.sharedRank origin.highRank origin.lowRank

def Origin.material : MotherReceiptHigher.Material origin.rank :=
  MotherMaterialJoin.Mixed.combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials

/-- The source selector actually executes on the joined material's low
readback; its inputs are the already formed complete branch outputs. -/
def Origin.readClauses : (query : state.Query) → MotherNativeClause.Clause state.root state.visit state.U7 state.calculus query :=
  MotherMaterialJoin.Mixed.getLow origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials .routing
    (formMixed state origin.answer.readClauses origin.action.readClauses origin.revision.readClause origin.queryCode origin.indexCode)
    (by change (formMixed state _ _ _ _ _ origin.routingMaterial).isSome; rw [origin.routed]; rfl)

theorem Origin.readClauses_eq : origin.readClauses = MotherNativeClause.ofState state := by
  unfold Origin.readClauses
  erw [MotherMaterialJoin.Mixed.getLow_eq]
  exact Option.some.inj ((Option.some_get _).trans origin.routed)

theorem Origin.all_materials_retained :
    (∀ index, MotherMaterialJoin.Mixed.restrictHigh origin.highRank origin.lowRank index origin.material = origin.highMaterials index) ∧
    ∀ index, MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank index origin.material = origin.lowMaterials index :=
  ⟨MotherMaterialJoin.Mixed.restrictHigh_combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials,
    MotherMaterialJoin.Mixed.restrictLow_combine origin.highRank origin.lowRank origin.highMaterials origin.lowMaterials⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
