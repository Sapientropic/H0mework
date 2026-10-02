import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.CompleteInquiry.Bundle

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

/-- The original inquiry supplies no branch, address, restored-header or
formed-node premise. All five full compilation branches are covered by the
three source families and an independently formed selector programme. -/
theorem every_source (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) : Nonempty (Origin state) := by
  obtain ⟨answerRank, _answerMaterial, answer, _answerPacked, answerSame, _labels, _current, _header, _old⟩ :=
    MotherAnswerQueries.every_answering_fragment N V state
  obtain ⟨actionLower, actionUpper, actionMaterial, actionTargets, action, actionParent, actionChildren, _actionCompiles, _retains⟩ :=
    MotherActionQueries.every_action_fragment N V state
  obtain ⟨revisionRank, _revisionMaterial, revisionData, revision, _revisionPacked, _revisionCompiles, _old⟩ :=
    MotherU8Compiler.every_u8_fragment N V state
  let Total := state.Query ⊕ BranchIndex state
  let routingRank := MotherArenaHigher.carrierRank Total
  let shared := MotherArenaHigher.carrierAddress Total
  let queryCode : state.Query ↪ MotherArenaHigher.Base routingRank :=
    ⟨fun query => shared (.inl query), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let indexCode : BranchIndex state ↪ MotherArenaHigher.Base routingRank :=
    ⟨fun index => shared (.inr index), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨routingMaterial, routed⟩ := mixed_recovers state answer.readClauses action.readClauses revision.readClause
    queryCode indexCode (fun index => congrFun answerSame index)
    (fun index => congrFun action.readClauses_eq index) revision.readClause_eq
  exact ⟨{
    answerRank := answerRank
    answer := answer
    actionLower := actionLower
    actionUpper := actionUpper
    actionTargets := actionTargets
    action := action
    actionMaterial := actionMaterial
    action_parent := actionParent
    action_children := actionChildren
    revisionRank := revisionRank
    revisionData := revisionData
    revision := revision
    routingRank := routingRank
    queryCode := queryCode
    indexCode := indexCode
    routingMaterial := routingMaterial
    routed := routed }⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
