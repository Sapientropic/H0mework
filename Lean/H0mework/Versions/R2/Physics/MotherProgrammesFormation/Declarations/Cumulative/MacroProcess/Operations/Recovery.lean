import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Operations.Assembly

/-! Whole-process inverse restriction through the original registry
presentation. The material successor index is retained; the other two
successor components are the original Prop-valued contracts. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

private abbrev NextState {Carrier : Type} (nodes : Carrier → RootInquiryProcessNode.{0}) :=
  (state : Carrier) → (nodes state).Query → Carrier

private def transportNext {Carrier : Type} {first last : Carrier → RootInquiryProcessNode.{0}}
    (same : first = last) (next : NextState first) : NextState last := Eq.mp (congrArg NextState same) next

private theorem transportNext_apply {Carrier : Type} {first last : Carrier → RootInquiryProcessNode.{0}}
    (same : first = last) (next : NextState first) (state : Carrier) (query : (last state).Query) :
    transportNext same next state query =
      next state (Eq.mp (congrArg RootInquiryProcessNode.Query (congrFun same state).symm) query) := by
  cases same
  rfl

private theorem query_roundtrip {first last : RootInquiryProcessNode.{0}} (same : first = last)
    (query : last.Query) :
    Eq.mp (congrArg RootInquiryProcessNode.Query same)
      (Eq.mp (congrArg RootInquiryProcessNode.Query same.symm) query) = query := by
  cases same
  rfl

private theorem next_at_equal_state (process : SourceNativeInquiryEngineProcess.{0})
    {first last : process.State} (same : first = last) {node : RootInquiryProcessNode.{0}}
    (nodeSame : node = process.stateAt first) (query : node.Query) :
    (process.successorAt last (Eq.mp (congrArg RootInquiryProcessNode.Query
      (nodeSame.trans (congrArg process.stateAt same))) query)).val =
      (process.successorAt first (Eq.mp (congrArg RootInquiryProcessNode.Query nodeSame) query)).val := by
  cases same
  rfl

private theorem process_ext (first last : SourceNativeInquiryEngineProcess.{0})
    (stateSame : first.State = last.State)
    (nodesSame : HEq first.stateAt last.stateAt)
    (initialSame : HEq first.initial last.initial)
    (nextSame : HEq (fun state query => (first.successorAt state query).val)
      (fun state query => (last.successorAt state query).val)) : first = last := by
  cases first with
  | mk firstState firstNodes firstInjective firstInitial firstNext =>
    cases last with
    | mk lastState lastNodes lastInjective lastInitial lastNext =>
      cases stateSame
      cases eq_of_heq nodesSame
      cases eq_of_heq initialSame
      have valuesSame := eq_of_heq nextSame
      have successorsSame : firstNext = lastNext := by
        funext state query
        apply Subtype.ext
        exact congrFun (congrFun valuesSame state) query
      cases successorsSame
      rfl

variable {source target : SourceNativeInquiryEngineProcess.{0}}
    (presentation : MotherRegistryRecovery.Presentation source target)

/-- Only the inverse State schema comes from the original process. All
node, initial and successor values are read from the generated process. -/
def restrict : SourceNativeInquiryEngineProcess.{0} :=
  MotherRegistryRecovery.rechart source presentation.state.symm

private theorem nodes_recover : (restrict presentation).stateAt = target.stateAt := by
  funext state
  exact (presentation.node (presentation.state.symm state)).trans
    (congrArg target.stateAt (presentation.state.apply_symm_apply state))

private theorem next_indices_recover (state : target.State)
    (query : ((restrict presentation).stateAt state).Query) :
    ((restrict presentation).successorAt state query).val =
      (target.successorAt state (Eq.mp (congrArg RootInquiryProcessNode.Query
        (congrFun (nodes_recover presentation) state)) query)).val := by
  have actual := presentation.successor (presentation.state.symm state) query
  have indexSame := presentation.state.apply_symm_apply state
  have moved := next_at_equal_state target indexSame
    (presentation.node (presentation.state.symm state)) query
  exact actual.trans moved.symm

private theorem next_recover :
    HEq (fun state query => ((restrict presentation).successorAt state query).val)
      (fun state query => (target.successorAt state query).val) := by
  let actual : NextState (restrict presentation).stateAt := fun state query =>
    ((restrict presentation).successorAt state query).val
  have transported : transportNext (nodes_recover presentation) actual =
      fun state query => (target.successorAt state query).val := by
    funext state query
    erw [transportNext_apply]
    have recovered := next_indices_recover presentation state
      (Eq.mp (congrArg RootInquiryProcessNode.Query (congrFun (nodes_recover presentation) state).symm) query)
    exact recovered.trans (congrArg (fun value => (target.successorAt state value).val)
      (query_roundtrip (congrFun (nodes_recover presentation) state) query))
  exact (cast_heq (congrArg NextState (nodes_recover presentation)) actual).symm.trans (heq_of_eq transported)

/-- This equality retains the whole successorAt function and both original
proof fields, not merely the erased root current or selected trajectory. -/
theorem restrict_eq : restrict presentation = target :=
  process_ext _ _ rfl (heq_of_eq (nodes_recover presentation))
    (heq_of_eq presentation.initial) (next_recover presentation)

private theorem successor_field_heq {first last : SourceNativeInquiryEngineProcess.{0}} (same : first = last) :
    HEq first.successorAt last.successorAt := by
  cases same
  rfl

theorem successorAt_recovers : HEq (restrict presentation).successorAt target.successorAt :=
  successor_field_heq (restrict_eq presentation)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
