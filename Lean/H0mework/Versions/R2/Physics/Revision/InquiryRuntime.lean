import H0mework.Versions.R2.Physics.SpinRuntime.InquiryHistory

/-! Canonical physics inquiry execution begins at the original physical
 seed, follows its generated prefix, then consumes the Cartan and spin-pair
actual actions at their existing material occurrences. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext
open StageTenPhysicalRoot

noncomputable section

private def historicalSuccessor (index : Fin 7) : SpinPair.RuntimeState :=
  if before : index.val + 1 < 7 then .history ⟨index.val + 1, before⟩
  else .native 0

def physicalInquiryProcess : SourceNativeInquiryEngineProcess where
  State := SpinPair.RuntimeState
  stateAt := fun state => .active (SpinPair.runtimePresentation state)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive equality
    cases leftActive
    cases rightActive
    exact SpinPair.runtimePresentation_erase_injective equality
  initial := .history 0
  successorAt := by
    intro state query
    cases state with
    | history index =>
        refine ⟨historicalSuccessor index, ?_⟩
        fin_cases index <;> cases query
        · exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (oldInquiryPresentation 0) (oldInquiryPresentation 1) PUnit.unit
            (oldConfigurationFace _) (oldConfigurationConsumer _) rfl rfl HEq.rfl
        · exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (oldInquiryPresentation 1) (oldInquiryPresentation 2) PUnit.unit
            (oldConfigurationFace _) (oldConfigurationConsumer _) rfl rfl HEq.rfl
        · exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (oldInquiryPresentation 2) cartanInquiryPresentation PUnit.unit
            (oldConfigurationFace _) (oldConfigurationConsumer _) rfl rfl HEq.rfl
        · exact RootInquiryProcessNode.active_actualAction_successor_valid
            cartanInquiryPresentation (materialInquiryPresentation 0) PUnit.unit
            firstAssemblyGeneratedCartanAction rfl rfl HEq.rfl
        · exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (materialInquiryPresentation 0) (materialInquiryPresentation 1) PUnit.unit
            (materialConfigurationFace 1) (materialConfigurationConsumer 1) rfl rfl HEq.rfl
        · exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (materialInquiryPresentation 1) SpinPair.inquiryPresentation PUnit.unit
            (materialConfigurationFace 2) (materialConfigurationConsumer 2) rfl rfl HEq.rfl
        · exact RootInquiryProcessNode.active_actualAction_successor_valid
            SpinPair.inquiryPresentation (SpinPair.readPresentation 0) PUnit.unit
            SpinPair.generatedAction rfl rfl HEq.rfl
    | native index =>
        refine ⟨.native (index + 1), ?_⟩
        rcases index with _ | _ | _ | index
        · cases query
          exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (SpinPair.readPresentation 0) (Stage9CU.Runtime.weakPresentation 1)
            PUnit.unit (SpinPair.configurationFace 1)
            (SpinPair.configurationConsumer 1) rfl rfl HEq.rfl
        · cases query
          exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (Stage9CU.Runtime.weakPresentation 1) (SpinPair.readPresentation 2)
            PUnit.unit (Stage9CU.Runtime.weakFace 2)
            (Stage9CU.Runtime.weakConsumer 2) rfl rfl HEq.rfl
        · cases query
          exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (SpinPair.readPresentation 2) (Stage9DEF.Runtime.quantumPresentation 3)
            PUnit.unit (SpinPair.configurationFace 3)
            (SpinPair.configurationConsumer 3) rfl rfl HEq.rfl
        · cases query
          exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
            (Stage9DEF.Runtime.quantumPresentation (index + 3))
            (Stage9DEF.Runtime.quantumPresentation (index + 4))
            PUnit.unit (Stage9DEF.Runtime.quantumFace (index + 4))
            (Stage9DEF.Runtime.quantumConsumer (index + 4)) rfl rfl HEq.rfl

private def initialQuery :
    (physicalInquiryProcess.stateAt physicalInquiryProcess.initial).Query := PUnit.unit

private theorem initialQuery_unique
    (query : (physicalInquiryProcess.stateAt physicalInquiryProcess.initial).Query) :
    query = initialQuery := by cases query; rfl

private theorem query_type (state : SpinPair.RuntimeState) :
    (physicalInquiryProcess.stateAt state).Query = PUnit := by
  cases state with
  | history index => fin_cases index <;> rfl
  | native index => rcases index with _ | _ | _ | index <;> rfl

private def nextQuery (state : SpinPair.RuntimeState)
    (query : (physicalInquiryProcess.stateAt state).Query) :
    (physicalInquiryProcess.stateAt
      (physicalInquiryProcess.successorAt state query).1).Query :=
  (query_type _).symm ▸ PUnit.unit

private theorem nextQuery_unique (state : SpinPair.RuntimeState)
    (query : (physicalInquiryProcess.stateAt state).Query)
    (candidate : (physicalInquiryProcess.stateAt
      (physicalInquiryProcess.successorAt state query).1).Query) :
    candidate = nextQuery state query := by
  cases state with
  | history index => fin_cases index <;> cases candidate <;> rfl
  | native index => rcases index with _ | _ | _ | index <;> cases candidate <;> rfl

/-- The only named macro runtime; its seed is the original physical root. -/
def physicalInquiryRuntime : SourceNativeInquiryRuntime physicalInquiryProcess where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    initialQuery initialQuery_unique nextQuery nextQuery_unique

theorem physicalInquiryRuntime_seed_eq_physicalRuntimeSeed :
    (physicalInquiryRuntime.initialState.engine.node).erase =
      (⟨OldN, physicalRuntimeSeed.current.erase⟩ : AnyAuthoritativeRootCurrent) :=
  rfl

def firstAssemblyInquiryTick := physicalInquiryRuntime.tickAt 3

theorem firstAssemblyInquiryTick_action :
    firstAssemblyInquiryTick.resolution = .actualAction firstAssemblyGeneratedCartanAction :=
  rfl

theorem firstAssemblyInquiryTick_resumes_generated_material :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      firstAssemblyGeneratedCartanAction physicalInquiryRuntime 3 where
  contains_action := by
    rw [firstAssemblyInquiryTick_action]
    exact HEq.rfl

theorem firstAssemblyInquiryTick_next :
    firstAssemblyInquiryTick.next.node.erase =
      ⟨MaterialN, firstAssemblyGeneratedCartanAction.target.targetAnswerAndNext.nextCurrent⟩ :=
  firstAssemblyInquiryTick.next_erases_to_generated

def firstMaterialInquiryTick := physicalInquiryRuntime.tickAt 4

theorem firstMaterialInquiryTick_native_answer :
    firstMaterialInquiryTick.resolution =
      .directlyAnswered (materialConfigurationFace 1) (materialConfigurationConsumer 1) :=
  rfl

theorem firstMaterialInquiryTick_next :
    firstMaterialInquiryTick.next.node.erase =
      (materialInquiryPresentation 1).erase :=
  rfl

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision
