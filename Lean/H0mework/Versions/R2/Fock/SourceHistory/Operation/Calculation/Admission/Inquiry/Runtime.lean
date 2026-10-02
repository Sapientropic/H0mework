import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Program

/-! The existing macro runtime consumes the birth and then the actual joint
normalization writes. Every query activation belongs to its generated next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry

open RootInquiryCompletion
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

variable (runtime : LivingRuntimeState process)

inductive Phase
  | birth
  | math (depth : Nat)

def presentationAt : Phase → RootInquiryStatePresentation
  | .birth => birthPresentation runtime
  | .math depth => mathPresentation runtime depth

private def erasedDepth (current : AnyAuthoritativeRootCurrent) : Option Nat :=
  match current.current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

private theorem finiteDepth (count : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth (Unit.finiteVisit (registered runtime) count).history = count := by
  induction count with
  | zero => rfl
  | succ count prior =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (Unit.finiteVisit (registered runtime) count).history + 1 = count + 1
      rw [prior]

private theorem math_erased_depth (depth : Nat) :
    erasedDepth (mathPresentation runtime depth).erase = some (depth + 1) :=
  congrArg some (finiteDepth runtime (depth + 1))

private theorem networks_distinct : OldN ≠ NewN runtime := by
  intro same
  have types := congrArg WorldRelationNetwork.Claim same
  have singleton : Subsingleton (NewN runtime).Claim := types ▸ (by change Subsingleton PUnit; infer_instance)
  have impossible := @Subsingleton.elim _ singleton (Sum.inl PUnit.unit)
    (Sum.inr (registered runtime).input.expression)
  cases impossible

theorem presentationAt_erase_injective : Function.Injective (fun phase => (presentationAt runtime phase).erase) := by
  intro first second same
  cases first with
  | birth =>
      cases second with
      | birth => rfl
      | math depth => exact False.elim (networks_distinct runtime (congrArg AnyAuthoritativeRootCurrent.N same))
  | math first =>
      cases second with
      | birth => exact False.elim (networks_distinct runtime (congrArg AnyAuthoritativeRootCurrent.N same).symm)
      | math second =>
          have depthEq := congrArg erasedDepth same
          change erasedDepth (mathPresentation runtime first).erase =
            erasedDepth (mathPresentation runtime second).erase at depthEq
          rw [math_erased_depth, math_erased_depth] at depthEq
          exact congrArg Phase.math (Nat.add_right_cancel (Option.some.inj depthEq))

set_option linter.defProp false in
def birth_successor :=
  RootInquiryProcessNode.active_debtAdmission_successor_valid
    (birthPresentation runtime) (mathPresentation runtime 0) PUnit.unit (birthGenerated runtime)
    (birth_compiles runtime)
    (by
      exact congrArg (fun current => (⟨NewN runtime, current⟩ : AnyAuthoritativeRootCurrent))
        (birthGenerated runtime |>.target.targetAnswerAndNext_next_eq).symm)
    HEq.rfl

set_option linter.defProp false in
def math_successor (depth : Nat) :=
  RootInquiryProcessNode.active_directlyAnswered_successor_valid
    (mathPresentation runtime depth) (mathPresentation runtime (depth + 1)) PUnit.unit
    (mathAnswerFace runtime depth) (mathConsumer runtime depth) (math_compiles runtime depth)
    (by
      apply congrArg (fun current => (⟨NewN runtime, current⟩ : AnyAuthoritativeRootCurrent))
      symm
      apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
      rfl)
    (by change HEq (targetRoot runtime) (targetRoot runtime); rfl)

def inquiryProcess : SourceNativeInquiryEngineProcess where
  State := Phase
  stateAt := fun phase => .active (presentationAt runtime phase)
  erase_injective := by
    intro first second firstState secondState firstActive secondActive same
    cases firstActive
    cases secondActive
    exact presentationAt_erase_injective runtime same
  initial := .birth
  successorAt := by
    intro phase query
    cases phase with
    | birth => cases query; exact ⟨.math 0, birth_successor runtime⟩
    | math depth => cases query; exact ⟨.math (depth + 1), math_successor runtime depth⟩

def initialQuery : ((inquiryProcess runtime).stateAt (inquiryProcess runtime).initial).Query := PUnit.unit

theorem initialQuery_unique (candidate : ((inquiryProcess runtime).stateAt (inquiryProcess runtime).initial).Query) :
    candidate = initialQuery runtime := by cases candidate; rfl

def nextQueryAt (phase : Phase) (query : ((inquiryProcess runtime).stateAt phase).Query) :
    ((inquiryProcess runtime).stateAt ((inquiryProcess runtime).successorAt phase query).1).Query := by
  cases phase <;> cases query <;> exact PUnit.unit

theorem nextQuery_unique (phase : Phase) (query : ((inquiryProcess runtime).stateAt phase).Query)
    (candidate : ((inquiryProcess runtime).stateAt ((inquiryProcess runtime).successorAt phase query).1).Query) :
    candidate = nextQueryAt runtime phase query := by
  cases phase <;> cases query <;> cases candidate <;> rfl

def inquiryRuntime : SourceNativeInquiryRuntime (inquiryProcess runtime) where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    (initialQuery runtime) (initialQuery_unique runtime) (nextQueryAt runtime) (nextQuery_unique runtime)

def firstTick := (inquiryRuntime runtime).tickAt 0

theorem initial_resolution : (firstTick runtime).resolution = .debtAdmission (birthGenerated runtime) := rfl

theorem initial_resolution_kind : (firstTick runtime).resolutionKind = .debtAdmission := by
  rw [SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.resolutionKind, initial_resolution]
  rfl

theorem initial_next : (firstTick runtime).next.node.erase =
    ⟨NewN runtime, (birthGenerated runtime).target.targetAnswerAndNext.nextCurrent⟩ :=
  (firstTick runtime).next_erases_to_generated

theorem initial_next_living_law : HEq (mathPresentation runtime 0).state.base.root
    (birthGenerated runtime).target.targetRoot := (firstTick runtime).next_preservesGeneratedLivingLaw

private theorem next_node_math (depth : Nat) (engine : Engine (inquiryProcess runtime))
    (same : engine.node = .active (mathPresentation runtime depth))
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    (engine.ask activation).next.node = .active (mathPresentation runtime (depth + 1)) := by
  rcases engine with ⟨phase⟩
  have samePresentation : presentationAt runtime phase = mathPresentation runtime depth :=
    RootInquiryProcessNode.active.inj same
  have phaseEq : phase = .math depth := presentationAt_erase_injective runtime
    (congrArg RootInquiryStatePresentation.erase samePresentation)
  subst phase
  rcases activation with ⟨query⟩
  cases query
  rfl

theorem stateAt_afterBirth_node (depth : Nat) :
    ((inquiryRuntime runtime).stateAt (depth + 1)).engine.node =
      .active (mathPresentation runtime depth) := by
  induction depth with
  | zero => rfl
  | succ depth prior =>
      exact next_node_math runtime depth ((inquiryRuntime runtime).stateAt (depth + 1)).engine
        prior ((inquiryRuntime runtime).stateAt (depth + 1)).activation

theorem bornResumption : SourceNativeInquiryRuntime.DebtAdmissionActualActionResumptionAt
    (birthGenerated runtime) (inquiryRuntime runtime) 0 where
  contains_action := by rw [initial_resolution]; exact HEq.rfl

end
end SourcePhysicalCalculationAdmission.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
