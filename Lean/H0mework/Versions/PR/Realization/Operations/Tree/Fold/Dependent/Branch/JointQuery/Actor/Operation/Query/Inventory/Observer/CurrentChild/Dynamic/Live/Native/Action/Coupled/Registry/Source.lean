import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Continuation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
namespace Observation
theorem root_congr {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
 {first second : SourceNativeLivingRootClosure N V} (same : first=second) (ast : Shape)
 (terminalEmpty : (current : V.Current) → IsEmpty (V.FaithfulTerminalAt current)) :
 root first.toAuthoritativeRoot ast terminalEmpty=root second.toAuthoritativeRoot ast terminalEmpty :=
 congrArg (fun live => root live.toAuthoritativeRoot ast terminalEmpty) same
theorem canonical_next_congr {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
 {first second : SourceNativeLivingRootClosure N V} (same : first=second) :
 first.generatedNextCurrentAt (.finite first.toAuthoritativeRoot.toRoot.initialVisit)=
 second.generatedNextCurrentAt (.finite second.toAuthoritativeRoot.toRoot.initialVisit) :=
 congrArg (fun live => live.generatedNextCurrentAt (.finite live.toAuthoritativeRoot.toRoot.initialVisit)) same
end Observation
namespace Parent
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled
 (initial configuration frameAt targetAt target_root sourceSeed)
end Parent
section InitialNext
variable {S : Type u} {Value Var : S → Type u} [∀ s,AddCommGroup (Value s)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=s))
theorem canonical_initial_next :
 (observedRoot frame cfg).generatedNextCurrentAt (.finite (observedRoot frame cfg).toAuthoritativeRoot.toRoot.initialVisit)=
 ⟨C.JointV frame.registered frame.packetAt,(observedRoot frame cfg).toAuthoritativeRoot,visitAt frame cfg 1⟩ := by
 apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
 rfl
end InitialNext
namespace Boot
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (rootVisit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root rootVisit rec slot) := inferInstance
abbrev frame:=Rep.sourceFrame root rootVisit rec U7 calculus anchor sourceStage stage
abbrev programme:=Rep.configuration root rootVisit rec U7 calculus anchor sourceStage
abbrev initial:=Parent.initial root rootVisit rec U7 calculus anchor sourceStage stage
abbrev targetConfiguration:=Parent.configuration root rootVisit rec U7 calculus anchor sourceStage stage
abbrev sourceRoot:=observedRoot (frame root rootVisit rec U7 calculus anchor sourceStage stage)
 (programme root rootVisit rec U7 calculus anchor sourceStage)
abbrev sourceVisit:=Registry.visit (frame root rootVisit rec U7 calculus anchor sourceStage stage)
 (programme root rootVisit rec U7 calculus anchor sourceStage)
abbrev sourceAuthority:=Registry.authority (frame root rootVisit rec U7 calculus anchor sourceStage stage)
 (programme root rootVisit rec U7 calculus anchor sourceStage)
abbrev query:=Registry.query (frame root rootVisit rec U7 calculus anchor sourceStage stage)
 (programme root rootVisit rec U7 calculus anchor sourceStage)
abbrev entry:=(frame root rootVisit rec U7 calculus anchor sourceStage stage).currentState.entryAt PUnit.unit
abbrev Event:=ExactTemporalCausalRootEventAt (sourceRoot root rootVisit rec U7 calculus anchor sourceStage stage).toAuthoritativeRoot.toLedgerRoot
 (sourceVisit root rootVisit rec U7 calculus anchor sourceStage stage)

def targetAt (event : Event root rootVisit rec U7 calculus anchor sourceStage stage) :
 SourceNativeDebtAdmissionActualActionTargetAt (sourceRoot root rootVisit rec U7 calculus anchor sourceStage stage)
 (sourceVisit root rootVisit rec U7 calculus anchor sourceStage stage) event
 (entry root rootVisit rec U7 calculus anchor sourceStage stage) (sourceAuthority root rootVisit rec U7 calculus anchor sourceStage stage) :=
 Observation.target (oldRoot:=Shared.root (frame root rootVisit rec U7 calculus anchor sourceStage stage)
   (programme root rootVisit rec U7 calculus anchor sourceStage))
  (oldVisit:=sourceVisit root rootVisit rec U7 calculus anchor sourceStage stage) (oldEvent:=event)
  (oldEntry:=entry root rootVisit rec U7 calculus anchor sourceStage stage)
  (oldAuthority:=SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.authority
   (frame root rootVisit rec U7 calculus anchor sourceStage stage) (programme root rootVisit rec U7 calculus anchor sourceStage))
  (shape (frame root rootVisit rec U7 calculus anchor sourceStage stage).rawRead.expression)
  (noFaithful (frame root rootVisit rec U7 calculus anchor sourceStage stage))
  (sourceAuthority root rootVisit rec U7 calculus anchor sourceStage stage)
  (Parent.targetAt root rootVisit rec U7 calculus anchor sourceStage stage event)
  (shape (initial root rootVisit rec U7 calculus anchor sourceStage stage).rawRead.expression)
  (noFaithful (initial root rootVisit rec U7 calculus anchor sourceStage stage))

theorem target_root (event : Event root rootVisit rec U7 calculus anchor sourceStage stage) :
 (targetAt root rootVisit rec U7 calculus anchor sourceStage stage event).targetRoot=
 observedRoot (initial root rootVisit rec U7 calculus anchor sourceStage stage)
  (targetConfiguration root rootVisit rec U7 calculus anchor sourceStage stage) :=
 Observation.root_congr (Parent.target_root root rootVisit rec U7 calculus anchor sourceStage stage event)
  (shape (initial root rootVisit rec U7 calculus anchor sourceStage stage).rawRead.expression)
  (noFaithful (initial root rootVisit rec U7 calculus anchor sourceStage stage))

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt (sourceRoot root rootVisit rec U7 calculus anchor sourceStage stage)
 (sourceVisit root rootVisit rec U7 calculus anchor sourceStage stage)
 (entry root rootVisit rec U7 calculus anchor sourceStage stage) (sourceAuthority root rootVisit rec U7 calculus anchor sourceStage stage) where
 targetAt:=targetAt root rootVisit rec U7 calculus anchor sourceStage stage
abbrev sourceEvent:=(sourceRoot root rootVisit rec U7 calculus anchor sourceStage stage).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
 (sourceVisit root rootVisit rec U7 calculus anchor sourceStage stage)
abbrev generatedAction:=(birthProgram root rootVisit rec U7 calculus anchor sourceStage stage).generate
 (sourceEvent root rootVisit rec U7 calculus anchor sourceStage stage)

def compilation (candidate : Germ (frame root rootVisit rec U7 calculus anchor sourceStage stage)
 (programme root rootVisit rec U7 calculus anchor sourceStage)) : SourceNativeInquiryCompilationProgramAt
 (sourceRoot root rootVisit rec U7 calculus anchor sourceStage stage) (sourceVisit root rootVisit rec U7 calculus anchor sourceStage stage)
 (Original.base (frame root rootVisit rec U7 calculus anchor sourceStage stage)).U7
 (Original.base (frame root rootVisit rec U7 calculus anchor sourceStage stage)).calculus
 (sourceRoot root rootVisit rec U7 calculus anchor sourceStage stage).source.base.lawSurface candidate
 (ULift.up.{u+1,u} (Original.actualOccurrence (frame root rootVisit rec U7 calculus anchor sourceStage stage)))
 (entry root rootVisit rec U7 calculus anchor sourceStage stage) (sourceAuthority root rootVisit rec U7 calculus anchor sourceStage stage) where
 compile:=fun event => by
  cases Original.query_unique (frame root rootVisit rec U7 calculus anchor sourceStage stage)
   (programme root rootVisit rec U7 calculus anchor sourceStage) candidate
  exact .debtAdmission ((birthProgram root rootVisit rec U7 calculus anchor sourceStage stage).generate event)

def state : RootInquiryStateAt
 (C.World (frame root rootVisit rec U7 calculus anchor sourceStage stage).registered)
 (C.JointV (frame root rootVisit rec U7 calculus anchor sourceStage stage).registered
  (frame root rootVisit rec U7 calculus anchor sourceStage stage).packetAt) where
 root:=sourceRoot root rootVisit rec U7 calculus anchor sourceStage stage
 visit:=sourceVisit root rootVisit rec U7 calculus anchor sourceStage stage
 U7:=(Original.base (frame root rootVisit rec U7 calculus anchor sourceStage stage)).U7
 calculus:=(Original.base (frame root rootVisit rec U7 calculus anchor sourceStage stage)).calculus
 Query:=Germ (frame root rootVisit rec U7 calculus anchor sourceStage stage) (programme root rootVisit rec U7 calculus anchor sourceStage)
 entryAt:=fun _ => entry root rootVisit rec U7 calculus anchor sourceStage stage
 authorityAt:=fun _ => sourceAuthority root rootVisit rec U7 calculus anchor sourceStage stage
 compilationProgramAt:=compilation root rootVisit rec U7 calculus anchor sourceStage stage
 compilationFaceAt:=fun candidate => by
  cases Original.query_unique (frame root rootVisit rec U7 calculus anchor sourceStage stage)
   (programme root rootVisit rec U7 calculus anchor sourceStage) candidate
  exact {projection:=(Original.compilationInstallation (frame root rootVisit rec U7 calculus anchor sourceStage stage)
           (programme root rootVisit rec U7 calculus anchor sourceStage)).embed PUnit.unit
         active:=PUnit.unit
         classifier_eq:=rfl
         project_heq:=HEq.rfl}
 u7RootDisposition_commutes:=by
  intro candidate _ _ impossible
  cases Original.query_unique (frame root rootVisit rec U7 calculus anchor sourceStage stage)
   (programme root rootVisit rec U7 calculus anchor sourceStage) candidate
  exact nomatch impossible

def presentation : RootInquiryStatePresentation where
 N:=C.World (frame root rootVisit rec U7 calculus anchor sourceStage stage).registered
 V:=C.JointV (frame root rootVisit rec U7 calculus anchor sourceStage stage).registered
  (frame root rootVisit rec U7 calculus anchor sourceStage stage).packetAt
 state:=.create (state root rootVisit rec U7 calculus anchor sourceStage stage)
abbrev targetPresentation:=Registry.presentation (initial root rootVisit rec U7 calculus anchor sourceStage stage)
 (targetConfiguration root rootVisit rec U7 calculus anchor sourceStage stage)

theorem target_next (event : Event root rootVisit rec U7 calculus anchor sourceStage stage) : type_of%
 ((targetAt root rootVisit rec U7 calculus anchor sourceStage stage event).targetAnswerAndNext_next_eq) :=
 (targetAt root rootVisit rec U7 calculus anchor sourceStage stage event).targetAnswerAndNext_next_eq

theorem canonical_target (event : Event root rootVisit rec U7 calculus anchor sourceStage stage) : type_of%
 (Observation.canonical_next_congr (target_root root rootVisit rec U7 calculus anchor sourceStage stage event)) :=
 Observation.canonical_next_congr (target_root root rootVisit rec U7 calculus anchor sourceStage stage event)

theorem target_current (event : Event root rootVisit rec U7 calculus anchor sourceStage stage) :
 (targetAt root rootVisit rec U7 calculus anchor sourceStage stage event).targetAnswerAndNext.nextCurrent=
 ⟨C.JointV (initial root rootVisit rec U7 calculus anchor sourceStage stage).registered
   (initial root rootVisit rec U7 calculus anchor sourceStage stage).packetAt,
  (observedRoot (initial root rootVisit rec U7 calculus anchor sourceStage stage)
   (targetConfiguration root rootVisit rec U7 calculus anchor sourceStage stage)).toAuthoritativeRoot,
  Registry.visit (initial root rootVisit rec U7 calculus anchor sourceStage stage)
   (targetConfiguration root rootVisit rec U7 calculus anchor sourceStage stage)⟩ :=
 (canonical_target root rootVisit rec U7 calculus anchor sourceStage stage event).trans
  (canonical_initial_next (initial root rootVisit rec U7 calculus anchor sourceStage stage)
   (targetConfiguration root rootVisit rec U7 calculus anchor sourceStage stage))

theorem compiles : (state root rootVisit rec U7 calculus anchor sourceStage stage).compileInquiry
 (query root rootVisit rec U7 calculus anchor sourceStage stage)=
 .debtAdmission (generatedAction root rootVisit rec U7 calculus anchor sourceStage stage) := rfl

theorem successor_valid (candidate : (presentation root rootVisit rec U7 calculus anchor sourceStage stage).Query) :
 (targetPresentation root rootVisit rec U7 calculus anchor sourceStage stage).erase=
 (RootInquiryProcessNode.answered (presentation root rootVisit rec U7 calculus anchor sourceStage stage) candidate).erase ∧
 (.active (presentation root rootVisit rec U7 calculus anchor sourceStage stage) : RootInquiryProcessNode).PreservesGeneratedLivingLawAt
 candidate (.active (targetPresentation root rootVisit rec U7 calculus anchor sourceStage stage)) := by
 cases Original.query_unique (frame root rootVisit rec U7 calculus anchor sourceStage stage)
  (programme root rootVisit rec U7 calculus anchor sourceStage) candidate
 apply RootInquiryProcessNode.active_debtAdmission_successor_valid
  (presentation root rootVisit rec U7 calculus anchor sourceStage stage)
  (targetPresentation root rootVisit rec U7 calculus anchor sourceStage stage)
  (query root rootVisit rec U7 calculus anchor sourceStage stage)
  (generatedAction root rootVisit rec U7 calculus anchor sourceStage stage)
  (compiles root rootVisit rec U7 calculus anchor sourceStage stage)
 · exact (congrArg (fun current =>
    (⟨C.World (initial root rootVisit rec U7 calculus anchor sourceStage stage).registered,current⟩ : AnyAuthoritativeRootCurrent.{u}))
   (target_current root rootVisit rec U7 calculus anchor sourceStage stage
    (sourceEvent root rootVisit rec U7 calculus anchor sourceStage stage))).symm
 · exact heq_of_eq (target_root root rootVisit rec U7 calculus anchor sourceStage stage
    (sourceEvent root rootVisit rec U7 calculus anchor sourceStage stage)).symm

theorem boot_tail_separated (offset : Nat) : (presentation root rootVisit rec U7 calculus anchor sourceStage stage).erase≠
 (Registry.presentation (Parent.frameAt root rootVisit rec U7 calculus anchor sourceStage stage offset)
 (targetConfiguration root rootVisit rec U7 calculus anchor sourceStage stage)).erase :=
 first_tail_separated (frame root rootVisit rec U7 calculus anchor sourceStage stage)
  (programme root rootVisit rec U7 calculus anchor sourceStage)
  (initial root rootVisit rec U7 calculus anchor sourceStage stage)
  (targetConfiguration root rootVisit rec U7 calculus anchor sourceStage stage)
  (Rep.receiver_strict root rootVisit rec U7 calculus anchor sourceStage stage) offset
end Boot
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
