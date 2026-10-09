import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot, AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Act.LowValue root visit rec) (Act.LowVar root visit rec) (Act.sort root rec))))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Act.LowValue root visit rec) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
variable (sourceStage stage : Nat)
def nextCount (currentFrame : LowFrame root visit rec) (count : Nat) :=
 match currentFrame.action with | .inr _ => count | .inl _ => count+1
def birthCount : Nat → Nat
 | 0 => D.Parent.birthCount root visit rec U7 calculus anchor sourceStage stage
 | offset+1 => nextCount root visit rec
  (frameAt root visit rec U7 calculus anchor sourceStage stage offset) (birthCount offset)

abbrev CorePair :=
 (SourceOperationNative.Tree.Fold.Dependent.Branch.Node root visit rec →₀ ℤ) ×
 (SourceOperationNative.Tree.Fold.Dependent.Branch.Node root visit rec →₀ ℤ)
@[reducible] def coreRead (environment : Env (Act.LowValue root visit rec) (Act.LowVar root visit rec))
 (datum : SourceOperationNative.Tree.Fold.Dependent.Branch.Node root visit rec) : CorePair root visit rec :=
 (environment (D.coreSlot root rec) (.inr (datum,.old))).1 (0:Fin 2)
def UniformAt (currentFrame : LowFrame root visit rec) (count : Nat) : Prop :=
 ∀ (current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered)
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence currentFrame (current:=current))
 (datum : SourceOperationNative.Tree.Fold.Dependent.Branch.Node root visit rec),
 coreRead root visit rec (Act.actualEnvironment root visit rec currentFrame supplied) datum=
 D.orbitPair root visit rec count datum

theorem right_binding
 (environment : Env (Act.LowValue root visit rec) (Act.LowVar root visit rec))
 (slot) (name : Act.PhysicalVar root visit rec slot) :
 SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment (Act.lowBinding root visit rec) environment slot (.inr name)=
 ((SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.binding root visit rec slot name).eval
   (fun target variableName => (environment target (.inr variableName)).1),
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.binding root visit rec slot name).effect
   (fun target variableName => (environment target (.inr variableName)).1)
   (fun target variableName => (environment target (.inr variableName)).2)) := by
 change (D.Low.right (liftExpr _)).eval environment=_
 exact (Expr.eval_subst _ _ _).trans (eval_liftExpr _ _ _)

theorem core_binding
 (environment : Env (Act.LowValue root visit rec) (Act.LowVar root visit rec))
 (datum : SourceOperationNative.Tree.Fold.Dependent.Branch.Node root visit rec) :
 coreRead root visit rec
  (SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment (Act.lowBinding root visit rec) environment) datum=
 coreRead root visit rec environment
  (SourceOperationNative.Tree.Fold.Dependent.Branch.nextNode root visit rec datum) := by
 unfold coreRead
 rw [right_binding]
 rfl

theorem born_actual_environment
 {nextCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
  (A.Shared.nextBorn frame (configuration root visit rec U7 calculus anchor seed)).registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence
  (A.Shared.nextBorn frame (configuration root visit rec U7 calculus anchor seed)) (current:=nextCurrent)) :
 Act.actualEnvironment root visit rec
  (A.Shared.nextBorn frame (configuration root visit rec U7 calculus anchor seed)) supplied =
 Act.physicalNext root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame) := rfl

theorem frames_succ (offset : Nat) :
 frameAt root visit rec U7 calculus anchor sourceStage stage (offset+1)=
 A.Shared.next (frameAt root visit rec U7 calculus anchor sourceStage stage offset)
  (sourceConfiguration root visit rec U7 calculus anchor sourceStage stage) := rfl

theorem uniform_next (count : Nat) (uniform : UniformAt root visit rec frame count) :
 UniformAt root visit rec (A.Shared.next frame (configuration root visit rec U7 calculus anchor seed))
  (nextCount root visit rec frame count) := by
 unfold nextCount
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 cases selected : frame.action with
 | inr paid => exact uniform
 | inl settled =>
  intro current supplied datum
  have source := congrArg (fun environment => coreRead root visit rec environment datum)
   (born_actual_environment root visit rec U7 calculus anchor seed frame supplied)
  have shifted := core_binding root visit rec
   (Act.actualEnvironment root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame)) datum
  have prior := uniform _ (A.Shared.actualOccurrence frame)
   (SourceOperationNative.Tree.Fold.Dependent.Branch.nextNode root visit rec datum)
  have orbit : D.orbitPair root visit rec count
    (SourceOperationNative.Tree.Fold.Dependent.Branch.nextNode root visit rec datum)=
    D.orbitPair root visit rec (count+1) datum := by
   unfold D.orbitPair
   rw [←Function.iterate_succ_apply,←Function.iterate_succ_apply]
  exact source.trans (shifted.trans (prior.trans orbit))

theorem uniform_source (offset : Nat) : UniformAt root visit rec
 (frameAt root visit rec U7 calculus anchor sourceStage stage offset)
 (birthCount root visit rec U7 calculus anchor sourceStage stage offset) := by
 induction offset with
 | zero =>
  intro current supplied datum
  change SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.environmentAt root visit rec
   (A.epoch (Act.Owned.sourceFrame root visit rec U7 calculus anchor sourceStage stage))
   (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
    (initial root visit rec U7 calculus anchor sourceStage stage).registered
    (initial root visit rec U7 calculus anchor sourceStage stage).packetAt supplied)
   (D.coreSlot root rec) (datum,.old) (0:Fin 2)=_
  exact D.Parent.Origin.uniform_origin root visit rec U7 calculus anchor sourceStage stage _ _ datum
 | succ offset previous =>
  rw [frames_succ]
  dsimp only [sourceConfiguration,birthCount]
  exact uniform_next root visit rec U7 calculus anchor (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
   (frameAt root visit rec U7 calculus anchor sourceStage stage offset)
   (birthCount root visit rec U7 calculus anchor sourceStage stage offset) previous

theorem actor_word_of_uniform (count : Nat) (uniform : UniformAt root visit rec frame count) :
 actorWord root visit rec frame actual = Finsupp.single (D.actorAtCount root visit rec (count+1)) 1 := by
 have paidRead : actorWord root visit rec frame actual=
  ((Child.actorTerm root visit rec).eval (Act.rightOldEnvironment root visit rec frame actual)).2.1.2.1+
  ((Child.actorTerm root visit rec).eval (Act.rightOldEnvironment root visit rec frame actual)).2.1.2.2 :=
  congrArg (fun output : Child.Output root visit rec => output.2.1.2.1+output.2.1.2.2)
   (actor_value root visit rec frame actual)
 have actors := D.actor_projection_eval root visit rec
  (Act.rightOldEnvironment root visit rec frame actual) count (fun datum => uniform _ actual datum)
 have summed := congrArg (fun pair :
  (Child.SourceActor root rec →₀ ℤ) × (Child.SourceActor root rec →₀ ℤ) => pair.1+pair.2) actors
 have cancellation : Finsupp.single (D.actorAtCount root visit rec count) (1:ℤ)+
  (Finsupp.single (D.actorAtCount root visit rec (count+1)) (1:ℤ)-
   Finsupp.single (D.actorAtCount root visit rec count) (1:ℤ))=
  Finsupp.single (D.actorAtCount root visit rec (count+1)) (1:ℤ) := by abel
 exact paidRead.trans (summed.trans cancellation)

theorem actor_word_source (offset : Nat) :
 actorWord root visit rec (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset))=
 Finsupp.single (D.actorAtCount root visit rec
  (birthCount root visit rec U7 calculus anchor sourceStage stage offset+1)) 1 :=
 actor_word_of_uniform root visit rec
  (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (birthCount root visit rec U7 calculus anchor sourceStage stage offset)
  (uniform_source root visit rec U7 calculus anchor sourceStage stage offset)

theorem support_source (offset : Nat) :
 support root visit rec (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset))=
 [D.actorAtCount root visit rec (birthCount root visit rec U7 calculus anchor sourceStage stage offset+1)] := by
 classical
 unfold support
 rw [actor_word_source]
 simp


end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
