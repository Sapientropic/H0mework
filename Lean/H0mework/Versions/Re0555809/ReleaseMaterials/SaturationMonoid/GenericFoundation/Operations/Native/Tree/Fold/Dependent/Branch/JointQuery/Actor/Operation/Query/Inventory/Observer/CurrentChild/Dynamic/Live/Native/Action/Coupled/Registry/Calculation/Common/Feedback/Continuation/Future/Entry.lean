import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.First
import H0mework.Versions.Re0555809.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.History
import H0mework.Versions.Re0555809.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Installed
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
open CategoryTheory CategoryTheory.Limits SourceGeneratedScalarCofinalKernelCompletion
namespace Future.Entry
namespace Join
variable {G F B : Type u} [AddCommGroup G] [AddCommGroup F] [AddCommGroup B]
variable {C : Nat → Type u} [∀ k,AddCommGroup (C k)]
variable (native : Data (R:=ℤ) (Generator:=F) (Carrier:=C))
variable (firstRead : G →ₗ[ℤ] B) (lift : G →ₗ[ℤ] F)
def Prefix (bound : Nat) : Type u := match bound with
 | 0 => B
 | k+1 => B × C k
@[instance_reducible] local instance prefixGroup (bound : Nat) : AddCommGroup (Prefix (B:=B) (C:=C) bound) :=
 match bound with
 | 0 => inferInstanceAs (AddCommGroup B)
 | k+1 => inferInstanceAs (AddCommGroup (B × C k))
def evaluator : (bound : Nat) → G →ₗ[ℤ] Prefix (B:=B) (C:=C) bound
 | 0 => firstRead
 | k+1 => firstRead.prod ((native.evaluator k).comp lift)
def restriction : (bound : Nat) → Prefix (B:=B) (C:=C) (bound+1) →ₗ[ℤ] Prefix (B:=B) (C:=C) bound
 | 0 => LinearMap.fst ℤ B (C 0)
 | k+1 => (LinearMap.fst ℤ B (C (k+1))).prod ((native.transition k).comp (LinearMap.snd ℤ B (C (k+1))))
def data : Data (R:=ℤ) (Generator:=G) (Carrier:=Prefix (B:=B) (C:=C)) where
 evaluator:=evaluator native firstRead lift
 transition:=restriction native
variable (law : native.Compatible)
include law in
theorem compatible : (data native firstRead lift).Compatible := by
 intro bound
 cases bound with
 | zero => apply LinearMap.ext; intro value; rfl
 | succ k =>
  apply LinearMap.ext
  intro value
  exact Prod.ext rfl (LinearMap.congr_fun (law k) (lift value))
def completion := (data native firstRead lift).Completion (compatible native firstRead lift law)
def sourceMap : G →ₗ[ℤ] completion native firstRead lift law :=
 ((data native firstRead lift).completionMap (compatible native firstRead lift law)).hom
def readPrefix (bound : Nat) : completion native firstRead lift law →ₗ[ℤ] Prefix (B:=B) (C:=C) bound :=
 ((data native firstRead lift).stageRealization bound).comp
 (((data native firstRead lift).restriction (compatible native firstRead lift law) bound).hom)
theorem source_prefix (bound : Nat) (value : G) :
 readPrefix native firstRead lift law bound (sourceMap native firstRead lift law value)=evaluator native firstRead lift bound value :=
 ConcreteCategory.congr_hom ((data native firstRead lift).source_to_evaluator (compatible native firstRead lift law) bound) value

theorem source_fibre (left right : G) : sourceMap native firstRead lift law left=sourceMap native firstRead lift law right ↔
 firstRead left=firstRead right ∧ ∀ k,native.evaluator k (lift left)=native.evaluator k (lift right) := by
 constructor
 · intro same
   constructor
   · have observed:=congrArg (fun value => readPrefix native firstRead lift law 0 value) same
     rw [source_prefix,source_prefix] at observed
     exact observed
   · intro k
     have observed:=congrArg (fun value => (readPrefix native firstRead lift law (k+1) value).2) same
     rw [source_prefix,source_prefix] at observed
     exact observed
 · intro observed
   apply Limits.Concrete.limit_ext ((data native firstRead lift).quotientTower (compatible native firstRead lift law))
   intro bound
   have leftRead:=ConcreteCategory.congr_hom ((data native firstRead lift).completionMap_restriction (compatible native firstRead lift law) bound.unop) left
   have rightRead:=ConcreteCategory.congr_hom ((data native firstRead lift).completionMap_restriction (compatible native firstRead lift law) bound.unop) right
   have quot : (data native firstRead lift).quotientMap bound.unop left=(data native firstRead lift).quotientMap bound.unop right := by
    apply (data native firstRead lift).stageRealization_injective bound.unop
    cases bound.unop with
    | zero => exact observed.1
    | succ k => exact Prod.ext observed.1 (observed.2 k)
   exact leftRead.trans (quot.trans rightRead.symm)

def historyMorphism : SourceGeneratedScalarCofinalNaturality.Morphism
 (SourceGeneratedScalarCofinalTail.tail (data native firstRead lift)) native where
 generatorMap:=lift
 stageMap k:=LinearMap.snd ℤ B (C k)
 transition_naturality k:=by apply LinearMap.ext; intro value; rfl
 evaluator_naturality k:=by apply LinearMap.ext; intro value; rfl
def successor : completion native firstRead lift law →ₗ[ℤ] native.Completion law :=
 ((historyMorphism native firstRead lift).completionMorphism
  (SourceGeneratedScalarCofinalTail.compatible (data native firstRead lift) (compatible native firstRead lift law)) law).hom.comp
 (SourceGeneratedScalarCofinalTail.completionMap (data native firstRead lift) (compatible native firstRead lift law)).hom
theorem successor_source (value : G) : successor native firstRead lift law (sourceMap native firstRead lift law value)=
 (native.completionMap law).hom (lift value) := by
 have tail:=ConcreteCategory.congr_hom (SourceGeneratedScalarCofinalTail.completionMap_source
  (data native firstRead lift) (compatible native firstRead lift law)) value
 have natural:=ConcreteCategory.congr_hom ((historyMorphism native firstRead lift).completionMorphism_source_naturality
  (SourceGeneratedScalarCofinalTail.compatible (data native firstRead lift) (compatible native firstRead lift law)) law) value
 exact (congrArg ((historyMorphism native firstRead lift).completionMorphism
  (SourceGeneratedScalarCofinalTail.compatible (data native firstRead lift) (compatible native firstRead lift law)) law).hom tail).trans natural
end Join
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance sourceGroups : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
local instance entryGroups (n : Nat) (slot : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) :
 AddCommGroup (Lower.Value (Act.LowValue root visit rec) n slot) := Lower.groups (Act.LowValue root visit rec) n slot
local instance pairGroups (slot : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) :
 AddCommGroup (PairValue (Act.LowValue root visit rec) slot) :=
 @Prod.instAddCommGroup _ _ (entryGroups root visit rec 0 slot) (entryGroups root visit rec 0 slot)
local instance pairSlot : AddCommGroup (PairValue (Act.LowValue root visit rec) (Act.sort root rec)) :=
 pairGroups root visit rec (Act.sort root rec)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count : Nat)
abbrev firstFrame:=First.firstFrame root visit rec U7 calculus anchor sourceStage stage count
abbrev cfg:=First.cfg root visit rec U7 calculus anchor sourceStage stage
abbrev Word:=Formal ℤ (PairValue (Act.LowValue root visit rec)) (Act.LowVar root visit rec) (Act.sort root rec)
abbrev Whole:=PairValue (PairValue (Act.LowValue root visit rec)) (Act.sort root rec)
abbrev beforeEnv:=(Future.Q.query (firstFrame root visit rec U7 calculus anchor sourceStage stage count) (cfg root visit rec U7 calculus anchor sourceStage stage)).raw.environment
abbrev afterEnv:=SourceGeneratedInquiryReceiptAction.afterEnvironment
 (firstFrame root visit rec U7 calculus anchor sourceStage stage count) (cfg root visit rec U7 calculus anchor sourceStage stage)
abbrev nextEnv:=(Future.Q.query (actualFrame root visit rec U7 calculus anchor sourceStage stage count 1)
 (actualCfg root visit rec U7 calculus anchor sourceStage stage count 1)).raw.environment
def firstRead := updateInventory (R:=ℤ) (s:=Act.sort root rec)
 (beforeEnv root visit rec U7 calculus anchor sourceStage stage count)
 (afterEnv root visit rec U7 calculus anchor sourceStage stage count-beforeEnv root visit rec U7 calculus anchor sourceStage stage count)
abbrev native:=History.data (firstFrame root visit rec U7 calculus anchor sourceStage stage count)
 (cfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) 0
abbrev nativeLaw:=History.compatible (firstFrame root visit rec U7 calculus anchor sourceStage stage count)
 (cfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) 0
def lift : Word root visit rec →ₗ[ℤ] History.Word (W:=Act.LowValue root visit rec) (X:=Act.LowVar root visit rec) (s:=Act.sort root rec) 0 := liftMap
abbrev data:=Join.data (native root visit rec U7 calculus anchor sourceStage stage count)
 (firstRead root visit rec U7 calculus anchor sourceStage stage count) (lift root visit rec)
abbrev sourceMap:=Join.sourceMap (native root visit rec U7 calculus anchor sourceStage stage count)
 (firstRead root visit rec U7 calculus anchor sourceStage stage count) (lift root visit rec) (nativeLaw root visit rec U7 calculus anchor sourceStage stage count)
abbrev successor:=Join.successor (native root visit rec U7 calculus anchor sourceStage stage count)
 (firstRead root visit rec U7 calculus anchor sourceStage stage count) (lift root visit rec) (nativeLaw root visit rec U7 calculus anchor sourceStage stage count)
theorem actual_prefix (bound : Nat) (word : Word root visit rec) : type_of% (Join.source_prefix
 (native root visit rec U7 calculus anchor sourceStage stage count) (firstRead root visit rec U7 calculus anchor sourceStage stage count)
 (lift root visit rec) (nativeLaw root visit rec U7 calculus anchor sourceStage stage count) bound word) := Join.source_prefix _ _ _ _ _ _
theorem actual_fibre (left right : Word root visit rec) : type_of% (Join.source_fibre
 (native root visit rec U7 calculus anchor sourceStage stage count) (firstRead root visit rec U7 calculus anchor sourceStage stage count)
 (lift root visit rec) (nativeLaw root visit rec U7 calculus anchor sourceStage stage count) left right) := Join.source_fibre _ _ _ _ _ _
theorem actual_successor (word : Word root visit rec) : type_of% (Join.successor_source
 (native root visit rec U7 calculus anchor sourceStage stage count) (firstRead root visit rec U7 calculus anchor sourceStage stage count)
 (lift root visit rec) (nativeLaw root visit rec U7 calculus anchor sourceStage stage count) word) := Join.successor_source _ _ _ _ _
theorem actual_word (word : Word root visit rec) : type_of%
 (LinearMap.congr_fun (Transport.wholeMorphism
  (afterEnv root visit rec U7 calculus anchor sourceStage stage count)
  (nextEnv root visit rec U7 calculus anchor sourceStage stage count)
  (First.actual_first_environment root visit rec U7 calculus anchor sourceStage stage count)
  (beforeEnv root visit rec U7 calculus anchor sourceStage stage count)).commutes word) :=
 LinearMap.congr_fun (Transport.wholeMorphism
  (afterEnv root visit rec U7 calculus anchor sourceStage stage count)
  (nextEnv root visit rec U7 calculus anchor sourceStage stage count)
  (First.actual_first_environment root visit rec U7 calculus anchor sourceStage stage count)
  (beforeEnv root visit rec U7 calculus anchor sourceStage stage count)).commutes word

theorem actual_residual (word : Word root visit rec) : type_of% (Transport.whole_residual
 (afterEnv root visit rec U7 calculus anchor sourceStage stage count) (nextEnv root visit rec U7 calculus anchor sourceStage stage count)
 (First.actual_first_environment root visit rec U7 calculus anchor sourceStage stage count)
 (beforeEnv root visit rec U7 calculus anchor sourceStage stage count) word) := Transport.whole_residual _ _ _ _ _
-- The first pair remains a prefix coordinate; only the successor projection drops it.
theorem actual_consumption (bound : Nat) (word : Word root visit rec) :
 type_of% (actual_prefix root visit rec U7 calculus anchor sourceStage stage count bound word) ∧
 type_of% (actual_word root visit rec U7 calculus anchor sourceStage stage count word) ∧
 type_of% (actual_residual root visit rec U7 calculus anchor sourceStage stage count word) ∧
 type_of% (actual_successor root visit rec U7 calculus anchor sourceStage stage count word) ∧
 type_of% (Consumed.actual_receipt_with_packet root visit rec U7 calculus anchor sourceStage stage count 0) :=
 ⟨actual_prefix _ _ _ _ _ _ _ _ _ _ _,actual_word _ _ _ _ _ _ _ _ _ _,actual_residual _ _ _ _ _ _ _ _ _ _,
  actual_successor _ _ _ _ _ _ _ _ _ _,Consumed.actual_receipt_with_packet _ _ _ _ _ _ _ _ _ _⟩
end Future.Entry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
