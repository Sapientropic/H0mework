import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.Source
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.Source
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.History.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Action.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects
open SourceOperationScalarRelations SourceOperationScalarInventoryLift
namespace Q
export SourceOperationInquiry.Context (RawAt RawSource raw readEnv increment)
end Q
namespace Hist
export SourceOperationInquiry.Context.History (Words stageInventory sourceMap readPrefix source_stage fibre_generated)
end Hist
namespace D
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (process actual_node)
end D
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Observer.Action.Frame root visit recognition)

private def restriction := Lower.restrictionOfFace root visit recognition
  (Observer.Live.E.Shared.root frame (Observer.Live.programme root visit recognition U7 calculus anchor))
  (Observer.Live.E.Shared.visit frame (Observer.Live.programme root visit recognition U7 calculus anchor))
  (Observer.Live.activeFace root visit recognition U7 calculus anchor frame
    (Observer.Live.sourceSeed root visit recognition U7 calculus anchor))
  (rawAt root visit recognition U7 calculus anchor (Observer.Live.E.epoch frame)
    (Observer.Live.E.Shared.actualOccurrence frame))
  (heq_of_eq (Observer.Live.active_raw root visit recognition U7 calculus anchor frame
    (Observer.Live.sourceSeed root visit recognition U7 calculus anchor)))

private theorem restriction_read : Lower.readRestriction root visit recognition _
    (restriction root visit recognition U7 calculus anchor frame) =
      rawAt root visit recognition U7 calculus anchor (Observer.Live.E.epoch frame)
        (Observer.Live.E.Shared.actualOccurrence frame) :=
  Lower.restriction_read root visit recognition _ _ _ _ _

def rawSource (state : (Observer.Live.runtime root visit recognition U7 calculus anchor).State) :
    Q.RawAt (PhysicalValue:=Observer.Value root visit recognition)
      (PhysicalVar:=Observer.Variable root visit recognition) (sort:=Observer.resultSlot root recognition)
      (Observer.Live.runtime root visit recognition U7 calculus anchor) state := by
  rcases state with ⟨⟨count⟩, activation⟩
  exact restriction root visit recognition U7 calculus anchor
    (Observer.Live.frameAt root visit recognition U7 calculus anchor count.down)
private def index (engine : Engine (D.process (Observer.Live.initial root visit recognition U7 calculus anchor)
    (Observer.Live.programme root visit recognition U7 calculus anchor))) : Nat := by
  rcases engine with ⟨count⟩
  exact count.down
private theorem raw_state (state : (Observer.Live.runtime root visit recognition U7 calculus anchor).State) :
    Q.raw (Observer.Live.runtime root visit recognition U7 calculus anchor)
      (rawSource root visit recognition U7 calculus anchor) state =
    rawAt root visit recognition U7 calculus anchor
      (Observer.Live.E.epoch (Observer.Live.frameAt root visit recognition U7 calculus anchor
        (index root visit recognition U7 calculus anchor state.engine)))
      (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor
        (index root visit recognition U7 calculus anchor state.engine))) := by
  rcases state with ⟨⟨count⟩, activation⟩
  exact restriction_read root visit recognition U7 calculus anchor _

theorem raw_actual (count : Nat) :
    Q.raw (Observer.Live.runtime root visit recognition U7 calculus anchor)
      (rawSource root visit recognition U7 calculus anchor)
      ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count) =
    rawAt root visit recognition U7 calculus anchor
      (Observer.Live.E.epoch (Observer.Live.frameAt root visit recognition U7 calculus anchor count))
      (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor count)) := by
  have indexEq : index root visit recognition U7 calculus anchor
      ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count).engine = count := by
    have same := D.actual_node (Observer.Live.initial root visit recognition U7 calculus anchor)
      (Observer.Live.programme root visit recognition U7 calculus anchor) count
    generalize engineEq : ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count).engine = engine at same ⊢
    rcases engine with ⟨hidden⟩
    have hiddenEq : hidden = ULift.up count :=
      (D.process (Observer.Live.initial root visit recognition U7 calculus anchor)
        (Observer.Live.programme root visit recognition U7 calculus anchor)).erase_injective rfl rfl
        (congrArg RootInquiryProcessNode.erase same)
    subst hidden
    rfl
  exact (raw_state root visit recognition U7 calculus anchor _).trans
    (congrArg (fun count => rawAt root visit recognition U7 calculus anchor
      (Observer.Live.E.epoch (Observer.Live.frameAt root visit recognition U7 calculus anchor count))
      (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor count))) indexEq)

def activeEnvironment (count : Nat) := Observer.Action.environmentAt root visit recognition
  (Observer.Live.E.epoch (Observer.Live.frameAt root visit recognition U7 calculus anchor count))
  (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor count))
theorem environment_actual (count : Nat) :
    Q.readEnv (Observer.Live.runtime root visit recognition U7 calculus anchor)
      (rawSource root visit recognition U7 calculus anchor)
      ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count) =
        activeEnvironment root visit recognition U7 calculus anchor count :=
  congrArg (fun raw => raw.environment) (raw_actual root visit recognition U7 calculus anchor count)

def sourceWord : Hist.Words (PhysicalValue:=Observer.Value root visit recognition)
    (PhysicalVar:=Observer.Variable root visit recognition) (sort:=Observer.resultSlot root recognition) :=
  Finsupp.single (Observer.Action.observerSyntax root visit recognition U7 calculus anchor) 1

theorem source_word_future (offset bound : Nat) (position : Fin (bound+1)) :
    Hist.readPrefix (Observer.Live.runtime root visit recognition U7 calculus anchor)
      (rawSource root visit recognition U7 calculus anchor) offset bound
      ((Hist.sourceMap (Observer.Live.runtime root visit recognition U7 calculus anchor)
        (rawSource root visit recognition U7 calculus anchor) offset).hom
        (sourceWord root visit recognition U7 calculus anchor)) position =
    Hist.stageInventory (Observer.Live.runtime root visit recognition U7 calculus anchor)
      (rawSource root visit recognition U7 calculus anchor) (offset+position.val)
      (sourceWord root visit recognition U7 calculus anchor) :=
  Hist.source_stage _ _ _ _ _ _


theorem increment_actual (count : Nat) :
    Q.increment (Observer.Live.runtime root visit recognition U7 calculus anchor)
      (rawSource root visit recognition U7 calculus anchor)
      ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count) =
    activeEnvironment root visit recognition U7 calculus anchor (count+1) -
      activeEnvironment root visit recognition U7 calculus anchor count := by
  change Q.readEnv _ _ ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt (count+1)) -
    Q.readEnv _ _ ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count) = _
  rw [environment_actual,environment_actual]

-- This frame is used only to instantiate existing expression-evaluation lemmas.
private def evaluationFrame (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition)) :=
  {Observer.sourceFrame root visit recognition U7 calculus anchor with
    environment := fun _ slot name => env (.inl slot) name}
private abbrev evaluationOccurrence (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition)) :=
  Inventory.Action.E.Shared.actualOccurrence (evaluationFrame root visit recognition U7 calculus anchor env)
private theorem evaluation_environment (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition)) :
    Observer.environmentAt root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
      (evaluationOccurrence root visit recognition U7 calculus anchor env) = env := by
  funext slot name
  cases slot with
  | inl original => rfl
  | inr extra => exact PEmpty.elim name
private theorem evaluation_syntax (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition)) :
    Observer.expressionAt root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
      (evaluationOccurrence root visit recognition U7 calculus anchor env) =
    Observer.Action.observerSyntax root visit recognition U7 calculus anchor := rfl

def point (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition))
    (row : Observer.Row root recognition) := env (.inl (.inr (.inl row.1))) ⟨row.2⟩ row.2
def observationValue (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition))
    (index : Observer.Index root visit recognition) (kind : Fin 4) :=
  let row := Observer.rowAt root visit recognition index
  let value := point root visit recognition env row
  match kind.val with
  | 0 => Observer.measurement root recognition row value
  | 1 => Observer.measurement root recognition row (Observer.action root recognition row value)
  | 2 => Observer.evolution root recognition row (Observer.measurement root recognition row value)
  | _ => Observer.evolution root recognition row (Observer.measurement root recognition row value) -
      Observer.measurement root recognition row (Observer.action root recognition row value)
private theorem evaluation_observation (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition))
    (index : Observer.Index root visit recognition) (kind : Fin 4) :
    Observer.observationValueAt root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
      (evaluationOccurrence root visit recognition U7 calculus anchor env) index kind =
      observationValue root visit recognition env index kind := by
  fin_cases kind
  · rfl
  · exact congrArg (Observer.measurement root recognition (Observer.rowAt root visit recognition index))
      (Observer.next_point_at root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
        (evaluationOccurrence root visit recognition U7 calculus anchor env) (Observer.rowAt root visit recognition index))
  · rfl
  · exact congrArg (fun value => Observer.evolution root recognition (Observer.rowAt root visit recognition index)
        (Observer.measurement root recognition (Observer.rowAt root visit recognition index)
          (point root visit recognition env (Observer.rowAt root visit recognition index))) -
        Observer.measurement root recognition (Observer.rowAt root visit recognition index) value)
      (Observer.next_point_at root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
        (evaluationOccurrence root visit recognition U7 calculus anchor env) (Observer.rowAt root visit recognition index))

theorem syntax_observation (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition))
    (index : Observer.Index root visit recognition) (kind : Fin 4) :
    ((Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval env).2.1 index kind =
      observationValue root visit recognition env index kind := by
  have observed := Observer.paid_observation_at root visit recognition
    (evaluationFrame root visit recognition U7 calculus anchor env)
    (evaluationOccurrence root visit recognition U7 calculus anchor env) index kind
  have paidValue := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Observer.E.Shared.base (evaluationFrame root visit recognition U7 calculus anchor env)).root.toAuthoritativeRoot
    (fun {_current} supplied => Observer.rawAt root visit recognition
      (evaluationFrame root visit recognition U7 calculus anchor env) supplied)
    (evaluationOccurrence root visit recognition U7 calculus anchor env)
  change (Observer.paidAt root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
      (evaluationOccurrence root visit recognition U7 calculus anchor env)).2.2.1 =
    (Observer.expressionAt root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
      (evaluationOccurrence root visit recognition U7 calculus anchor env)).eval
    (Observer.environmentAt root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
      (evaluationOccurrence root visit recognition U7 calculus anchor env)) at paidValue
  have result := (congrArg (fun value : Observer.Output root visit recognition => value.2.1 index kind) paidValue).symm.trans observed
  rw [evaluation_syntax,evaluation_environment,evaluation_observation] at result
  exact result

theorem syntax_gram (env : Env (Observer.Value root visit recognition) (Observer.Variable root visit recognition))
    (first second : Observer.Sample root visit recognition) :
    (((Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval env).2.2 first second).down =
      inner ℂ (observationValue root visit recognition env first.1 first.2)
        (observationValue root visit recognition env second.1 second.2) := by
  have observed := Observer.paid_gram_at root visit recognition
    (evaluationFrame root visit recognition U7 calculus anchor env)
    (evaluationOccurrence root visit recognition U7 calculus anchor env) first second
  have paidValue := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Observer.E.Shared.base (evaluationFrame root visit recognition U7 calculus anchor env)).root.toAuthoritativeRoot
    (fun {_current} supplied => Observer.rawAt root visit recognition
      (evaluationFrame root visit recognition U7 calculus anchor env) supplied)
    (evaluationOccurrence root visit recognition U7 calculus anchor env)
  change (Observer.paidAt root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
      (evaluationOccurrence root visit recognition U7 calculus anchor env)).2.2.1 =
    (Observer.expressionAt root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
      (evaluationOccurrence root visit recognition U7 calculus anchor env)).eval
    (Observer.environmentAt root visit recognition (evaluationFrame root visit recognition U7 calculus anchor env)
      (evaluationOccurrence root visit recognition U7 calculus anchor env)) at paidValue
  have result := (congrArg (fun value : Observer.Output root visit recognition => (value.2.2 first second).down) paidValue).symm.trans observed
  rw [evaluation_syntax,evaluation_environment,evaluation_observation,evaluation_observation] at result
  exact result

def futurePair (offset bound : Nat) (position : Fin (bound+1)) :=
  Hist.readPrefix (Observer.Live.runtime root visit recognition U7 calculus anchor)
    (rawSource root visit recognition U7 calculus anchor) offset bound
    ((Hist.sourceMap (Observer.Live.runtime root visit recognition U7 calculus anchor)
      (rawSource root visit recognition U7 calculus anchor) offset).hom
      (sourceWord root visit recognition U7 calculus anchor)) position

theorem future_pair (offset bound : Nat) (position : Fin (bound+1)) :
    futurePair root visit recognition U7 calculus anchor offset bound position =
      ((Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval
        (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val)),
       (Observer.Action.observerSyntax root visit recognition U7 calculus anchor).effect
        (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val))
        (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val+1) -
          activeEnvironment root visit recognition U7 calculus anchor (offset+position.val))) := by
  rw [futurePair,source_word_future]
  unfold Hist.stageInventory
  rw [environment_actual,increment_actual]
  simp only [sourceWord,updateInventory,LinearMap.prod_apply,Function.prod,evaluation,effectEvaluator,
    Finsupp.linearCombination_single,one_smul]

theorem future_pair_next (offset bound : Nat) (position : Fin (bound+1)) :
    (futurePair root visit recognition U7 calculus anchor offset bound position).1 +
      (futurePair root visit recognition U7 calculus anchor offset bound position).2 =
      (Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval
        (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val+1)) := by
  rw [future_pair]
  rw [←Expr.eval_update,add_sub_cancel]

theorem future_observation_old (offset bound : Nat) (position : Fin (bound+1))
    (index : Observer.Index root visit recognition) (kind : Fin 4) :
    (futurePair root visit recognition U7 calculus anchor offset bound position).1.2.1 index kind =
      observationValue root visit recognition (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val)) index kind := by
  rw [future_pair]
  exact syntax_observation root visit recognition U7 calculus anchor _ index kind

theorem future_observation_effect (offset bound : Nat) (position : Fin (bound+1))
    (index : Observer.Index root visit recognition) (kind : Fin 4) :
    (futurePair root visit recognition U7 calculus anchor offset bound position).2.2.1 index kind =
      observationValue root visit recognition (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val+1)) index kind -
      observationValue root visit recognition (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val)) index kind := by
  have total := congrArg (fun value : Observer.Output root visit recognition => value.2.1 index kind)
    (future_pair_next root visit recognition U7 calculus anchor offset bound position)
  change (futurePair root visit recognition U7 calculus anchor offset bound position).1.2.1 index kind +
    (futurePair root visit recognition U7 calculus anchor offset bound position).2.2.1 index kind = _ at total
  rw [future_observation_old,syntax_observation] at total
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using total)

theorem future_gram_old (offset bound : Nat) (position : Fin (bound+1))
    (first second : Observer.Sample root visit recognition) :
    ((futurePair root visit recognition U7 calculus anchor offset bound position).1.2.2 first second).down =
      inner ℂ (observationValue root visit recognition (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val)) first.1 first.2)
        (observationValue root visit recognition (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val)) second.1 second.2) := by
  rw [future_pair]
  exact syntax_gram root visit recognition U7 calculus anchor _ first second

theorem future_gram_effect (offset bound : Nat) (position : Fin (bound+1))
    (first second : Observer.Sample root visit recognition) :
    ((futurePair root visit recognition U7 calculus anchor offset bound position).2.2.2 first second).down =
      inner ℂ (observationValue root visit recognition (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val+1)) first.1 first.2)
        (observationValue root visit recognition (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val+1)) second.1 second.2) -
      inner ℂ (observationValue root visit recognition (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val)) first.1 first.2)
        (observationValue root visit recognition (activeEnvironment root visit recognition U7 calculus anchor (offset+position.val)) second.1 second.2) := by
  have total := congrArg (fun value : Observer.Output root visit recognition => (value.2.2 first second).down)
    (future_pair_next root visit recognition U7 calculus anchor offset bound position)
  change ((futurePair root visit recognition U7 calculus anchor offset bound position).1.2.2 first second).down +
    ((futurePair root visit recognition U7 calculus anchor offset bound position).2.2.2 first second).down = _ at total
  rw [future_gram_old,syntax_gram] at total
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using total)

theorem complete_fibre (offset : Nat)
    (left right : Hist.Words (PhysicalValue:=Observer.Value root visit recognition)
      (PhysicalVar:=Observer.Variable root visit recognition) (sort:=Observer.resultSlot root recognition)) :
    type_of% (Hist.fibre_generated (Observer.Live.runtime root visit recognition U7 calculus anchor)
      (rawSource root visit recognition U7 calculus anchor) offset left right) :=
  Hist.fibre_generated _ _ _ _ _

def residualRecover (count : Nat) := SourceOperationInquiry.Context.Faces.recover
  (Observer.Live.runtime root visit recognition U7 calculus anchor) (rawSource root visit recognition U7 calculus anchor)
  ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count)
theorem residual_recover_injective (count : Nat) : Function.Injective (residualRecover root visit recognition U7 calculus anchor count) :=
  SourceOperationInquiry.Context.Faces.recover_injective _ _ _
theorem source_reverse_pair (count : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.reverse_pair
  (Observer.Live.runtime root visit recognition U7 calculus anchor) (rawSource root visit recognition U7 calculus anchor)
  ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count)) :=
  SourceOperationInquiry.Context.Faces.Reverse.reverse_pair _ _ _
theorem source_whole (count : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_write
  (Observer.Live.runtime root visit recognition U7 calculus anchor) (rawSource root visit recognition U7 calculus anchor)
  ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count)) :=
  SourceOperationInquiry.Context.Faces.Reverse.source_write _ _ _
theorem source_next (count : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_next
  (Observer.Live.runtime root visit recognition U7 calculus anchor) (rawSource root visit recognition U7 calculus anchor)
  ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count)) :=
  SourceOperationInquiry.Context.Faces.Reverse.source_next _ _ _
theorem source_trace (count : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_trace
  (Observer.Live.runtime root visit recognition U7 calculus anchor) (rawSource root visit recognition U7 calculus anchor)
  ((Observer.Live.runtime root visit recognition U7 calculus anchor).stateAt count)) :=
  SourceOperationInquiry.Context.Faces.Reverse.source_trace _ _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
