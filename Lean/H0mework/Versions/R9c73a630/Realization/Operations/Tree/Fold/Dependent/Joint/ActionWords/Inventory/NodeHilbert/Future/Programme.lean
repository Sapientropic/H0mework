import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Action
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

variable (bound : Nat)
inductive Slot : Type u | model | atom | measured
abbrev Value : Slot → Type u
  | .model => Model root recognition visit successor transition alignment U7 calculus count
  | .atom => H
  | .measured => Space root recognition visit successor bound
abbrev Var : Slot → Type u := fun _ => PUnit.{u+1}
instance : (slot : Slot) → AddCommGroup (Value root recognition visit successor transition alignment U7 calculus count bound slot)
  | .model => inferInstance
  | .atom => inferInstance
  | .measured => inferInstance

def single (cell : Cells root recognition visit successor bound) : H →ₗ[ℤ] Space root recognition visit successor bound := by
  classical
  exact (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H)).symm.toLinearMap.comp
    (LinearMap.single ℤ (fun _ : Cells root recognition visit successor bound => H) cell)
def modelProgramme : List (Letter root recognition visit successor) →
    Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .model →
    Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .model
  | [],expression => expression
  | letter::rest,expression => modelProgramme rest
      (.linear (advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)
def cellProgramme (cell : Cells root recognition visit successor bound) :
    Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .measured :=
  .linear (s:=Slot.atom) (single root recognition visit successor bound cell).toAddMonoidHom
    (.linear (s:=Slot.model) (Covariance.feature root recognition visit successor transition alignment U7 calculus count
      (actor root recognition visit successor cell.2)).toAddMonoidHom
      (modelProgramme root recognition visit successor transition alignment U7 calculus count bound
        (word root recognition visit successor cell.1) (.var PUnit.unit)))
def sumProgramme : List (Cells root recognition visit successor bound) →
    Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .measured
  | [] => .const 0
  | cell::rest => .add (cellProgramme root recognition visit successor transition alignment U7 calculus count bound cell) (sumProgramme rest)
def programme : Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .measured :=
  sumProgramme root recognition visit successor transition alignment U7 calculus count bound (Finset.univ.toList)

def environmentAt (value : Model root recognition visit successor transition alignment U7 calculus count) :
    Env (Value root recognition visit successor transition alignment U7 calculus count bound) Var
  | .model,_ => value
  | .atom,_ => 0
  | .measured,_ => 0

theorem model_eval (letters : List (Letter root recognition visit successor))
    (sourceEnv : Env (Value root recognition visit successor transition alignment U7 calculus count bound) Var)
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .model) :
    (modelProgramme root recognition visit successor transition alignment U7 calculus count bound letters expression).eval sourceEnv=
      SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) letters (expression.eval sourceEnv) := by
  induction letters generalizing expression with
  | nil => rfl
  | cons letter rest previous => exact previous (.linear (advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)
theorem cell_eval (cell : Cells root recognition visit successor bound)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (cellProgramme root recognition visit successor transition alignment U7 calculus count bound cell).eval
      (environmentAt root recognition visit successor transition alignment U7 calculus count bound value) =
      single root recognition visit successor bound cell
        (observation root recognition visit successor transition alignment U7 calculus count bound value cell) := by
  change single root recognition visit successor bound cell
    (Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)
      ((modelProgramme root recognition visit successor transition alignment U7 calculus count bound
        (word root recognition visit successor cell.1) (.var PUnit.unit)).eval
          (environmentAt root recognition visit successor transition alignment U7 calculus count bound value))) = _
  rw [model_eval]
  rfl
theorem sum_eval (cells : List (Cells root recognition visit successor bound))
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (sumProgramme root recognition visit successor transition alignment U7 calculus count bound cells).eval
      (environmentAt root recognition visit successor transition alignment U7 calculus count bound value) =
      (cells.map (fun cell => single root recognition visit successor bound cell
        (observation root recognition visit successor transition alignment U7 calculus count bound value cell))).sum := by
  induction cells with
  | nil => rfl
  | cons cell rest previous =>
    change (cellProgramme root recognition visit successor transition alignment U7 calculus count bound cell).eval _ +
      (sumProgramme root recognition visit successor transition alignment U7 calculus count bound rest).eval _ = _
    rw [cell_eval,previous]
    rfl
theorem programme_value (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (programme root recognition visit successor transition alignment U7 calculus count bound).eval
      (environmentAt root recognition visit successor transition alignment U7 calculus count bound value) =
      observation root recognition visit successor transition alignment U7 calculus count bound value := by
  classical
  rw [programme,sum_eval,Finset.sum_map_toList]
  apply (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H)).injective
  change (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H))
    (∑ cell, single root recognition visit successor bound cell
      (observation root recognition visit successor transition alignment U7 calculus count bound value cell)) = _
  rw [map_sum]
  exact LinearMap.sum_single_apply _ _

theorem model_budget (letters : List (Letter root recognition visit successor))
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .model) :
    remaining (modelProgramme root recognition visit successor transition alignment U7 calculus count bound letters expression)=remaining expression+letters.length := by
  induction letters generalizing expression with
  | nil => simp only [modelProgramme,List.length_nil,Nat.add_zero]
  | cons letter rest previous => rw [modelProgramme,previous]; change remaining expression+1+rest.length=remaining expression+(rest.length+1); omega
theorem cell_budget (cell : Cells root recognition visit successor bound) :
    remaining (cellProgramme root recognition visit successor transition alignment U7 calculus count bound cell)=
      (word root recognition visit successor cell.1).length+3 := by
  change remaining (modelProgramme root recognition visit successor transition alignment U7 calculus count bound
    (word root recognition visit successor cell.1) (.var PUnit.unit))+1+1=_
  rw [model_budget]
  change 1+(word root recognition visit successor cell.1).length+1+1=_
  omega
theorem sum_budget (cells : List (Cells root recognition visit successor bound)) :
    remaining (sumProgramme root recognition visit successor transition alignment U7 calculus count bound cells)=
      (cells.map (fun cell => (word root recognition visit successor cell.1).length+4)).sum := by
  induction cells with
  | nil => rfl
  | cons cell rest previous =>
    change remaining (cellProgramme root recognition visit successor transition alignment U7 calculus count bound cell)+
      remaining (sumProgramme root recognition visit successor transition alignment U7 calculus count bound rest)+1=_
    rw [cell_budget,previous]
    simp only [List.map_cons,List.sum_cons]
    omega
abbrev budget := (Finset.univ.toList.map
  (fun cell : Cells root recognition visit successor bound => (word root recognition visit successor cell.1).length+4)).sum
theorem programme_budget : remaining (programme root recognition visit successor transition alignment U7 calculus count bound)=
    budget root recognition visit successor bound := sum_budget root recognition visit successor transition alignment U7 calculus count bound _

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
