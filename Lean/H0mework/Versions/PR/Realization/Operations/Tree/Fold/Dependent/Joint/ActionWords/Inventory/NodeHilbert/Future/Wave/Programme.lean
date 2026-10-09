import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
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

variable (bound : Nat) (queryWord : List (Letter root recognition visit successor))
abbrev Value := Future.Value root recognition visit successor transition alignment U7 calculus count bound
abbrev Var := Future.Var
namespace Slot
export Future.Slot (model atom measured)
end Slot
def atomProgramme : List (Letter root recognition visit successor) →
    (index : Index root recognition visit successor) → Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .atom → Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .atom
 | [],_,expression => expression
 | letter::rest,index,expression => atomProgramme rest index
     (.linear ((NodeHilbert.nodeEvolution root recognition visit successor letter index).toLinearMap.restrictScalars ℤ).toAddMonoidHom expression)
def cellProgramme (cell : Cells root recognition visit successor bound) : Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .measured :=
  .linear (s:=Slot.atom) (Future.single root recognition visit successor bound cell).toAddMonoidHom
    (.add (atomProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cell.2
      (.linear (s:=Slot.model) (Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)).toAddMonoidHom
        (Future.modelProgramme root recognition visit successor transition alignment U7 calculus count bound (word root recognition visit successor cell.1) (.var PUnit.unit))))
      (.linear (s:=Slot.model) (-(Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)).toAddMonoidHom)
        (Future.modelProgramme root recognition visit successor transition alignment U7 calculus count bound (queryWord++word root recognition visit successor cell.1) (.var PUnit.unit))))
def sumProgramme : List (Cells root recognition visit successor bound) → Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .measured
 | [] => .const 0
 | cell::rest => .add (cellProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cell) (sumProgramme rest)
def programme := sumProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord (Finset.univ.toList)
abbrev environmentAt := Future.environmentAt root recognition visit successor transition alignment U7 calculus count bound

def atomEvolution : List (Letter root recognition visit successor) →
    (index : Index root recognition visit successor) → H →ₗᵢ[ℂ] H
 | [],_ => LinearIsometry.id
 | letter::rest,index => (atomEvolution rest index).comp (NodeHilbert.nodeEvolution root recognition visit successor letter index)
theorem atom_eval (index : Index root recognition visit successor)
    (sourceEnv : Env (Value root recognition visit successor transition alignment U7 calculus count bound) Var)
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .atom) :
    (atomProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord index expression).eval sourceEnv=
    atomEvolution root recognition visit successor queryWord index (expression.eval sourceEnv) := by
  induction queryWord generalizing expression with
  | nil => rfl
  | cons letter rest previous => exact previous (.linear
      ((NodeHilbert.nodeEvolution root recognition visit successor letter index).toLinearMap.restrictScalars ℤ).toAddMonoidHom expression)
theorem atom_node (index : Index root recognition visit successor) (value : NodeHilbert.Space root recognition visit successor) :
    atomEvolution root recognition visit successor queryWord index (value index)=
    NodeHilbert.Words.wordEvolution root recognition visit successor queryWord value index := by
  induction queryWord generalizing value with
  | nil => rfl
  | cons letter rest previous => exact previous (NodeHilbert.evolution root recognition visit successor letter value)
theorem cell_eval (cell : Cells root recognition visit successor bound) (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (cellProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cell).eval (environmentAt root recognition visit successor transition alignment U7 calculus count bound value)=
      Future.single root recognition visit successor bound cell (effect root recognition visit successor transition alignment U7 calculus count bound queryWord value cell) := by
  change Future.single root recognition visit successor bound cell
    ((atomProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cell.2 _).eval (environmentAt root recognition visit successor transition alignment U7 calculus count bound value)+
      (-(Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)).toAddMonoidHom)
        ((Future.modelProgramme root recognition visit successor transition alignment U7 calculus count bound (queryWord++word root recognition visit successor cell.1) (.var PUnit.unit)).eval
          (environmentAt root recognition visit successor transition alignment U7 calculus count bound value)))=_
  rw [atom_eval]
  simp only [Expr.eval]
  rw [Future.model_eval,Future.model_eval]
  simp only [Expr.eval,environmentAt,Future.environmentAt,AddMonoidHom.neg_apply,LinearMap.toAddMonoidHom_coe,← sub_eq_add_neg]
  change Future.single root recognition visit successor bound cell
    (atomEvolution root recognition visit successor queryWord cell.2
      (Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)
        (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) (word root recognition visit successor cell.1) value))-
      Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)
        (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) (queryWord++word root recognition visit successor cell.1) value))=_
  apply congrArg (Future.single root recognition visit successor bound cell)
  have node := atom_node root recognition visit successor queryWord cell.2
    (NodeHilbert.measurement root recognition visit successor transition alignment U7 calculus count
      (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) (word root recognition visit successor cell.1) value))
  rw [NodeHilbert.measurement_node] at node
  exact (congrArg₂ (· - ·) node rfl).trans (effect_cell root recognition visit successor transition alignment U7 calculus count bound queryWord cell value).symm

theorem sum_eval (cells : List (Cells root recognition visit successor bound)) (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (sumProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cells).eval (environmentAt root recognition visit successor transition alignment U7 calculus count bound value)=
      (cells.map (fun cell => Future.single root recognition visit successor bound cell
        (effect root recognition visit successor transition alignment U7 calculus count bound queryWord value cell))).sum := by
  induction cells with
  | nil => rfl
  | cons cell rest previous =>
    change (cellProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cell).eval _+
      (sumProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord rest).eval _=_
    rw [cell_eval,previous]
    rfl

theorem programme_value (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (programme root recognition visit successor transition alignment U7 calculus count bound queryWord).eval (environmentAt root recognition visit successor transition alignment U7 calculus count bound value)=effect root recognition visit successor transition alignment U7 calculus count bound queryWord value := by
  classical
  rw [programme,sum_eval,Finset.sum_map_toList]
  apply (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H)).injective
  change (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H))
    (∑ cell,Future.single root recognition visit successor bound cell (effect root recognition visit successor transition alignment U7 calculus count bound queryWord value cell))=_
  rw [map_sum]
  exact LinearMap.sum_single_apply _ _

theorem atom_budget (index : Index root recognition visit successor)
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count bound) Var .atom) :
    remaining (atomProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord index expression)=remaining expression+queryWord.length := by
  induction queryWord generalizing expression with
  | nil => simp only [atomProgramme,List.length_nil,Nat.add_zero]
  | cons letter rest previous => rw [atomProgramme,previous]; change remaining expression+1+rest.length=remaining expression+(rest.length+1); omega

theorem cell_budget (cell : Cells root recognition visit successor bound) :
    remaining (cellProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cell)=
      2*(word root recognition visit successor cell.1).length+2*queryWord.length+6 := by
  change remaining (atomProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cell.2 _)+
    (remaining (Future.modelProgramme root recognition visit successor transition alignment U7 calculus count bound (queryWord++word root recognition visit successor cell.1) (.var PUnit.unit))+1)+1+1=_
  rw [atom_budget,Future.model_budget]
  change (remaining (Future.modelProgramme root recognition visit successor transition alignment U7 calculus count bound (word root recognition visit successor cell.1) (.var PUnit.unit))+1+queryWord.length)+
    ((1+(queryWord++word root recognition visit successor cell.1).length)+1)+1+1=_
  rw [Future.model_budget,List.length_append]
  change (1+(word root recognition visit successor cell.1).length+1+queryWord.length)+
    ((1+(queryWord.length+(word root recognition visit successor cell.1).length))+1)+1+1=_
  omega

theorem sum_budget (cells : List (Cells root recognition visit successor bound)) :
    remaining (sumProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cells)=
      (cells.map (fun cell => 2*(word root recognition visit successor cell.1).length+2*queryWord.length+7)).sum := by
  induction cells with
  | nil => rfl
  | cons cell rest previous =>
    change remaining (cellProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord cell)+remaining (sumProgramme root recognition visit successor transition alignment U7 calculus count bound queryWord rest)+1=_
    rw [cell_budget,previous]
    simp only [List.map_cons,List.sum_cons]
    omega
abbrev budget := (Finset.univ.toList.map (fun cell : Cells root recognition visit successor bound =>
  2*(word root recognition visit successor cell.1).length+2*queryWord.length+7)).sum
theorem programme_budget : remaining (programme root recognition visit successor transition alignment U7 calculus count bound queryWord)=budget root recognition visit successor bound queryWord :=
  sum_budget root recognition visit successor transition alignment U7 calculus count bound queryWord _
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
