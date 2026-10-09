import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Orbit.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceOrbit
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

namespace NativeOrbitProgramme
universe v
variable {I O : Type v} [AddCommGroup I] [AddCommGroup O]
inductive Slot : Type v | model | orbit
abbrev Value : Slot → Type v | .model => I | .orbit => O
abbrev Var : Slot → Type v := fun _ => PUnit.{v+1}
instance : (slot : Slot) → AddCommGroup (Value (I:=I) (O:=O) slot)
 | .model => inferInstanceAs (AddCommGroup I)
 | .orbit => inferInstanceAs (AddCommGroup O)
variable (seed : I →+ O) (action : O →+ O)
def environment (value : I) : Env (Value (I:=I) (O:=O)) Var
 | .model,_ => value
 | .orbit,_ => seed value

def iterate : Nat → Expr (Value (I:=I) (O:=O)) Var .orbit → Expr (Value (I:=I) (O:=O)) Var .orbit
 | 0,expression => expression
 | n+1,expression => iterate n (.linear action expression)
def programme (count : Nat) : Expr (Value (I:=I) (O:=O)) Var .orbit :=
  iterate action count (.linear (s:=Slot.model) seed (.var PUnit.unit))
def run : Nat → O → O
 | 0,value => value
 | n+1,value => run n (action value)
theorem iterate_value (count : Nat) (value : I) (expression : Expr (Value (I:=I) (O:=O)) Var .orbit) :
    (iterate action count expression).eval (environment seed value)=
      run action count (expression.eval (environment seed value)) := by
  induction count generalizing expression with
  | zero => rfl
  | succ n previous => exact previous (.linear action expression)
theorem iterate_budget (count : Nat) (expression : Expr (Value (I:=I) (O:=O)) Var .orbit) :
    remaining (iterate action count expression)=remaining expression+count := by
  induction count generalizing expression with
  | zero => simp only [iterate,Nat.add_zero]
  | succ n previous => rw [iterate,previous]; change remaining expression+1+n=remaining expression+(n+1); omega

theorem programme_value (count : Nat) (value : I) :
    (programme seed action count).eval (environment seed value)=run action count (seed value) :=
  iterate_value seed action count value (.linear (s:=Slot.model) seed (.var PUnit.unit))
theorem programme_budget (count : Nat) : remaining (programme seed action count)=count+2 := by
  rw [programme,iterate_budget]
  change 2+count=count+2
  omega
end NativeOrbitProgramme
namespace NativeOrbitProgramme
universe w
variable {I O : Type w} [AddCommGroup I] [AddCommGroup O]
def orbitEnvironment (project : O →+ I) (value : O) : Env (Value (I:=I) (O:=O)) Var
 | .model,_ => project value
 | .orbit,_ => value
def nextProgramme (action : O →+ O) : Expr (Value (I:=I) (O:=O)) Var .orbit :=
 .linear (s:=Slot.orbit) action (.var PUnit.unit)
theorem next_value (project : O →+ I) (action : O →+ O) (value : O) :
    (nextProgramme action).eval (orbitEnvironment project value)=action value := rfl
theorem pair_value (project : O →+ I) (action : O →+ O) (before after : O) :
    (SourceOperationScalarInventoryLift.liftExpr (nextProgramme action)).eval
      (SourceOperationScalarInventoryLift.pairEnvironment (orbitEnvironment project before)
        (orbitEnvironment project after-orbitEnvironment project before))=
      (action before,action after-action before) := by
  rw [SourceOperationScalarInventoryLift.eval_liftExpr]
  apply Prod.ext
  · rfl
  · have square := Expr.eval_update (nextProgramme action) (orbitEnvironment project before)
      (orbitEnvironment project after-orbitEnvironment project before)
    rw [add_sub_cancel] at square
    exact eq_sub_of_add_eq (by rw [add_comm]; exact square.symm)
end NativeOrbitProgramme
variable (bound : Nat) (letter : Letter root recognition visit successor) (iterations : Nat)
abbrev operation := input root recognition visit successor transition alignment U7 calculus count bound [letter]
abbrev OrbitCarrier := (operation root recognition visit successor transition alignment U7 calculus count bound letter).Carrier
abbrev advance := (operation root recognition visit successor transition alignment U7 calculus count bound letter).omega
abbrev seed := (operation root recognition visit successor transition alignment U7 calculus count bound letter).seedLift
abbrev Value := NativeOrbitProgramme.Value (I:=Model root recognition visit successor transition alignment U7 calculus count) (O:=OrbitCarrier root recognition visit successor transition alignment U7 calculus count bound letter)
abbrev Var := NativeOrbitProgramme.Var
namespace Slot
export NativeOrbitProgramme.Slot (model orbit)
end Slot
abbrev environmentAt := NativeOrbitProgramme.environment (seed root recognition visit successor transition alignment U7 calculus count bound letter).toAddMonoidHom
abbrev programme := NativeOrbitProgramme.programme (seed root recognition visit successor transition alignment U7 calculus count bound letter).toAddMonoidHom
  (advance root recognition visit successor transition alignment U7 calculus count bound letter).toAddMonoidHom iterations

theorem programme_value (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (programme root recognition visit successor transition alignment U7 calculus count bound letter iterations).eval (environmentAt root recognition visit successor transition alignment U7 calculus count bound letter value)=
      NativeOrbitProgramme.run (advance root recognition visit successor transition alignment U7 calculus count bound letter).toAddMonoidHom iterations (seed root recognition visit successor transition alignment U7 calculus count bound letter value) :=
  NativeOrbitProgramme.programme_value _ _ iterations value

theorem programme_budget : remaining (programme root recognition visit successor transition alignment U7 calculus count bound letter iterations)=iterations+2 :=
  NativeOrbitProgramme.programme_budget _ _ iterations
namespace NativeOrbitProgramme
universe w
variable {I O Q : Type w} [AddCommGroup I] [AddCommGroup O] [AddCommGroup Q]
theorem run_square (project : O →+ Q) (action : O →+ O) (target : Q →+ Q)
    (square : ∀ value, project (action value)=target (project value)) (n : Nat) (value : O) :
    project (run action n value)=run target n (project value) := by
  induction n generalizing value with
  | zero => rfl
  | succ n previous => exact (previous (action value)).trans (congrArg (run target n) (square value))
end NativeOrbitProgramme
theorem integral_read (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (operation root recognition visit successor transition alignment U7 calculus count bound letter).integralFace
      (NativeOrbitProgramme.run (advance root recognition visit successor transition alignment U7 calculus count bound letter).toAddMonoidHom iterations (seed root recognition visit successor transition alignment U7 calculus count bound letter value))=
    NativeOrbitProgramme.run (Inventory.advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom iterations value :=
  NativeOrbitProgramme.run_square (operation root recognition visit successor transition alignment U7 calculus count bound letter).integralFace.toAddMonoidHom
    (advance root recognition visit successor transition alignment U7 calculus count bound letter).toAddMonoidHom (Inventory.advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom
    (fun point => LinearMap.congr_fun (operation root recognition visit successor transition alignment U7 calculus count bound letter).integralFace_omega point) iterations _
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceOrbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
