import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Words.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceWordOrbit
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

namespace NativeWordProgramme
universe v
variable {L I O : Type v} [AddCommGroup I] [AddCommGroup O]
abbrev Value := PaidSourceOrbit.NativeOrbitProgramme.Value (I:=I) (O:=O)
abbrev Var := PaidSourceOrbit.NativeOrbitProgramme.Var
namespace Slot
export PaidSourceOrbit.NativeOrbitProgramme.Slot (model orbit)
end Slot
abbrev environment := PaidSourceOrbit.NativeOrbitProgramme.environment (I:=I) (O:=O)
local instance : (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot) → AddCommGroup (Value (I:=I) (O:=O) slot) :=
  inferInstanceAs ((slot : PaidSourceOrbit.NativeOrbitProgramme.Slot) → AddCommGroup (PaidSourceOrbit.NativeOrbitProgramme.Value (I:=I) (O:=O) slot))
variable (seed : I →ₗ[ℤ] O) (actions : L → O →ₗ[ℤ] O)
def iterate : List L → Expr (Value (I:=I) (O:=O)) Var .orbit → Expr (Value (I:=I) (O:=O)) Var .orbit
 | [],expression => expression
 | first::rest,expression => iterate rest (.linear (actions first).toAddMonoidHom expression)
def programme (letters : List L) : Expr (Value (I:=I) (O:=O)) Var .orbit :=
 iterate actions letters (.linear (s:=Slot.model) seed.toAddMonoidHom (.var PUnit.unit))
theorem iterate_value (letters : List L) (value : I) (expression : Expr (Value (I:=I) (O:=O)) Var .orbit) :
    (iterate actions letters expression).eval (environment seed.toAddMonoidHom value)=
      SourceGeneratedActionWords.run actions letters (expression.eval (environment seed.toAddMonoidHom value)) := by
  induction letters generalizing expression with
  | nil => rfl
  | cons first rest previous => exact previous (.linear (actions first).toAddMonoidHom expression)
theorem programme_value (letters : List L) (value : I) :
    (programme seed actions letters).eval (environment seed.toAddMonoidHom value)=
      SourceGeneratedActionWords.run actions letters (seed value) :=
  iterate_value seed actions letters value (.linear (s:=Slot.model) seed.toAddMonoidHom (.var PUnit.unit))
theorem iterate_budget (letters : List L) (expression : Expr (Value (I:=I) (O:=O)) Var .orbit) :
    remaining (iterate actions letters expression)=remaining expression+letters.length := by
  induction letters generalizing expression with
  | nil => simp only [iterate,List.length_nil,Nat.add_zero]
  | cons first rest previous =>
    rw [iterate,previous]
    change remaining expression+1+rest.length=remaining expression+(rest.length+1)
    omega
theorem programme_budget (letters : List L) : remaining (programme seed actions letters)=letters.length+2 := by
  rw [programme,iterate_budget]
  change 2+letters.length=letters.length+2
  omega
end NativeWordProgramme
variable (bound : Nat)
abbrev Value := PaidSourceOrbit.NativeOrbitProgramme.Value
  (I:=Model root recognition visit successor transition alignment U7 calculus count)
  (O:=WordCarrier root recognition visit successor transition alignment U7 calculus count bound)
abbrev Var := PaidSourceOrbit.NativeOrbitProgramme.Var
namespace Slot
export PaidSourceOrbit.NativeOrbitProgramme.Slot (model orbit)
end Slot
abbrev environmentAt := PaidSourceOrbit.NativeOrbitProgramme.environment
  (seed root recognition visit successor transition alignment U7 calculus count bound).toAddMonoidHom
abbrev programme (letters : List (Letter root recognition visit successor)) :=
  NativeWordProgramme.programme (seed root recognition visit successor transition alignment U7 calculus count bound)
    (advance root recognition visit successor transition alignment U7 calculus count bound) letters
theorem programme_value (letters : List (Letter root recognition visit successor))
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (programme root recognition visit successor transition alignment U7 calculus count bound letters).eval
      (environmentAt root recognition visit successor transition alignment U7 calculus count bound value)=
      SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count bound) letters
        (seed root recognition visit successor transition alignment U7 calculus count bound value) := NativeWordProgramme.programme_value _ _ letters value
theorem programme_budget (letters : List (Letter root recognition visit successor)) :
    remaining (programme root recognition visit successor transition alignment U7 calculus count bound letters)=letters.length+2 :=
  NativeWordProgramme.programme_budget _ _ letters
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceWordOrbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
