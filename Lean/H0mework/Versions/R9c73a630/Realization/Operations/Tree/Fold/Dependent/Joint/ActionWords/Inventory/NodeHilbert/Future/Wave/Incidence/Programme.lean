import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Recovery.Consumer
import Lean.LibrarySuggestions.Basic
-- Exclude only the complete incidence runtime namespace from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceIncidence"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidence
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


namespace PaidIncidenceProgramme
universe v
variable {L I O : Type v} [AddCommGroup I] [AddCommGroup O]
abbrev Value := PaidSourceOrbit.NativeOrbitProgramme.Value (I:=I) (O:=O)
abbrev Var := PaidSourceOrbit.NativeOrbitProgramme.Var
namespace Slot
export PaidSourceOrbit.NativeOrbitProgramme.Slot (model orbit)
end Slot
local instance : (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot) → AddCommGroup (Value (I:=I) (O:=O) slot) :=
  inferInstanceAs ((slot : PaidSourceOrbit.NativeOrbitProgramme.Slot) → AddCommGroup (PaidSourceOrbit.NativeOrbitProgramme.Value (I:=I) (O:=O) slot))
variable (seed : I →ₗ[ℤ] O) (source : L → I →ₗ[ℤ] I) (actions : L → O →ₗ[ℤ] O)
def modelWord : List L → Expr (Value (I:=I) (O:=O)) Var Slot.model → Expr (Value (I:=I) (O:=O)) Var Slot.model
 | [],expression => expression
 | first::rest,expression => modelWord rest (.linear (source first).toAddMonoidHom expression)
def programme (letters : List L) : Expr (Value (I:=I) (O:=O)) Var Slot.orbit :=
 .add (PaidSourceWordOrbit.NativeWordProgramme.programme seed actions letters)
   (.linear (s:=Slot.orbit) (-AddMonoidHom.id O) (.linear (s:=Slot.model) seed.toAddMonoidHom (modelWord source letters (.var PUnit.unit))))
theorem model_value (letters : List L) (value : I) (expression : Expr (Value (I:=I) (O:=O)) Var Slot.model) :
    (modelWord source letters expression).eval (PaidSourceOrbit.NativeOrbitProgramme.environment (I:=I) (O:=O) seed.toAddMonoidHom value)=
      SourceGeneratedActionWords.run source letters (expression.eval (PaidSourceOrbit.NativeOrbitProgramme.environment (I:=I) (O:=O) seed.toAddMonoidHom value)) := by
 induction letters generalizing expression with
 | nil => rfl
 | cons first rest previous => exact previous (.linear (source first).toAddMonoidHom expression)
theorem output (letters : List L) (value : I) :
    (programme seed source actions letters).eval (PaidSourceOrbit.NativeOrbitProgramme.environment (I:=I) (O:=O) seed.toAddMonoidHom value)=
      SourceGeneratedActionWords.run actions letters (seed value)-seed (SourceGeneratedActionWords.run source letters value) := by
 change (PaidSourceWordOrbit.NativeWordProgramme.programme seed actions letters).eval _ + -(seed ((modelWord source letters (.var PUnit.unit)).eval _))=_
 have left : (PaidSourceWordOrbit.NativeWordProgramme.programme seed actions letters).eval
      (PaidSourceOrbit.NativeOrbitProgramme.environment (I:=I) (O:=O) seed.toAddMonoidHom value)=
      SourceGeneratedActionWords.run actions letters (seed value) :=
   PaidSourceWordOrbit.NativeWordProgramme.programme_value seed actions letters value
 have right : (modelWord source letters (.var (s:=Slot.model) PUnit.unit)).eval
      (PaidSourceOrbit.NativeOrbitProgramme.environment (I:=I) (O:=O) seed.toAddMonoidHom value)=
      SourceGeneratedActionWords.run source letters value :=
   model_value seed source letters value (.var (s:=Slot.model) PUnit.unit)
 simpa only [sub_eq_add_neg] using congrArg₂ (fun (left : O) (right : I) => left + -(seed right)) left right
theorem model_budget (letters : List L) (expression : Expr (Value (I:=I) (O:=O)) Var Slot.model) :
    remaining (modelWord source letters expression)=remaining expression+letters.length := by
 induction letters generalizing expression with
 | nil => simp only [modelWord,List.length_nil,Nat.add_zero]
 | cons first rest previous => rw [modelWord,previous]; change remaining expression+1+rest.length=remaining expression+(rest.length+1); omega
theorem budget (letters : List L) : remaining (programme seed source actions letters)=2*letters.length+6 := by
 change remaining (PaidSourceWordOrbit.NativeWordProgramme.programme seed actions letters)+(remaining (modelWord source letters (.var PUnit.unit))+1+1)+1=_
 rw [PaidSourceWordOrbit.NativeWordProgramme.programme_budget,model_budget]
 change (letters.length+2)+(1+letters.length+1+1)+1=2*letters.length+6
 omega
end PaidIncidenceProgramme
abbrev Value := PaidSourceFullOrbit.Value root recognition visit successor transition alignment U7 calculus count
abbrev Var := PaidSourceFullOrbit.Var
namespace Slot
export PaidSourceOrbit.NativeOrbitProgramme.Slot (model orbit)
end Slot
abbrev programme (letters : List (Letter root recognition visit successor)) :=
 PaidIncidenceProgramme.programme
   (PaidSourceFullOrbit.seed root recognition visit successor transition alignment U7 calculus count)
   (Inventory.advance root recognition visit successor transition alignment U7 calculus count)
   (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count) letters
theorem programme_value (letters : List (Letter root recognition visit successor))
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (programme root recognition visit successor transition alignment U7 calculus count letters).eval
      (PaidSourceFullOrbit.environmentAt root recognition visit successor transition alignment U7 calculus count value)=
      (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).incidence letters value :=
 PaidIncidenceProgramme.output _ _ _ letters value
theorem programme_budget (letters : List (Letter root recognition visit successor)) :
    remaining (programme root recognition visit successor transition alignment U7 calculus count letters)=2*letters.length+6 := PaidIncidenceProgramme.budget _ _ _ letters
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
