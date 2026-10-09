import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Lineage.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import Lean.LibrarySuggestions.Basic
-- Exclude only complete next-inventory runtime signatures from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceMacroGram"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroGram
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


variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
variable (bound : Nat) (queryWord : List (Letter root recognition visit successor)) (letter : Letter root recognition visit successor)
namespace L
export PaidSourceMacroLineage (initial nativeRuntime source observed effect embed lowerWord actualWord)
end L
variable (cut : Nat)
def coordinate (value : SourceOperationEffects.Env (PaidSourceIncidence.Value root recognition visit successor transition alignment U7 calculus count) PaidSourceIncidence.Var.{u}) :=
 (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).coherentFace
   (value PaidSourceIncidence.Slot.orbit PUnit.unit) cut
def coordinateMap : SourceOperationEffects.Env (PaidSourceIncidence.Value root recognition visit successor transition alignment U7 calculus count)
    PaidSourceIncidence.Var.{u} →ₗ[ℤ] Space root recognition visit successor cut :=
 { toFun := coordinate root recognition visit successor transition alignment U7 calculus count cut
   map_add' := by intro left right; exact congrFun (map_add ((PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).coherentFace) _ _) cut
   map_smul' := by intro coefficient value; exact congrFun (map_smul ((PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).coherentFace) coefficient _) cut }
def readH := (coordinateMap root recognition visit successor transition alignment U7 calculus count cut).comp
  (L.observed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
def effectH := (coordinateMap root recognition visit successor transition alignment U7 calculus count cut).comp
  (L.effect root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
theorem h_effect (word : PaidSourceMacroLineage.LineageWord.{u}) :
 readH root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut (L.lowerWord (PaidSourceMacroLineage.normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))-
   readH root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut (L.lowerWord word)=effectH root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut (L.lowerWord word) :=
 (map_sub (coordinateMap root recognition visit successor transition alignment U7 calculus count cut) _ _).symm.trans
   (congrArg (coordinateMap root recognition visit successor transition alignment U7 calculus count cut)
     (PaidSourceMacroLineage.physical_effect root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))
theorem h_next (word : PaidSourceMacroLineage.LineageWord.{u}) :
 readH root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut (L.lowerWord (PaidSourceMacroLineage.normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word))=
   readH root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut (L.lowerWord word)+effectH root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut (L.lowerWord word) :=
 (sub_eq_iff_eq_add.mp (h_effect root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut word)).trans (add_comm _ _)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
