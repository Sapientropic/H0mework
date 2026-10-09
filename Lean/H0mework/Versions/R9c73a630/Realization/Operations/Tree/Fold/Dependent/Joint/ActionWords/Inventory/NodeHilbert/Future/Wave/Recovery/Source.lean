import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Recovery.Range
import Lean.LibrarySuggestions.Basic
-- Preserve explicit APIs while excluding complete runtime mouths from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceFullRecovery"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot


namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
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

abbrev Original := PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count
abbrev JointCarrier := Model root recognition visit successor transition alignment U7 calculus count ×
  (PaidSourceFullOrbit.coherentWhole root recognition visit successor transition alignment U7 calculus count ×
    CoarseModel root recognition visit successor transition alignment U7 calculus count)
local instance : Module ℤ (JointCarrier root recognition visit successor transition alignment U7 calculus count) := AddCommGroup.toIntModule _
def together : Original root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ]
    JointCarrier root recognition visit successor transition alignment U7 calculus count :=
  ((PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).integralFace.toAddMonoidHom.prod
    ((PaidSourceFullOrbit.coherentSourceMap root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom.prod
      (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).measurementFace.toAddMonoidHom)).toIntLinearMap
theorem kernel_zero (value : Original root recognition visit successor transition alignment U7 calculus count)
    (vanish : together root recognition visit successor transition alignment U7 calculus count value=0) : value=0 := by
  have integral := congrArg Prod.fst vanish
  have coherent := (PaidSourceFullOrbit.coherent_kernel root recognition visit successor transition alignment U7 calculus count value).mp
    (congrArg (fun reading => reading.2.1) vanish)
  have measured := congrArg (fun reading => reading.2.2) vanish
  apply Subtype.ext
  apply Prod.ext
  · exact integral
  · apply Prod.ext
    · exact coherent
    · exact measured
theorem injective : Function.Injective (together root recognition visit successor transition alignment U7 calculus count) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro value vanish
  exact kernel_zero root recognition visit successor transition alignment U7 calculus count value vanish
abbrev Range := (together root recognition visit successor transition alignment U7 calculus count).range
def equivalence := LinearEquiv.ofInjective (together root recognition visit successor transition alignment U7 calculus count)
  (injective root recognition visit successor transition alignment U7 calculus count)
abbrev emit := (equivalence root recognition visit successor transition alignment U7 calculus count).toLinearMap
abbrev recover := (equivalence root recognition visit successor transition alignment U7 calculus count).symm.toLinearMap
theorem recover_emit (value : Original root recognition visit successor transition alignment U7 calculus count) :
    recover root recognition visit successor transition alignment U7 calculus count
      (emit root recognition visit successor transition alignment U7 calculus count value)=value :=
  (equivalence root recognition visit successor transition alignment U7 calculus count).symm_apply_apply value
theorem emit_recover (value : Range root recognition visit successor transition alignment U7 calculus count) :
    emit root recognition visit successor transition alignment U7 calculus count
      (recover root recognition visit successor transition alignment U7 calculus count value)=value :=
  (equivalence root recognition visit successor transition alignment U7 calculus count).apply_symm_apply value
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
