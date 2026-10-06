import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Full.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullOrbit
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

namespace CofinalKernel
universe v
variable {G : Type v} [AddCommGroup G] [Module ℤ G]
variable {A : Nat → Type v} [∀ n,AddCommGroup (A n)] [∀ n,Module ℤ (A n)]
theorem zero_iff (data : SourceGeneratedScalarCofinalKernelCompletion.Data (R:=ℤ) (Generator:=G) (Carrier:=A))
    (compatible : data.Compatible) (value : G) : data.completionMap compatible value=0 ↔ ∀ n,data.evaluator n value=0 := by
  constructor
  · intro vanish n; exact data.evaluator_eq_zero_of_completionMap_eq_zero compatible value vanish n
  · intro vanish
    apply CategoryTheory.Limits.Concrete.limit_ext (data.quotientTower compatible)
    intro stage
    have square := CategoryTheory.ConcreteCategory.congr_hom (data.completionMap_restriction compatible stage.unop) value
    have quotientZero : data.quotientMap stage.unop value=0 := (Submodule.Quotient.mk_eq_zero _).mpr (vanish stage.unop)
    exact square.trans (quotientZero.trans (map_zero _).symm)
end CofinalKernel
theorem coherent_kernel (value : FullCarrier root recognition visit successor transition alignment U7 calculus count) :
    coherentSourceMap root recognition visit successor transition alignment U7 calculus count value=0 ↔
      (input root recognition visit successor transition alignment U7 calculus count).coherentFace value=0 := by
  have whole := CofinalKernel.zero_iff
    (coherentData root recognition visit successor transition alignment U7 calculus count)
    (coherent_compatible root recognition visit successor transition alignment U7 calculus count) value
  constructor
  · intro vanish
    funext bound
    exact whole.mp vanish bound
  · intro vanish
    apply whole.mpr
    intro bound
    exact congrArg (fun family => family bound) vanish
theorem complete_incidence (letters : List (Letter root recognition visit successor))
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    coherentSourceMap root recognition visit successor transition alignment U7 calculus count
      ((input root recognition visit successor transition alignment U7 calculus count).incidence letters value)=0 ↔
      ∀ bound,Wave.effect root recognition visit successor transition alignment U7 calculus count bound letters value=0 := by
  rw [coherent_kernel]
  constructor
  · intro vanish bound
    exact (exact_future root recognition visit successor transition alignment U7 calculus count bound letters value).symm.trans
      (congrArg (fun family => family bound) vanish)
  · intro vanish; funext bound
    exact (exact_future root recognition visit successor transition alignment U7 calculus count bound letters value).trans (vanish bound)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullOrbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
