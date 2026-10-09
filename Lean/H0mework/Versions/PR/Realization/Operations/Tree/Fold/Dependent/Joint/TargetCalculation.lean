import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.TargetProgramme
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (node : GeneratedNodeAt (recognition.generateStepAt visit) successor transition.history)
variable (sourceWord : SourceWord root visit recognition) (targetWord : TargetWord root visit recognition successor)
abbrev fromSourceWord := (StepSourceHistory (recognition.generateStepAt visit)).completionProjection sourceWord
abbrev fromTargetWord := (StepTargetHistory (recognition.generateStepAt visit) successor).completionProjection targetWord

theorem difference_value : (differenceExpression root visit recognition successor transition node).eval
    (targetEnvironment root visit recognition successor transition sourceWord targetWord) =
    targetDifference root visit recognition successor transition node (fromSourceWord root visit recognition sourceWord)
      (fromTargetWord root visit recognition successor targetWord) := by
  simp only [differenceExpression, Expr.eval, targetEnvironment, AddMonoidHom.neg_apply,
    LinearMap.toAddMonoidHom_coe, targetDifference, sub_eq_add_neg]

theorem target_programme_value : (fullTargetProgramme root visit recognition successor transition node).eval
    (targetEnvironment root visit recognition successor transition sourceWord targetWord) =
    (targetDifference root visit recognition successor transition node (fromSourceWord root visit recognition sourceWord) (fromTargetWord root visit recognition successor targetWord),
      targetObservationResidual root visit recognition successor transition node (fromSourceWord root visit recognition sourceWord) (fromTargetWord root visit recognition successor targetWord),
      targetRangeResidual root visit recognition successor transition node (fromSourceWord root visit recognition sourceWord) (fromTargetWord root visit recognition successor targetWord)) := by
  simp only [fullTargetProgramme, Expr.eval, observationExpression, imageExpression, difference_value,
    AddMonoidHom.prod_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply, Prod.mk_add_mk,
    add_zero, zero_add, LinearMap.toAddMonoidHom_coe]
  rfl

def targetRawCalculation : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=TargetValue root visit recognition successor transition (H:=H)) (Var:=TargetVar) (sort:=TargetSlot.full) :=
  ⟨targetEnvironment root visit recognition successor transition sourceWord targetWord,
    fullTargetProgramme root visit recognition successor transition node⟩
open RootInquiryCompletion
abbrev TargetMaterial := GeneratedNodeAt (recognition.generateStepAt visit) successor transition.history ×
  SourceWord root visit recognition × TargetWord root visit recognition successor ×
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=TargetValue root visit recognition successor transition (H:=H)) (Var:=TargetVar) (sort:=TargetSlot.full)
def targetMaterial : TargetMaterial root visit recognition successor transition :=
  ⟨node,sourceWord,targetWord,targetRawCalculation root visit recognition successor transition node sourceWord targetWord⟩
def targetComponent : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => TargetMaterial root visit recognition successor transition
  project := fun _ {_current} _ _ => targetMaterial root visit recognition successor transition node sourceWord targetWord
abbrev targetSourceRoot := root.withProjectionCoface (targetComponent root visit recognition successor transition node sourceWord targetWord)
abbrev targetSourceVisit : SourceNativeTemporalVisitAt (targetSourceRoot root visit recognition successor transition node sourceWord targetWord).toAuthoritativeRoot.toLedgerRoot := visit

def targetCalculationReader (occurrence : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) :=
  ((targetComponent root visit recognition successor transition node sourceWord targetWord).project PUnit.unit occurrence PUnit.unit).2.2.2
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
abbrev targetCalculationRoot := SourceTemporalMaterial.Calculation.sourceRoot
  (targetSourceRoot root visit recognition successor transition node sourceWord targetWord) visit
abbrev targetCalculationRuntime := SourceTemporalMaterial.Calculation.runtime
  (targetSourceRoot root visit recognition successor transition node sourceWord targetWord)
  (targetSourceVisit root visit recognition successor transition node sourceWord targetWord) U7 calculus
  (targetCalculationReader root visit recognition successor transition node sourceWord targetWord)

end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
