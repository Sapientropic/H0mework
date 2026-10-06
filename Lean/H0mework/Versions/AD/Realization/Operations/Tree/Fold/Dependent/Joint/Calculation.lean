import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Programme
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
variable (value : C root visit recognition)
inductive PairedSlot : Type u | original (slot : Slot.{u}) | paired
abbrev PairedValue : PairedSlot.{u} → Type u
  | .original slot => Value root visit recognition successor (H:=H) slot
  | .paired => H × H
abbrev PairedVar : PairedSlot.{u} → Type u
  | .original slot => Var slot
  | .paired => PEmpty.{u+1}
instance : (slot : PairedSlot.{u}) → AddCommGroup (PairedValue root visit recognition successor (H:=H) slot)
  | .original _slot => inferInstance
  | .paired => inferInstance

def includeExpression {slot : Slot.{u}} : Expr (Value root visit recognition successor (H:=H)) Var slot →
    Expr (PairedValue root visit recognition successor (H:=H)) PairedVar (.original slot)
  | .var name => .var name
  | .const value => .const value
  | .add first second => .add (includeExpression first) (includeExpression second)
  | .linear operation argument => .linear operation (includeExpression argument)
  | .bilinear operation first second => .bilinear operation (includeExpression first) (includeExpression second)

def pairedEnvironment : Env (PairedValue root visit recognition successor (H:=H)) PairedVar :=
  fun slot => match slot with
    | .original old => environment root visit recognition successor value old
    | .paired => PEmpty.elim

def pairedProgramme : Expr (PairedValue root visit recognition successor (H:=H)) PairedVar .paired :=
  .add (.linear (s:=.original Slot.measured) ((AddMonoidHom.id H).prod (0 : H →+ H))
      (includeExpression root visit recognition successor (sourceCoupling root visit recognition successor transition node)))
    (.linear (s:=.original Slot.measured) ((0 : H →+ H).prod (AddMonoidHom.id H))
      (includeExpression root visit recognition successor (targetCoupling root visit recognition successor transition node)))

theorem include_eval {slot : Slot.{u}} (expression : Expr (Value root visit recognition successor (H:=H)) Var slot) :
    (includeExpression root visit recognition successor expression).eval (pairedEnvironment root visit recognition successor value) =
      expression.eval (environment root visit recognition successor value) := by
  induction expression with
  | var name => rfl
  | const point => rfl
  | add first second ih1 ih2 => exact congrArg₂ (· + ·) ih1 ih2
  | linear operation argument ih => exact congrArg operation ih
  | bilinear operation first second ih1 ih2 => exact congrArg₂ (fun first second => operation first second) ih1 ih2

theorem paired_value : (pairedProgramme root visit recognition successor transition node).eval
    (pairedEnvironment root visit recognition successor value) =
      (sourceResidual root visit recognition successor transition node value,
        targetResidual root visit recognition successor transition node (RootLawDependentJointTransition.carrierMap transition.history value)) := by
  simp only [pairedProgramme, Expr.eval, include_eval, AddMonoidHom.prod_apply, AddMonoidHom.id_apply,
    AddMonoidHom.zero_apply, Prod.mk_add_mk, add_zero, zero_add]
  apply Prod.ext
  · simp only [sourceCoupling, sourceMeasured, Expr.eval, environment, AddMonoidHom.neg_apply,
      LinearMap.toAddMonoidHom_coe, LinearIsometry.coe_toLinearMap, sub_eq_add_neg]
  · simp only [targetCoupling, targetMeasured, actionAfter, nextExpression, Expr.eval, environment,
      AddMonoidHom.neg_apply, LinearMap.toAddMonoidHom_coe, LinearIsometry.coe_toLinearMap, sub_eq_add_neg]

def pairedRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=PairedValue root visit recognition successor (H:=H)) (Var:=PairedVar) (sort:=PairedSlot.paired) :=
  ⟨pairedEnvironment root visit recognition successor value, pairedProgramme root visit recognition successor transition node⟩
abbrev pairedReader := fun (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) =>
  pairedRaw root visit recognition successor transition node value
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
abbrev pairedRuntime := SourceTemporalMaterial.Calculation.runtime root visit U7 calculus
  (pairedReader root visit recognition successor transition node value)
end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
