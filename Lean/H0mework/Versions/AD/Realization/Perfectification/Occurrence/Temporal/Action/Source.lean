import H0mework.Versions.AD.Realization.Perfectification.Occurrence.Temporal.Source
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Source
import H0mework.Realization.Operations.InventoryLift
/-! The original compiler action retains the complete visit and canonical
material. Its continuing next is encoded exactly; terminal keeps the
original receipt. Neither an outcome nor an equation enters the primitive. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceTemporalMaterial.Action
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLivingRootClosure N V)
abbrev lower := root.toAuthoritativeRoot.toLedgerRoot
abbrev Receipt := Σ code : Code (lower root),
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.SourceMaterialAt root.toAuthoritativeRoot
    ((lower root).emitted code.current)
def receipt (code : Code (lower root)) : Receipt root := ⟨code, RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt root.toAuthoritativeRoot ((lower root).emitted code.current)⟩
def nextCode (code : Code (lower root)) : Option (Code (lower root)) :=
  match actual : ((lower root).toRoot.evolutionAt code.current).nextCurrent? with
  | none => none
  | some _target => some (next (lower root) code actual)
abbrev Result := Receipt root × Option (Code (lower root))
def actual (code : Code (lower root)) : Result root := ⟨receipt root code, nextCode root code⟩
def push : (Code (lower root) →₀ ℤ) →ₗ[ℤ] (Result root →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ (actual root)
inductive Slot : Type u | source | result
abbrev Value : Slot.{u} → Type u | .source => Code (lower root) →₀ ℤ | .result => Result root →₀ ℤ
abbrev Var : Slot.{u} → Type u := fun _ => PUnit.{u+1}
instance : (slot : Slot.{u}) → AddCommGroup (Value root slot)
  | .source => inferInstance
  | .result => inferInstance
def environment (code : Code (lower root)) : Env (Value root) (Var) :=
  fun slot _ => match slot with | .source => Finsupp.single code 1 | .result => 0
def programme : Expr (Value root) Var .result := .linear (s:=.source) (push root).toAddMonoidHom (.var PUnit.unit)
theorem programme_value (code : Code (lower root)) :
    (programme root).eval (environment root code) = Finsupp.single (actual root code) 1 := by
  change Finsupp.mapDomain (actual root) (Finsupp.single code (1 : ℤ)) = _
  exact Finsupp.mapDomain_single
def updatedEnvironment (code : Code (lower root)) : Env (Value root) Var :=
  match nextCode root code with
  | none => environment root code
  | some next => environment root next
abbrev delta (code : Code (lower root)) := updatedEnvironment root code - environment root code
def raw (code : Code (lower root)) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=PairValue (Value root)) (Var:=Var) (sort:=Slot.result) :=
  ⟨pairEnvironment (environment root code) (delta root code), liftExpr (programme root)⟩
theorem raw_value (code : Code (lower root)) : (raw root code).expression.eval (raw root code).environment =
    (Finsupp.single (actual root code) 1,
      (programme root).eval (updatedEnvironment root code) - Finsupp.single (actual root code) 1) := by
  rw [show (raw root code).expression.eval (raw root code).environment = _ from
    eval_liftExpr (programme root) (environment root code) (delta root code)]
  apply Prod.ext
  · exact programme_value root code
  · have generated := Expr.eval_update (programme root) (environment root code) (delta root code)
    rw [show environment root code + delta root code = updatedEnvironment root code from add_sub_cancel _ _] at generated
    rw [programme_value] at generated
    exact eq_sub_of_add_eq (by rw [add_comm]; exact generated.symm)
theorem actual_injective : Function.Injective (actual root) := by
  intro first second same
  exact congrArg (fun value : Result root => value.1.1) same

theorem nextCode_exact {target : V.Current} (code : Code (lower root))
    (actual : ((lower root).toRoot.evolutionAt code.current).nextCurrent? = some target) :
    nextCode root code = some (next (lower root) code actual) := by
  unfold nextCode
  split
  next selected => exact False.elim (by rw [actual] at selected; cases selected)
  next destination selected =>
    have same : destination = target := Option.some.inj (selected.symm.trans actual)
    cases same
    rfl

theorem nextCode_terminal (code : Code (lower root))
    (actual : ((lower root).toRoot.evolutionAt code.current).nextCurrent? = none) :
    nextCode root code = none := by
  unfold nextCode
  split
  next => rfl
  next destination selected => exact False.elim (by rw [actual] at selected; cases selected)

theorem effect_value (code : Code (lower root)) :
    (programme root).effect (environment root code) (delta root code) =
      (programme root).eval (updatedEnvironment root code) - Finsupp.single (actual root code) 1 := by
  have generated := Expr.eval_update (programme root) (environment root code) (delta root code)
  rw [show environment root code + delta root code = updatedEnvironment root code from add_sub_cancel _ _] at generated
  rw [programme_value] at generated
  exact eq_sub_of_add_eq (by rw [add_comm]; exact generated.symm)

end SourceTemporalMaterial.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
