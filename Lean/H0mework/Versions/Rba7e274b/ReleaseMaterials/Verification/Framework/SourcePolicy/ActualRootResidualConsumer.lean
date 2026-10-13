import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.RootConsumer.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP121RootResidualControls
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open ActualCofinalRootResidualConsumer
section Direct
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance nativeGroups (grade : Nat) (target : Sorts) : AddCommGroup (CA.Value W grade target) := CA.groups W grade target
variable (factory : CA.Factory W X s)
variable (initial : CA.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : CA.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

example (ordinal : Nat) : type_of% (residual_word_registered factory initial cfg language ordinal) :=
 residual_word_registered factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (next_model_residual factory initial cfg language ordinal) :=
 next_model_residual factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (original_compiles factory initial cfg language ordinal) :=
 original_compiles factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (actual_generated_current factory initial cfg language ordinal) :=
 actual_generated_current factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (rooted_request_model factory initial cfg language ordinal) :=
 rooted_request_model factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (rooted_material_source factory initial cfg language ordinal) :=
 rooted_material_source factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (rooted_request_source factory initial cfg language ordinal) :=
 rooted_request_source factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (rooted_request_transport factory initial cfg language ordinal) :=
 rooted_request_transport factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (original_whole factory initial cfg language ordinal) :=
 original_whole factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (originalOldRow factory initial cfg language ordinal) :=
 originalOldRow factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (originalBornRow factory initial cfg language ordinal) :=
 originalBornRow factory initial cfg language ordinal
example (ordinal : Nat) (history : List PUnit.{u+1}) (target : Nat) :
 type_of% (actual_root_future factory initial cfg language ordinal history target) :=
 actual_root_future factory initial cfg language ordinal history target
example {Result : Sort v} (ordinal : Nat)
 (read : (request : C.RequestAtCurrent
   (Value := CA.NativeValue factory initial cfg language (ordinal+1)) (Var := X) (s := s)
   (generatedCurrent factory initial cfg language ordinal)) →
  CA.projection factory initial cfg language
   (DFinsupp.single (ordinal+1) (Finsupp.single request.expression 1)) =
   CA.projection factory initial cfg language
    (DFinsupp.single (ordinal+1) (boundaryWord factory initial cfg language ordinal)) →
  type_of% (original_compiles factory initial cfg language ordinal) →
  type_of% (original_whole factory initial cfg language ordinal) → Result) : Result :=
 actual_root_eliminate factory initial cfg language ordinal read

example (ordinal : Nat) :
 DFinsupp.single (ordinal+1) (Finsupp.single (rootedRequest factory initial cfg language ordinal).expression 1) ≠
 ActualCofinalNativeTower.residualWord factory initial cfg language (ordinal+1) := by
 intro same
 have components := congrArg (ActualCofinalNativeTower.component factory initial cfg language (ordinal+1)) same
 rw [ActualCofinalNativeTower.residualWord, ActualCofinalNativeTower.sourceWord_component] at components
 change (DFinsupp.single (ordinal+1)
  (Finsupp.single (rootedRequest factory initial cfg language ordinal).expression (1 : ℤ)) :
  ActualCofinalNativeTower.CommonWords factory initial cfg language) (ordinal+1) = _ at components
 rw [DFinsupp.single_eq_same] at components
 change Finsupp.single (rootedRequest factory initial cfg language ordinal).expression 1 =
  Finsupp.single (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
   (ActualCofinalInstalledRaw.materialAtStop factory initial cfg language (ordinal+1))) 1 at components
 have expressions := Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) components
 have raw : (rootedRequest factory initial cfg language ordinal).expression =
   (ActualCofinalInstalledRaw.materialAtStop factory initial cfg language (ordinal+1)).raw :=
  (rooted_request_source factory initial cfg language ordinal).2.1.trans
   ((rooted_material_source factory initial cfg language ordinal).2.1.trans
    (C.materialAtStop_source factory initial cfg language (ordinal+1)).2.1.symm)
 have sizes := congrArg remaining (raw.symm.trans expressions)
 rw [RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget] at sizes
 omega
end Direct

namespace Literal
abbrev V := fun _ : Unit => ℤ
abbrev X := fun _ : Unit => Unit
def raw : Expr V X () := .var ()
def prior : Expr V X () := .const 0
def residual : Expr V X () := .add raw (.linear (-AddMonoidHom.id ℤ) prior)
def zeroEnv : Env V X := fun _ _ => 0
def oneEnv : Env V X := fun _ _ => 1
theorem at_zero : residual.eval zeroEnv = 0 := rfl
theorem at_one : residual.eval oneEnv = 1 := rfl

theorem residual_boundary :
 Finsupp.single residual 1 - (Finsupp.single raw 1 - Finsupp.single prior 1) ∈
 ActualCofinalResidualModelSplice.semanticZero :=
 ActualCofinalResidualModelSplice.residual_semantic_zero raw prior

theorem residual_not_universal_zero :
 Finsupp.single residual 1 ∉ ActualCofinalResidualModelSplice.semanticZero := by
 intro member
 have zero := member oneEnv
 simp [evaluation, Finsupp.linearCombination_single,
  Expr.eval, residual, raw, prior, oneEnv] at zero

def zeroWord : Formal ℤ V X () := Finsupp.single (.const 0) 1
theorem zero_word_not_formal_zero : zeroWord ≠ 0 := by
 simp [zeroWord]
theorem zero_word_semantic_zero : zeroWord ∈ ActualCofinalResidualModelSplice.semanticZero := by
 intro environment
 simp [zeroWord, evaluation, Finsupp.linearCombination_single, Expr.eval]
end Literal

#print axioms ActualCofinalResidualModelSplice.semantic_model_equiv
#print axioms ActualCofinalResidualModelSplice.residual_boundary_model
#print axioms next_model_residual
#print axioms original_compiles
#print axioms actual_generated_current
#print axioms rootedRequest
#print axioms rootedMaterial
#print axioms rooted_material_source
#print axioms rooted_request_source
#print axioms rooted_request_transport
#print axioms rooted_request_model
#print axioms original_whole
#print axioms originalOldRow
#print axioms originalBornRow
#print axioms consume
#print axioms actual_root_future
#print axioms actual_root_eliminate
#print axioms Literal.residual_not_universal_zero
#print axioms Literal.zero_word_not_formal_zero
end CP121RootResidualControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
