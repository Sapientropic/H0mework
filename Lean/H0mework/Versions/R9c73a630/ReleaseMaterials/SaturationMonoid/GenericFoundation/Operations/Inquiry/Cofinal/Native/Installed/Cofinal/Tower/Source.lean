import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Consumer
import H0mework.Realization.ScalarCofinal.Naturality
import H0mework.Realization.Operations.ScalarExact
import Mathlib.LinearAlgebra.DFinsupp
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCofinalNativeTower"

/-! The fixed coefficient source contains each actual admission's complete native
word at its own grade. Its observations consume the existing installed Env and
actual native increment, before forming finite prefixes. Prefix restriction is
derived from these source observations. Complete runtime states keep their
original separate carrier. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalNativeTower
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation
open SourceOperationScalarInventoryLift SourceGeneratedScalarCofinalKernelCompletion CategoryTheory CategoryTheory.Limits
namespace C
export ActualCofinalInstalledRaw (packet rawAtStop materialAtStop installed_request materialAtStop_source)
end C
namespace SF
export ActualCofinalInstalledRaw.SF (Factory)
end SF
namespace L
export ActualCofinalInstalledRaw.L (Value groups)
end L
namespace M
export ActualCofinalInstalledRaw.M (Frame)
end M
namespace A
export ActualCofinalInstalledRaw.A (Programme)
end A
namespace O
export ActualCofinalInstalledRaw.O (readRaw)
end O
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression old_value updated_value input)
end N
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) :
 AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

abbrev NativeValue (ordinal : Nat) := L.Value W (C.packet factory initial cfg language ordinal).1
abbrev Words (ordinal : Nat) := Formal ℤ (NativeValue factory initial cfg language ordinal) X s

/-- A finite complete word can use multiple source sites; their native grades stay dependent. -/
abbrev CommonWords := Π₀ ordinal : Nat, Words factory initial cfg language ordinal

/-- Restrict an existing complete coefficient word to its original native site. -/
abbrev component (ordinal : Nat) : CommonWords factory initial cfg language →ₗ[ℤ]
 Words factory initial cfg language ordinal := DFinsupp.lapply ordinal

/-- The original source AST enters the shared coefficient carrier at its exact site. -/
def sourceWord (ordinal : Nat) (expression : Expr (NativeValue factory initial cfg language ordinal) X s) :
 CommonWords factory initial cfg language :=
 DFinsupp.lsingle (R := ℤ) ordinal (Finsupp.single expression 1)

theorem sourceWord_component (ordinal : Nat)
 (expression : Expr (NativeValue factory initial cfg language ordinal) X s) :
 component factory initial cfg language ordinal (sourceWord factory initial cfg language ordinal expression) =
 Finsupp.single expression 1 := DFinsupp.single_eq_same

def oldEnvironment (ordinal : Nat) : Env (NativeValue factory initial cfg language ordinal) X :=
 (O.readRaw _ (C.rawAtStop factory initial cfg language ordinal)).environment

def actualIncrement (ordinal : Nat) : Env (NativeValue factory initial cfg language ordinal) X :=
 (C.materialAtStop factory initial cfg language ordinal).increment

/-- The old coordinate is read from the actual installed projection, not an observation table. -/
theorem installed_environment (ordinal : Nat) : oldEnvironment factory initial cfg language ordinal =
 (C.materialAtStop factory initial cfg language ordinal).environment :=
 (C.installed_request factory initial cfg language ordinal).1

/-- The original native old/effect inventory evaluates each full local coefficient word. -/
def nativeInventory (ordinal : Nat) : Words factory initial cfg language ordinal →ₗ[ℤ]
 NativeValue factory initial cfg language ordinal s × NativeValue factory initial cfg language ordinal s :=
 updateInventory (R := ℤ) (oldEnvironment factory initial cfg language ordinal)
  (actualIncrement factory initial cfg language ordinal)

def stageInventory (ordinal : Nat) : CommonWords factory initial cfg language →ₗ[ℤ]
 NativeValue factory initial cfg language ordinal s × NativeValue factory initial cfg language ordinal s :=
 (nativeInventory factory initial cfg language ordinal).comp (component factory initial cfg language ordinal)

abbrev Prefix (bound : Nat) := (index : Fin (bound + 1)) →
 NativeValue factory initial cfg language index.val s × NativeValue factory initial cfg language index.val s

def prefixEvaluator (bound : Nat) : CommonWords factory initial cfg language →ₗ[ℤ]
 Prefix factory initial cfg language bound :=
 LinearMap.pi fun index => stageInventory factory initial cfg language index.val

/-- This drops only the last actual source observation. -/
def restriction (bound : Nat) : Prefix factory initial cfg language (bound + 1) →ₗ[ℤ]
 Prefix factory initial cfg language bound :=
 LinearMap.pi fun index => LinearMap.proj index.castSucc

/-- Both fields are constructed from the original source packets and their local actual effects. -/
def data : Data (R := ℤ) (Generator := CommonWords factory initial cfg language)
 (Carrier := Prefix factory initial cfg language) where
 evaluator := prefixEvaluator factory initial cfg language
 transition := restriction factory initial cfg language

theorem compatible : (data factory initial cfg language).Compatible := by
 intro bound
 apply LinearMap.ext
 intro word
 funext index
 rfl

/-- The actual installed raw is itself an emitted word of this fixed source module. -/
def registeredWord (ordinal : Nat) : CommonWords factory initial cfg language :=
 sourceWord factory initial cfg language ordinal
  (O.readRaw _ (C.rawAtStop factory initial cfg language ordinal)).expression

/-- The local residual has its own word; it does not replace the previous registered sigma. -/
def residualWord (ordinal : Nat) : CommonWords factory initial cfg language :=
 sourceWord factory initial cfg language ordinal
  (N.expression (C.materialAtStop factory initial cfg language ordinal))

/-- This inventory square is generated by the original literal AST lift and actual increment. -/
theorem actual_inventory_square (ordinal : Nat) :
 (evaluation (R := ℤ) (pairEnvironment (oldEnvironment factory initial cfg language ordinal)
  (actualIncrement factory initial cfg language ordinal))).comp
  ((liftMap (R := ℤ)).comp (component factory initial cfg language ordinal)) =
 stageInventory factory initial cfg language ordinal := by
 rw [← LinearMap.comp_assoc,evaluation_liftMap]
 rfl

/-- On the actual native residual the second coordinate is the original source-generated effect. -/
theorem actual_residual_inventory (ordinal : Nat) :
 stageInventory factory initial cfg language ordinal (residualWord factory initial cfg language ordinal) =
 (0, effectEvaluator (R := ℤ) (C.materialAtStop factory initial cfg language ordinal).environment
  (C.materialAtStop factory initial cfg language ordinal).increment
  (SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace.boundary
   (C.materialAtStop factory initial cfg language ordinal))) := by
 change nativeInventory factory initial cfg language ordinal
  (component factory initial cfg language ordinal (residualWord factory initial cfg language ordinal)) = _
 rw [residualWord,sourceWord_component]
 simp only [nativeInventory,updateInventory,LinearMap.prod_apply,Function.prod,
  SourceOperationScalarRelations.evaluation,effectEvaluator,
  Finsupp.linearCombination_single,one_smul]
 change ((N.expression (C.materialAtStop factory initial cfg language ordinal)).eval
  (oldEnvironment factory initial cfg language ordinal),
  (N.expression (C.materialAtStop factory initial cfg language ordinal)).effect
   (oldEnvironment factory initial cfg language ordinal) (actualIncrement factory initial cfg language ordinal)) = _
 rw [installed_environment]
 apply Prod.ext
 · exact N.old_value _
 · have update := N.updated_value (R := ℤ) (C.materialAtStop factory initial cfg language ordinal)
   rw [RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input,Expr.eval_update,N.old_value,zero_add] at update
   exact update

end ActualCofinalNativeTower
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
