import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Cochain.Derived
import H0mework.Versions.R47d66620.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Cohomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open CategoryTheory CategoryTheory.Limits CofinalHistorySettlement CofinalRelationGeneratedComplex
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations CofinalAllPrimeTopology

private theorem integral_extension_d (K : CochainComplex (ModuleCat ℤ) ℕ) (i j : Nat) :
    (K.extend ComplexShape.embeddingUpNat).d (i : ℤ) (j : ℤ) ≫
        (K.extendXIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f j = (j : ℤ) from rfl)).hom =
      (K.extendXIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f i = (i : ℤ) from rfl)).hom ≫ K.d i j := by
  let e := ComplexShape.embeddingUpNat
  let left := K.extendXIso e (show e.f i = (i : ℤ) from rfl)
  let right := K.extendXIso e (show e.f j = (j : ℤ) from rfl)
  have written : (K.extend e).d (i : ℤ) (j : ℤ) = left.hom ≫ K.d i j ≫ right.inv :=
    K.extend_d_eq e rfl rfl
  change (K.extend e).d (i : ℤ) (j : ℤ) ≫ right.hom = left.hom ≫ K.d i j
  exact (congrArg (fun d => d ≫ right.hom) written).trans (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

private def integral_extension_short_complex (K : CochainComplex (ModuleCat ℤ) ℕ) :
    (K.extend ComplexShape.embeddingUpNat).sc' 0 1 2 ≅ K.sc' 0 1 2 :=
  ShortComplex.isoMk (K.extendXIso ComplexShape.embeddingUpNat rfl)
    (K.extendXIso ComplexShape.embeddingUpNat rfl) (K.extendXIso ComplexShape.embeddingUpNat rfl)
    (integral_extension_d K 0 1).symm (integral_extension_d K 1 2).symm

variable {S Root : Type} {V X : S → Type} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before after : Expr V X s}
variable (root : RootedAccountedUnfolding Root) (paid : Trace old before after)

local notation "history" => prefixHistory root (exposure paid)
local notation "forget" => forget₂ (ModuleCat ℤ) AddCommGrpCat

/-- The already generated integral relation complex supplies the factorial tower. -/
abbrev paidIntegralGroupComplex : CochainComplex AddCommGrpCat ℤ :=
  ((forget).mapHomologicalComplex (ComplexShape.up ℤ)).obj (intComplex history)

private def observedIntegralHomologyIso (observe : AddCommGrpCat ⥤ ModuleCat ℤ) [observe.Additive] :
    ((observe.mapHomologicalComplex (ComplexShape.up ℤ)).obj (paidIntegralGroupComplex root paid)).homology 1 ≅
      (observedPaidComplex root paid observe).homology 1 := by
  let observed := (observe.mapHomologicalComplex (ComplexShape.up ℤ)).obj (paidIntegralGroupComplex root paid)
  let original := observedPaidComplex root paid observe
  let windows := ((forget ⋙ observe).mapShortComplex).mapIso (integral_extension_short_complex (natComplex history))
  have previous : (ComplexShape.up ℤ).prev 1 = 0 := (ComplexShape.up ℤ).prev_eq' rfl
  have following : (ComplexShape.up ℤ).next 1 = 2 := (ComplexShape.up ℤ).next_eq' rfl
  exact observed.homologyIsoSc' 0 1 2 previous following ≪≫
    (ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso windows ≪≫
    (original.homologyIsoSc' 0 1 2 (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1)).symm

/-- The whole factorial homotopy-limit H¹ reads the original paid relation quotient. -/
def factorialPaidHomologyIso :
    (factorialDerivedLimitFace root (paidIntegralGroupComplex root paid)).homotopyLimit.homology 1 ≅
      factorialCompletionFunctor.obj (AddCommGrpCat.of (history).CompletionCarrier) := by
  let source := paidIntegralGroupComplex root paid
  let comparison := factorialDerivedLimitMap root source
  let exactness := factorial_derived_limit_quasiIso root source
  letI : IsIso (HomologicalComplex.homologyMap comparison 1) :=
    (quasiIsoAt_iff_isIso_homologyMap comparison 1).1 (exactness.quasiIsoAt 1)
  exact (asIso (HomologicalComplex.homologyMap comparison 1)).symm ≪≫
    observedIntegralHomologyIso root paid factorialCompletionFunctor ≪≫
    paidObservedCohomologyIso root paid factorialCompletionFunctor

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
