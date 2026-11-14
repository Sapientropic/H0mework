import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Retraction
import Mathlib.Algebra.Homology.ShortComplex.Exact

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open CategoryTheory CofinalHistorySettlement CofinalRelationGeneratedComplex
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations

open private readRelations read_relation from
  SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Retraction

variable {S Root : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before after : Expr V X s}
variable (root : RootedAccountedUnfolding Root) (paid : Trace old before after)

local notation "sourceHistory" => prefixHistory root (exposure paid)

/-- The original differential and quotient projection are the paid settlement sequence. -/
def paidCochainSettlement : ShortComplex (ModuleCat.{u} ℤ) :=
  ShortComplex.mk ((natComplex sourceHistory).d 0 1) (ModuleCat.ofHom (sourceHistory).completionProjection)
    (ModuleCat.hom_ext (LinearMap.ext fun relation => completion_kills_generated_differential sourceHistory relation))

private def terminalSection : (sourceHistory).CompletionCarrier →ₗ[ℤ] (sourceHistory).generatorClosure :=
  (LinearMap.toSpanSingleton ℤ _ (terminalGenerator root paid)).comp (paidCompletionEquiv root paid).toLinearMap

/-- The actual relation ranks and the terminal unit split the source's own settlement sequence. -/
def paidCochainSettlementSplitting : (paidCochainSettlement root paid).Splitting where
  r := ModuleCat.ofHom ((readRelations root paid).comp (sourceHistory).generatorClosure.subtype)
  s := ModuleCat.ofHom (terminalSection root paid)
  f_r := by
    change ((natComplex sourceHistory).d 0 1) ≫
      ModuleCat.ofHom ((readRelations root paid).comp (sourceHistory).generatorClosure.subtype) = 𝟙 _
    rw [natComplex_d_zero_one sourceHistory]
    exact ModuleCat.hom_ext (LinearMap.ext (read_relation root paid))
  s_g := ModuleCat.hom_ext (LinearMap.ext fun value =>
    (paid_completion_terminal root paid (paidCompletionEquiv root paid value)).symm.trans
      ((paidCompletionEquiv root paid).symm_apply_apply value))
  id := ModuleCat.hom_ext (LinearMap.ext fun word =>
    (congrArg (fun coefficient : ℤ =>
      ((natComplex sourceHistory).d 0 1).hom (readRelations root paid word.val) +
        coefficient • terminalGenerator root paid) (paid_completion_source root paid word)).trans
      (paid_differential_split root paid word))

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
