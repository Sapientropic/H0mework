import H0mework.Versions.R47d66620.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Settlement
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Cofinal
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open CategoryTheory CategoryTheory.Limits CofinalHistorySettlement CofinalRelationGeneratedComplex
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations

variable {S Root : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before after : Expr V X s}
variable (root : RootedAccountedUnfolding Root) (paid : Trace old before after)
variable (observe : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ) [observe.Additive]

local notation "sourceHistory" => prefixHistory root (exposure paid)

abbrev observedPaidComplex : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  (observe.mapHomologicalComplex (ComplexShape.up ℕ)).obj (paidGroupComplex root paid)

private abbrev observedSettlement :=
  (paidCochainSettlement root paid).map (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat ⋙ observe)

private theorem observed_next_zero : ((observedPaidComplex root paid observe).sc' 0 1 2).g = 0 := by
  let lift := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat ⋙ observe
  change lift.map ((natComplex sourceHistory).d 1 2) = 0
  have original : (natComplex sourceHistory).d 1 2 = 0 :=
    CochainComplex.of_d (CofinalRelationGeneratedComplex.object sourceHistory) (differential sourceHistory) 1
  rw [original, Functor.map_zero]

private def observedCofork : CokernelCofork ((observedPaidComplex root paid observe).sc' 0 1 2).f :=
  CokernelCofork.ofπ (observedSettlement root paid observe).g (observedSettlement root paid observe).zero

private def observedCoforkIsColimit : IsColimit (observedCofork root paid observe) :=
  ((paidCochainSettlementSplitting root paid).map (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat ⋙ observe)).gIsCokernel

private def observedHomologyData : ((observedPaidComplex root paid observe).sc' 0 1 2).HomologyData :=
  ShortComplex.HomologyData.ofIsColimitCokernelCofork ((observedPaidComplex root paid observe).sc' 0 1 2)
    (observed_next_zero root paid observe) (observedCofork root paid observe) (observedCoforkIsColimit root paid observe)

/-- The actual observed degree-one cohomology is the observed original relation quotient. -/
def paidObservedCohomologyIso : (observedPaidComplex root paid observe).homology 1 ≅
    observe.obj (AddCommGrpCat.of (sourceHistory).CompletionCarrier) :=
  ((observedPaidComplex root paid observe).homologyIsoSc' 0 1 2 (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1)) ≪≫
    (observedHomologyData root paid observe).left.homologyIso

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
