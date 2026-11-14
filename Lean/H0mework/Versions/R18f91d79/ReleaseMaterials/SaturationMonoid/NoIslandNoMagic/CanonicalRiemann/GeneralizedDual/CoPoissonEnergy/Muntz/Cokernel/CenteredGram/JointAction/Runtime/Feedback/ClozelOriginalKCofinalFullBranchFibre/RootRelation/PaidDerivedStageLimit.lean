import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Cochain.DerivedNaturality
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCofinalCochain
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open CategoryTheory BurnolPhysicalState SourceOperationScalarInventoryLift
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations SourceGeneratedPrimePowerCompletion
open SourceOperationCompletion
open CofinalRelationGeneratedComplex

attribute [local instance] relationGroups

open private paidRuntime from
  H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidDerivedContinuation

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

private def extendPaidHomotopy {source target : CochainComplex (ModuleCat ℤ) ℕ}
    (action : HomotopyEquiv source target) :
    HomotopyEquiv (source.extend ComplexShape.embeddingUpNat) (target.extend ComplexShape.embeddingUpNat) where
  hom := HomologicalComplex.extendMap action.hom ComplexShape.embeddingUpNat
  inv := HomologicalComplex.extendMap action.inv ComplexShape.embeddingUpNat
  homotopyHomInvId := by
    simpa only [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id] using
      action.homotopyHomInvId.extend ComplexShape.embeddingUpNat
  homotopyInvHomId := by
    simpa only [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id] using
      action.homotopyInvHomId.extend ComplexShape.embeddingUpNat

-- Preserve the dependent let chain while checking the original receipt.
set_option cleanup.letToHave false in
/-- The actual paid map acts on both cochain limits of a literal original R tick. -/
def actual_paid_derived_stage_limit
    (index : Fin (Calc.originalFrontier observation nontrivial half depth ordinal).stageCount)
    (p : Nat.Primes) (stage : Nat) :=
  let source := sourceRoot observation nontrivial half depth ordinal
  let origin := sourceCurrent observation nontrivial half depth ordinal
  let reader := sourceReader observation nontrivial half depth ordinal
  let runtime := paidRuntime observation nontrivial half depth ordinal index.val
  let arrived := runtime.tick.next
  let first := RootedAccountedUnfolding.zero runtime.emittedOccurrence
  let next := RootedAccountedUnfolding.zero arrived.emittedOccurrence
  let prior := (Paid.runtimeCurrent source origin reader runtime).2
  let later := (Paid.runtimeCurrent source origin reader arrived).2
  let retained := Paid.tick_paid_prefix source origin reader runtime
  let shape := ComplexShape.up ℤ
  let forget := forget₂ (ModuleCat ℤ) AddCommGrpCat
  let groups := forget.mapHomologicalComplex shape
  let before := groups.obj (intComplex (prefixHistory first (exposure prior)))
  let after := groups.obj (intComplex (prefixHistory next (exposure later)))
  let original := continuationCochainHomotopyEquiv first prior next later retained
  let paid := forget.mapHomotopyEquiv (extendPaidHomotopy original)
  let paidCofiber := continuationDerivedCofiber first prior next later retained
  let firstMap := cochainDerivedLimitMap first p before
  let nextMap := cochainDerivedLimitMap next p after
  let action := cochainDerivedAction first next p paid.hom
  let comparison := cochain_derived_limit_naturality first next p paid.hom
  let firstIso := cochain_derived_limit_quasiIso first p before
  let nextIso := cochain_derived_limit_quasiIso next p after
  let advances := cochain_derived_action_quasiIso first next p paid
  let exactAction : paid.hom = groups.map paidCofiber.actualTransition := rfl
  let topology := actual_paid_derived_continuation observation nontrivial half depth ordinal index
  PProd.mk (firstMap, nextMap, action) (And.intro exactAction (And.intro comparison
    (And.intro firstIso (And.intro nextIso (And.intro advances
      (And.intro (cochain_derived_limit_stage first p before stage)
        (And.intro (cochain_derived_limit_stage next p after stage) topology)))))))

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
