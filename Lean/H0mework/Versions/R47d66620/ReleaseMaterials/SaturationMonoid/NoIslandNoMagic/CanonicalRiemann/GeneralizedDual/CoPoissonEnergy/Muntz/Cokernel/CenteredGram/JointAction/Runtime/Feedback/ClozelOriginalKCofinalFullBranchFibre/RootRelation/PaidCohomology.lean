import H0mework.Versions.R47d66620.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Cohomology.Naturality
import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion

-- These dependent theorems are consumed by name.
run_cmd Lean.modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_cohomology_cokernel_stage"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_cohomology_cokernel_next"

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open CategoryTheory BurnolPhysicalState SourceOperationScalarInventoryLift
open SourceOperationCompletion SourceGeneratedPrimePowerCompletion

attribute [local instance] relationGroups

open private paidTrace from
  H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCompletion
open private paidEvaluation from
  H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage
open private modelCharge from
  H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

private abbrev paidRoot :=
  RootedAccountedUnfolding.zero (sourceRuntime observation nontrivial half depth ordinal).emittedOccurrence

local notation "rootAt" => paidRoot observation nontrivial half depth ordinal
local notation "traceAt" => paidTrace observation nontrivial half depth ordinal

/-- Degree one of the completed original R complex is its original coherent relation quotient. -/
def actualPaidCohomologyIso (p : Nat.Primes) :
    (observedPaidComplex rootAt traceAt (completionFunctor p)).homology 1 ≅
      Completion (L := SourceCompletion observation nontrivial half depth ordinal) p :=
  paidObservedCohomologyIso rootAt traceAt (completionFunctor p)

/-- The original evaluator connects the entire coherent cohomology to its actual cokernel. -/
def actualPaidCohomologyCokernel (p : Nat.Primes) :=
  (actualPaidCohomologyIso observation nontrivial half depth ordinal p).toLinearEquiv.trans
    (actualPaidCokernelCompletion observation nontrivial half depth ordinal p)

theorem actual_paid_cohomology_cokernel_stage (p : Nat.Primes) (j : Nat)
    (charge : (observedPaidComplex rootAt traceAt (completionFunctor p)).homology 1) :
    let restriction := completionFunctorRestriction p j
    let map := (restriction.mapHomologicalComplex (ComplexShape.up ℕ)).app (paidGroupComplex rootAt traceAt)
    let finiteRead := paidObservedCohomologyIso rootAt traceAt (stageFunctor p j)
    (torsionCompletionRestriction (_ ⧸ LinearMap.range (paidEvaluation observation nontrivial half depth ordinal)) p j).hom
        (actualPaidCohomologyCokernel observation nontrivial half depth ordinal p charge) =
      actualPaidCokernelStage observation nontrivial half depth ordinal p j
        (finiteRead.hom (HomologicalComplex.homologyMap map 1 charge)) := by
  let read := actualPaidCohomologyIso observation nontrivial half depth ordinal p
  let finiteRead := actualPaidCokernelStage observation nontrivial half depth ordinal p j
  have fromOriginal := actual_paid_cokernel_completion_restriction observation nontrivial half depth ordinal p j
    (read.hom charge)
  have restriction := ConcreteCategory.congr_hom
    (paid_cohomology_restriction rootAt traceAt (completionFunctorRestriction p j)) charge
  exact fromOriginal.trans (congrArg (fun stage => finiteRead stage) restriction.symm)

/-- The original factor and model action consume every coherent degree-one charge at their literal next ordinal. -/
theorem actual_paid_cohomology_cokernel_next (p : Nat.Primes)
    (charge : (observedPaidComplex rootAt traceAt (completionFunctor p)).homology 1) :
    actualPaidCokernelCompletionNext observation nontrivial half depth ordinal p
      (actualPaidCohomologyCokernel observation nontrivial half depth ordinal p charge) =
      actualPaidModelCokernelCompletion observation nontrivial half depth (ordinal+1) p
        (inducedCompletionLinearMap p (modelCharge observation nontrivial half depth ordinal)
          ((actualPaidCohomologyIso observation nontrivial half depth ordinal p).hom charge)) :=
  actual_paid_cokernel_coherent_next observation nontrivial half depth ordinal p
    ((actualPaidCohomologyIso observation nontrivial half depth ordinal p).hom charge)

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
