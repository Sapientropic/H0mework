import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Cochain.Homology
import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFactorialCompletion

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationScalarInventoryLift
open SourceOperationCompletion CofinalAllPrimeTopology

attribute [local instance] relationGroups

open private paidTrace from H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCompletion
open private paidEvaluation from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage
open private sourceDivides from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFiniteModulus

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The original exact R occurrence owns the factorial homotopy-limit cohomology. -/
def actualPaidFactorialHomologyIso :=
  factorialPaidHomologyIso (.zero (sourceRuntime observation nontrivial half depth ordinal).emittedOccurrence)
    (paidTrace observation nontrivial half depth ordinal)

-- Keep the original occurrence and the dependent cochain class let-bound.
set_option cleanup.letToHave false in
/-- Every original factorial H¹ class supplies the entire evaluator family and native next read. -/
def actual_paid_factorial_homology_next :=
  fun charge =>
  let coordinate := actualPaidFactorialHomologyIso observation nontrivial half depth ordinal
  let source := coordinate.hom.hom.toFun charge
  let evaluate := paidEvaluation observation nontrivial half depth ordinal
  let faithful := actual_paid_evaluation_injective observation nontrivial half depth ordinal
  let divides := sourceDivides observation nontrivial half depth ordinal
  let cokernel := allPrimeCokernelEquiv evaluate faithful divides
  let coordinates := factorialToPrimes source
  let family := cokernel.toLinearMap.toFun coordinates
  let written := actual_paid_factorial_next observation nontrivial half depth ordinal family
  let original := (congrArg factorialFromPrimes (cokernel.symm_apply_apply coordinates)).trans
    ((factorialCompletionEquiv (L := SourceCompletion observation nontrivial half depth ordinal)).apply_symm_apply source)
  PProd.mk (family, written.1.2) (And.intro original written.2)

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
