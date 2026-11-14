import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Action
import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFiniteModulus

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationScalarInventoryLift
open SourceGeneratedPrimePowerCompletion CofinalAllPrimeTopology

attribute [local instance] relationGroups

open private paidEvaluation from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage
open private modelCharge complex_power_bijective from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel
open private sourceDivides from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFiniteModulus

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

-- Keep the original dependent context let-bound across the full family comparison.
set_option cleanup.letToHave false in
/-- The same factorial limit transports the entire original evaluator cokernel to the literal next model. -/
def actual_paid_factorial_next :=
  fun family =>
  let evaluate := paidEvaluation observation nontrivial half depth ordinal
  let faithful := actual_paid_evaluation_injective observation nontrivial half depth ordinal
  let divides := sourceDivides observation nontrivial half depth ordinal
  let inverse := allPrimeCokernelEquiv evaluate faithful divides
  let connected := inverse.symm.toLinearMap.toFun family
  let source := factorialFromPrimes connected
  let move := modelCharge observation nontrivial half depth ordinal
  let written := factorialCompletionAction move source
  let nextFactor := factor observation nontrivial half depth (ordinal+1)
  let nextFaithful := actual_paid_factor_injective observation nontrivial half depth (ordinal+1)
  let next := allPrimeCokernelEquiv nextFactor nextFaithful (fun prime => complex_power_bijective prime)
  let before := (congrArg inverse.toLinearMap.toFun (factorial_to_primes_from_primes connected)).trans
    (inverse.apply_symm_apply family)
  let after := funext (fun prime : Nat.Primes =>
    let step := (actualPaidCokernelCompletionNext observation nontrivial half depth ordinal prime).toFun
    (actual_paid_cokernel_coherent_next observation nontrivial half depth ordinal prime (connected prime)).symm.trans
      (congrArg step (all_prime_cokernel_roundtrip evaluate faithful divides family prime)))
  let advanced := (congrArg next.toLinearMap.toFun (factorial_action_readback move connected)).trans after
  let finite := fun address : Nat =>
    let modulus := factorialModulus address
    let nonzero := factorial_modulus_ne_zero address
    let primes := modulusPrimes modulus
    let levels := modulusDepth modulus
    let charge := actual_paid_finite_charge_next observation nontrivial half depth ordinal primes levels family
    let coordinate := actualPaidCompletion observation nontrivial half depth ordinal
    let projected := (modulus_projection_eq_iff modulus nonzero charge.1 connected).2
      (finite_prime_integral_lift primes levels coordinate connected).1
    And.intro ((factorial_from_primes_restriction address connected).trans projected.symm) charge.2
  let whole := actual_root_relation_consumer observation nontrivial half depth ordinal
  PProd.mk (source, written) (And.intro before (And.intro advanced (And.intro finite whole)))

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
