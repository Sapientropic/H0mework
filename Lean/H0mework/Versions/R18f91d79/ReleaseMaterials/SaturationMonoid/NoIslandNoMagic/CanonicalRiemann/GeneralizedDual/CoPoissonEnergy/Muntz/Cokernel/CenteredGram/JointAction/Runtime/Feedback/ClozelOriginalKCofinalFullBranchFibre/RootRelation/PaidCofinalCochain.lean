import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Cofinal
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidDerivedContinuation

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open CategoryTheory CategoryTheory.Limits BurnolPhysicalState SourceOperationScalarInventoryLift
open SourceOperationCompletion SourceGeneratedPrimePowerCompletion

attribute [local instance] relationGroups

open private paidRuntime from
  H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidDerivedContinuation

namespace Paid
export RootGeneratedDebtActivationJointSource.OwnerFree (tick_paid_prefix)
end Paid

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- Both coherent cochain limits and all action comparisons come from the same actual R tick. -/
def actual_paid_cochain_continuation
    (index : Fin (Calc.originalFrontier observation nontrivial half depth ordinal).stageCount)
    (p : Nat.Primes) (j : Nat) :=
  let source := sourceRoot observation nontrivial half depth ordinal
  let origin := sourceCurrent observation nontrivial half depth ordinal
  let reader := sourceReader observation nontrivial half depth ordinal
  let runtime := paidRuntime observation nontrivial half depth ordinal index.val
  let arrived := runtime.tick.next
  let prior := (Paid.runtimeCurrent source origin reader runtime).2
  let next := (Paid.runtimeCurrent source origin reader arrived).2
  let firstRoot := RootedAccountedUnfolding.zero runtime.emittedOccurrence
  let nextRoot := RootedAccountedUnfolding.zero arrived.emittedOccurrence
  let retained := Paid.tick_paid_prefix source origin reader runtime
  let shape := ComplexShape.up ℕ
  let currentLimit := cochainCompletionIsLimit shape p (paidGroupComplex firstRoot prior)
  let nextLimit := cochainCompletionIsLimit shape p (paidGroupComplex nextRoot next)
  let restriction := continuation_cochain_naturality firstRoot prior nextRoot next retained
    (completionFunctorRestriction p j)
  let stage := continuation_cochain_naturality firstRoot prior nextRoot next retained (stageFunctorTransition p j)
  let separated := continuation_cochain_naturality firstRoot prior nextRoot next retained (coimageFunctorRealization p)
  let lifted := continuation_cochain_from_tower firstRoot prior nextRoot next retained p
  let receipt := actual_paid_derived_continuation observation nontrivial half depth ordinal index
  PProd.mk (currentLimit, nextLimit) (And.intro restriction (And.intro stage (And.intro separated (And.intro lifted receipt))))

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
