import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Cofinal
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidDerivedContinuation

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
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidDerivedContinuation

namespace Paid
export RootGeneratedDebtActivationJointSource.OwnerFree (tick_paid_prefix)
end Paid

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "source" => sourceRoot observation nontrivial half depth ordinal
local notation "origin" => sourceCurrent observation nontrivial half depth ordinal
local notation "reader" => sourceReader observation nontrivial half depth ordinal
local notation "frontier" => Calc.originalFrontier observation nontrivial half depth ordinal
variable (index : Fin (frontier).stageCount)

local notation "runtime" => paidRuntime observation nontrivial half depth ordinal index.val
local notation "prior" => (Paid.runtimeCurrent source origin reader runtime).2
local notation "next" => (Paid.runtimeCurrent source origin reader (runtime).tick.next).2
local notation "firstRoot" => RootedAccountedUnfolding.zero (runtime).emittedOccurrence
local notation "nextRoot" => RootedAccountedUnfolding.zero (runtime).tick.next.emittedOccurrence
local notation "paidPrefix" => Paid.tick_paid_prefix source origin reader runtime

/-- The original current and next cochain completions use the limits of their literal stage towers. -/
def actual_paid_cochain_limits (p : Nat.Primes) :
    IsLimit (cochainCompletionCone (ComplexShape.up ℕ) p (paidGroupComplex firstRoot prior)) ×
      IsLimit (cochainCompletionCone (ComplexShape.up ℕ) p (paidGroupComplex nextRoot next)) :=
  ⟨cochainCompletionIsLimit _ p _, cochainCompletionIsLimit _ p _⟩

/-- The original R action and both reverse reads commute with the canonical topology comparisons. -/
theorem actual_paid_cochain_continuation (p : Nat.Primes) (j : Nat) :
    type_of% (continuation_cochain_naturality firstRoot prior nextRoot next paidPrefix (completionFunctorRestriction p j)) ∧
      type_of% (continuation_cochain_naturality firstRoot prior nextRoot next paidPrefix (stageFunctorTransition p j)) ∧
      type_of% (continuation_cochain_naturality firstRoot prior nextRoot next paidPrefix (coimageFunctorRealization p)) ∧
      type_of% (continuation_cochain_from_tower firstRoot prior nextRoot next paidPrefix p) ∧
      type_of% (actual_paid_derived_continuation observation nontrivial half depth ordinal index) :=
  ⟨continuation_cochain_naturality firstRoot prior nextRoot next paidPrefix (completionFunctorRestriction p j),
    continuation_cochain_naturality firstRoot prior nextRoot next paidPrefix (stageFunctorTransition p j),
    continuation_cochain_naturality firstRoot prior nextRoot next paidPrefix (coimageFunctorRealization p),
    continuation_cochain_from_tower firstRoot prior nextRoot next paidPrefix p,
    actual_paid_derived_continuation observation nontrivial half depth ordinal index⟩

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
