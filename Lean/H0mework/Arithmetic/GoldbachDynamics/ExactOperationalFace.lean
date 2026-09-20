import H0mework.Arithmetic.Goldbach.ExactUnfolding
import H0mework.Arithmetic.GoldbachDynamics.OperationalDecay

/-!
# Exact-occurrence operational factor-decay face

The arithmetic target unfolding, its factorization, canonical split and every
repair/emission receipt are generated under one caller-inaccessible exact
runtime occurrence index.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer

open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open SourceGeneratedFiniteEffectiveBranchingReachability

universe u

structure RootGeneratedExactOccurrenceOperationalFactorDecayAt
    {Occurrence : Type u} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index) : Type u where
  private mk ::
  occurrence :
    RootedAccountedUnfolding
      (ExactOccurrenceAdditivePointAt rootOccurrence)
  occurrence_eq : occurrence =
    evenTargetOccurrenceAt rootOccurrence index
  targetFold : occurrence.fold
      CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.terminalHistoryAlgebra =
    evenTargetHistory index
  factorization : GeneratedUnitFactorizationAt (evenTargetHistory index)
  factorization_eq : factorization = evenTargetFactorization index
  source : EffectiveSplitAt index
  source_eq : source = canonicalSplit index indexInRange
  occurrenceRoot : occurrence.root.rootOccurrence = rootOccurrence
  channelReceipt : ∀ state : EffectiveSplitAt index,
    (channel : FactorDecayChannelAt state) →
      OperationalFactorDecayChannelReceiptAt channel
  pathReceipt : ∀ {source target : EffectiveSplitAt index},
    (path : GeneratedPathAt (fullFactorDecayLaw index) source target) →
      OperationalFactorDecayPathReceiptAt path

noncomputable def generate
    {Occurrence : Type u} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index) :
    RootGeneratedExactOccurrenceOperationalFactorDecayAt
      rootOccurrence index indexInRange :=
  { occurrence := evenTargetOccurrenceAt rootOccurrence index
    occurrence_eq := rfl
    targetFold := evenTargetHistoryAt_eq rootOccurrence index
    factorization := evenTargetFactorization index
    factorization_eq := rfl
    source := canonicalSplit index indexInRange
    source_eq := rfl
    occurrenceRoot := evenTargetOccurrenceAt_root_is_exact
      rootOccurrence index
    channelReceipt := fun _state channel => generateChannelReceipt channel
    pathReceipt := fun path => generatePathReceipt path }

end CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
