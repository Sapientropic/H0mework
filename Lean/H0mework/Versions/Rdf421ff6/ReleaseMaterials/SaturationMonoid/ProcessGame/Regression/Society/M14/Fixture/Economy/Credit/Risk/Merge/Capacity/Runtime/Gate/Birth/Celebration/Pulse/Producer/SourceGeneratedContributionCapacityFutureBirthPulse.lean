import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Producer.SourceGeneratedContributionCapacityNewCompatibleFutureBirth
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.AuthorityObserver

/-!
# Finite future-birth frontier and pulse

The frontier is generated on demand from actual new-compatible future-birth
tokens.  Its pulse is only `List.length`; it stores no frontier, root,
occurrence, authority, next, or future schedule.

Two adjacent actual births both have singleton pulse `1`, while their
payment-occurrence authority and compiler-generated next occurrences differ.
The existing `AuthorityKernelPair` therefore proves that pulse cannot
reconstruct occurrence authority or factor the actual next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityFutureBirthPulse

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth
open M14UBIPeriodicActualServiceCapacity

abbrev AnyContributionCapacityFutureBirth
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  Sigma fun index : Nat =>
    SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex index

def contributionCapacityFutureBirthOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AnyContributionCapacityFutureBirth oldVisit sourceIndex :=
  ⟨index,
    sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex index⟩

theorem contributionCapacityFutureBirthOccurrenceAt_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (contributionCapacityFutureBirthOccurrenceAt oldVisit sourceIndex) := by
  intro left right equality
  exact congrArg Sigma.fst equality

/-- Requested finite observation; no completed `Nat → FutureBirth` table is
installed in a source or root. -/
def sourceGeneratedFiniteContributionCapacityFutureBirthFrontier
    (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    List (AnyContributionCapacityFutureBirth oldVisit sourceIndex) :=
  (List.range horizon).map fun offset =>
    contributionCapacityFutureBirthOccurrenceAt oldVisit sourceIndex
      (start + offset)

abbrev ContributionCapacityFutureBirthPulse := Nat

/-- Pure numerical shadow of the already generated finite frontier. -/
def sourceGeneratedContributionCapacityFutureBirthPulse
    (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    ContributionCapacityFutureBirthPulse :=
  (sourceGeneratedFiniteContributionCapacityFutureBirthFrontier oldVisit
    sourceIndex start horizon).length

@[simp] theorem contributionCapacityFutureBirthPulse_eq_horizon
    (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    sourceGeneratedContributionCapacityFutureBirthPulse oldVisit sourceIndex
        start horizon =
      horizon := by
  simp [sourceGeneratedContributionCapacityFutureBirthPulse,
    sourceGeneratedFiniteContributionCapacityFutureBirthFrontier]

theorem mem_contributionCapacityFutureBirthFrontier_iff
    {oldVisit : OldVisit} {sourceIndex start horizon : Nat}
    {birth : AnyContributionCapacityFutureBirth oldVisit sourceIndex} :
    birth ∈ sourceGeneratedFiniteContributionCapacityFutureBirthFrontier
        oldVisit sourceIndex start horizon ↔
      ∃ offset : Nat, offset < horizon ∧
        birth = contributionCapacityFutureBirthOccurrenceAt oldVisit
          sourceIndex (start + offset) := by
  constructor
  · intro membership
    rcases List.mem_map.mp membership with ⟨offset, offsetMem, equality⟩
    exact ⟨offset, List.mem_range.mp offsetMem, equality.symm⟩
  · rintro ⟨offset, offsetLt, rfl⟩
    exact List.mem_map.mpr
      ⟨offset, List.mem_range.mpr offsetLt, rfl⟩

theorem contributionCapacityFutureBirthFrontier_nodup
    (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    (sourceGeneratedFiniteContributionCapacityFutureBirthFrontier oldVisit
      sourceIndex start horizon).Nodup := by
  apply List.nodup_range.map
  intro left right equality
  have index_eq := congrArg Sigma.fst equality
  change start + left = start + right at index_eq
  omega

/-- Type-valued pointwise producer behind cofinal liveness.  It produces one
later actual birth, not a function or completed future table. -/
abbrev SourceGeneratedLaterContributionCapacityFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  Sigma fun later : Nat =>
    PLift (index < later) ×
      SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt
        oldVisit sourceIndex later

def sourceGeneratedLaterContributionCapacityFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedLaterContributionCapacityFutureBirthAt oldVisit
      sourceIndex index :=
  ⟨index + 1, PLift.up (by omega),
    sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex (index + 1)⟩

/-- Source-specific cofinal liveness on the continuing reopening micro-root.
The canonical macro branch later chooses settlement at current three, so this
theorem is deliberately not advertised as cofinality of that cross-root
history.  It generates one later token on demand and installs no schedule. -/
theorem sourceGeneratedContributionCapacityFutureBirth_cofinalOnReopeningRoot
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ∀ index : Nat, ∃ later : Nat, index < later ∧
      Nonempty
        (SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt
          oldVisit sourceIndex later) := by
  intro index
  let generated := sourceGeneratedLaterContributionCapacityFutureBirthAt
    oldVisit sourceIndex index
  exact ⟨generated.1, generated.2.1.down, ⟨generated.2.2⟩⟩

/-! ## Singleton pulse loses actual payment-occurrence authority -/

def contributionCapacityFutureBirthPulseObserver
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AuthorityObserver
      (AnyContributionCapacityFutureBirth oldVisit sourceIndex)
      ContributionCapacityFutureBirthPulse AnyPeriodicActualServiceExit where
  forget := fun birth =>
    sourceGeneratedContributionCapacityFutureBirthPulse oldVisit sourceIndex
      birth.1 1
  authorityK := fun birth =>
    periodicActualServiceExitOccurrenceAt
      (contributionCapacityFutureBirthDepth sourceIndex birth.1)

def adjacentContributionCapacityFutureBirthPulseKernelPair
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AuthorityKernelPair
      (contributionCapacityFutureBirthPulseObserver oldVisit sourceIndex) where
  left := contributionCapacityFutureBirthOccurrenceAt oldVisit sourceIndex
    index
  right := contributionCapacityFutureBirthOccurrenceAt oldVisit sourceIndex
    (index + 1)
  occurrence_ne := by
    intro equality
    have index_eq :=
      contributionCapacityFutureBirthOccurrenceAt_injective oldVisit
        sourceIndex equality
    omega
  visible_eq := by
    simp [contributionCapacityFutureBirthPulseObserver]
  authority_ne := by
    intro equality
    have depth_eq := periodicActualServiceExitOccurrenceAt_injective equality
    change
      contributionCapacityFutureBirthDepth sourceIndex index =
        contributionCapacityFutureBirthDepth sourceIndex (index + 1)
      at depth_eq
    unfold contributionCapacityFutureBirthDepth at depth_eq
    unfold contributionCapacityReopeningDepthAtCurrent at depth_eq
    omega

theorem contributionCapacityFutureBirthPulse_noOccurrenceReconstruction
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ¬ ∃ reconstruct : ContributionCapacityFutureBirthPulse →
        AnyContributionCapacityFutureBirth oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityFutureBirthPulseObserver oldVisit
          sourceIndex).forget :=
  (adjacentContributionCapacityFutureBirthPulseKernelPair oldVisit
    sourceIndex index).noOccurrenceLeftInverse

theorem contributionCapacityFutureBirthPulse_noAuthorityFactorization
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityFutureBirthPulseObserver oldVisit sourceIndex)) :=
  (adjacentContributionCapacityFutureBirthPulseKernelPair oldVisit
    sourceIndex index).noAuthorityFactorization

theorem contributionCapacityFutureBirthPulse_noFaithfulReconstruction
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityFutureBirthPulseObserver oldVisit sourceIndex)) :=
  (adjacentContributionCapacityFutureBirthPulseKernelPair oldVisit
    sourceIndex index).noFaithfulAuthorityReconstruction

/-! ## The same pulse cannot factor compiler-generated next -/

abbrev AnyContributionCapacityFutureBirthNext
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  Sigma fun current : Nat =>
    (contributionCapacityReopeningSource oldVisit sourceIndex
      (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
        oldVisit sourceIndex)).toRootSource.actual.OccurrenceAt current

def contributionCapacityFutureBirthNextAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AnyContributionCapacityFutureBirthNext oldVisit sourceIndex :=
  ⟨index + 2,
    contributionCapacityReopeningEmitted oldVisit sourceIndex
      (M14SourceGeneratedContributionCapacityReopeningRuntimePayment.CanonicalReopeningSourceEventAt
        oldVisit sourceIndex) (index + 2)⟩

theorem contributionCapacityFutureBirthNextAt_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (contributionCapacityFutureBirthNextAt oldVisit sourceIndex) := by
  intro left right equality
  have current_eq := congrArg Sigma.fst equality
  change left + 2 = right + 2 at current_eq
  omega

def contributionCapacityFutureBirthNextPulseObserver
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AuthorityObserver
      (AnyContributionCapacityFutureBirth oldVisit sourceIndex)
      ContributionCapacityFutureBirthPulse
      (AnyContributionCapacityFutureBirthNext oldVisit sourceIndex) where
  forget := fun birth =>
    sourceGeneratedContributionCapacityFutureBirthPulse oldVisit sourceIndex
      birth.1 1
  authorityK := fun birth =>
    contributionCapacityFutureBirthNextAt oldVisit sourceIndex birth.1

def adjacentContributionCapacityFutureBirthNextPulseKernelPair
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AuthorityKernelPair
      (contributionCapacityFutureBirthNextPulseObserver oldVisit
        sourceIndex) where
  left := contributionCapacityFutureBirthOccurrenceAt oldVisit sourceIndex
    index
  right := contributionCapacityFutureBirthOccurrenceAt oldVisit sourceIndex
    (index + 1)
  occurrence_ne := by
    intro equality
    have index_eq :=
      contributionCapacityFutureBirthOccurrenceAt_injective oldVisit
        sourceIndex equality
    omega
  visible_eq := by
    simp [contributionCapacityFutureBirthNextPulseObserver]
  authority_ne := by
    intro equality
    change
      contributionCapacityFutureBirthNextAt oldVisit sourceIndex index =
        contributionCapacityFutureBirthNextAt oldVisit sourceIndex (index + 1)
      at equality
    have index_eq :=
      contributionCapacityFutureBirthNextAt_injective oldVisit sourceIndex
        equality
    omega

theorem contributionCapacityFutureBirthPulse_noNextFactorization
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityFutureBirthNextPulseObserver oldVisit
          sourceIndex)) :=
  (adjacentContributionCapacityFutureBirthNextPulseKernelPair oldVisit
    sourceIndex index).noAuthorityFactorization

set_option linter.unusedVariables false in
theorem barePulse_cannot_retype_asFutureBirth
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  fail_if_success exact
    ((1 : ContributionCapacityFutureBirthPulse) :
      SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
        sourceIndex index)
  trivial

end
end M14SourceGeneratedContributionCapacityFutureBirthPulse
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFutureBirthPulse.contributionCapacityFutureBirthPulse_eq_horizon
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFutureBirthPulse.contributionCapacityFutureBirthFrontier_nodup
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFutureBirthPulse.sourceGeneratedContributionCapacityFutureBirth_cofinalOnReopeningRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFutureBirthPulse.contributionCapacityFutureBirthPulse_noAuthorityFactorization
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFutureBirthPulse.contributionCapacityFutureBirthPulse_noNextFactorization
