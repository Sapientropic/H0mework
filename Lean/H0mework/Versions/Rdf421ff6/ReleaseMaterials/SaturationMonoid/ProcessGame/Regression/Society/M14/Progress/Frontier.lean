import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Pulse.Producer.SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse

/-!
# Strict growth of the generated, paid possibility frontier

The order is inclusion of actual-service authority images of the existing
finite FutureBirth frontier. It remembers exact payment/service/exit occurrences;
its strictness cannot be obtained from a clock or a visible pulse alone.
This is a readout of generated history, not a stock of currently available
options and not a second ledger or a future schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress

noncomputable section

open M14SourceGeneratedContributionMergeActionSource
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse

/-- The existing actual-service authority, including its original payment and
independent exit, read at this exact generated post-root occurrence. -/
def authorityAt (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AnyPeriodicActualServiceExit :=
  periodicActualServiceExitOccurrenceAt
    (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit sourceIndex index)

theorem authorityAt_injective (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective (authorityAt oldVisit sourceIndex) := by
  intro left right equality
  have h := periodicActualServiceExitOccurrenceAt_injective equality
  change contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit sourceIndex left =
    contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit sourceIndex right at h
  unfold contributionCapacityPostSettlementFutureBirthCurrentAt at h
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at h
  omega

/-- No second frontier: this is the existing finite, already generated list. -/
abbrev frontier (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :=
  sourceGeneratedFiniteContributionCapacityPostSettlementFutureBirthFrontier
    oldVisit sourceIndex start horizon

/-- An occurrence-sensitive readout of that list, never a future inventory. -/
def authoritySupport (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    Set AnyPeriodicActualServiceExit :=
  { authority | ∃ birth ∈ frontier oldVisit sourceIndex start horizon,
      authority = authorityAt oldVisit sourceIndex birth.1 }

theorem mem_authoritySupport_iff (oldVisit : OldVisit)
    (sourceIndex start horizon : Nat) (authority : AnyPeriodicActualServiceExit) :
    authority ∈ authoritySupport oldVisit sourceIndex start horizon ↔
      ∃ offset < horizon, authority = authorityAt oldVisit sourceIndex (start + offset) := by
  constructor
  · rintro ⟨birth, hmem, heq⟩
    obtain ⟨offset, hOffset, rfl⟩ := List.mem_map.mp hmem
    exact ⟨offset, List.mem_range.mp hOffset, heq⟩
  · rintro ⟨offset, hlt, heq⟩
    refine ⟨contributionCapacityPostSettlementFutureBirthOccurrenceAt
      oldVisit sourceIndex (start + offset), ?_, heq⟩
    exact List.mem_map.mpr ⟨offset, List.mem_range.mpr hlt, rfl⟩

theorem authoritySupport_mono (oldVisit : OldVisit)
    (sourceIndex start : Nat) {small large : Nat} (h : small ≤ large) :
    authoritySupport oldVisit sourceIndex start small ⊆
      authoritySupport oldVisit sourceIndex start large := by
  intro authority hmem
  obtain ⟨offset, hlt, heq⟩ :=
    (mem_authoritySupport_iff oldVisit sourceIndex start small authority).mp hmem
  exact (mem_authoritySupport_iff oldVisit sourceIndex start large authority).mpr
    ⟨offset, Nat.lt_of_lt_of_le hlt h, heq⟩

/-- Strictness is witnessed by a paid service authority absent from the old
image. Numeric length is a consequence, not the novelty certificate. -/
theorem authoritySupport_strictMono (oldVisit : OldVisit) (sourceIndex start : Nat) :
    StrictMono (authoritySupport oldVisit sourceIndex start) := by
  intro small large hlt
  refine ⟨authoritySupport_mono oldVisit sourceIndex start (Nat.le_of_lt hlt), ?_⟩
  intro reverse
  have inLarge : authorityAt oldVisit sourceIndex (start + small) ∈
      authoritySupport oldVisit sourceIndex start large :=
    (mem_authoritySupport_iff oldVisit sourceIndex start large _).mpr
      ⟨small, hlt, rfl⟩
  obtain ⟨offset, before, equality⟩ :=
    (mem_authoritySupport_iff oldVisit sourceIndex start small _).mp (reverse inLarge)
  have := authorityAt_injective oldVisit sourceIndex equality
  omega

theorem frontier_succ (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    frontier oldVisit sourceIndex start (horizon + 1) =
      frontier oldVisit sourceIndex start horizon ++
        [contributionCapacityPostSettlementFutureBirthOccurrenceAt
          oldVisit sourceIndex (start + horizon)] := by
  simp [frontier, sourceGeneratedFiniteContributionCapacityPostSettlementFutureBirthFrontier,
    List.range_succ, List.map_append]

/-- The authority image really reads the native payment's actual exit. -/
theorem authorityAt_fromNativeWrite (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (authorityAt oldVisit sourceIndex index).2.actualExit =
      Classical.choice
        (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
          oldVisit sourceIndex index).postPayment.write.down := by
  exact Subsingleton.elim _ _

/-- The added witness is absent from the whole old image, not merely
unequal to the immediately previous occurrence. -/
theorem freshAuthority (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    authorityAt oldVisit sourceIndex (start + horizon) ∈
        authoritySupport oldVisit sourceIndex start (horizon + 1) ∧
      authorityAt oldVisit sourceIndex (start + horizon) ∉
        authoritySupport oldVisit sourceIndex start horizon := by
  constructor
  · exact (mem_authoritySupport_iff oldVisit sourceIndex start (horizon + 1) _).mpr
      ⟨horizon, Nat.lt_succ_self horizon, rfl⟩
  · intro hmem
    obtain ⟨offset, hlt, heq⟩ :=
      (mem_authoritySupport_iff oldVisit sourceIndex start horizon _).mp hmem
    have := authorityAt_injective oldVisit sourceIndex heq
    omega

theorem authoritySupport_subset_iff (oldVisit : OldVisit)
    (sourceIndex start small large : Nat) :
    authoritySupport oldVisit sourceIndex start small ⊆
        authoritySupport oldVisit sourceIndex start large ↔ small ≤ large := by
  constructor
  · intro h
    by_contra hn
    exact (authoritySupport_strictMono oldVisit sourceIndex start (Nat.lt_of_not_ge hn)).2 h
  · exact authoritySupport_mono oldVisit sourceIndex start

theorem authoritySupport_strict_iff (oldVisit : OldVisit)
    (sourceIndex start small large : Nat) :
    authoritySupport oldVisit sourceIndex start small ⊂
        authoritySupport oldVisit sourceIndex start large ↔ small < large := by
  constructor
  · rintro ⟨forward, reverse⟩
    have le := (authoritySupport_subset_iff oldVisit sourceIndex start small large).mp forward
    have ne : small ≠ large := by
      intro h
      subst large
      exact reverse (fun _ hx => hx)
    omega
  · exact fun h => authoritySupport_strictMono oldVisit sourceIndex start h

end
end SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress

#print axioms SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.authoritySupport_strictMono
#print axioms SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.authorityAt_fromNativeWrite
#print axioms SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.freshAuthority
