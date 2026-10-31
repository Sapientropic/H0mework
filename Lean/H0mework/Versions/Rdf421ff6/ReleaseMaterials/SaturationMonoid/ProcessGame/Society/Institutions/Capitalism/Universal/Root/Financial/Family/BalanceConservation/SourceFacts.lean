import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

/-- A denomination comparison checks the contracts; it supplies no balance or payment. -/
def DenominatedAt (index : Index) (claim : Claim sources) : Prop :=
  (sources index).law.settlementUnit claim.2.instrument = (sources claim.1).law.settlementUnit claim.2.instrument ∧
  (sources index).law.settlementRate claim.2.instrument = (sources claim.1).law.settlementRate claim.2.instrument

def Compatible (index : Index) (state : ResponsibilityState (vocabulary sources)) : Prop :=
  ∀ claim ∈ state.slots.map (slotClaim sources), DenominatedAt sources index claim

omit [DecidableEq Port] in
theorem selected_review_keys {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    {claim : Claim sources} (review : Review sources claim)
    (selected : readReview sources claim origin = some review) :
    claim.2.instrument = movement.instrument ∧ claim.2.debtor = movement.debtor ∧
      review.kind = movement.kind ∧ review.sender = movement.sender ∧
      review.recipient = movement.recipient ∧ review.quantity = movement.quantity := by
  unfold readReview at selected
  rw [emitted] at selected
  repeat' first | split at selected | contradiction
  cases Option.some.inj selected
  simp_all only [Option.some.injEq, and_self]

omit [DecidableEq Port] in
theorem matching_review_exists {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (claim : Claim sources) (sameInstrument : claim.2.instrument = movement.instrument)
    (sameDebtor : claim.2.debtor = movement.debtor) (compatible : DenominatedAt sources origin.1 claim) :
    ∃ review, readReview sources claim origin = some review := by
  unfold readReview
  simp only [emitted, dif_pos sameInstrument.symm, dif_pos sameDebtor.symm,
    dif_pos compatible.1, dif_pos compatible.2]
  exact ⟨_, rfl⟩

theorem consume_compatible (index : Index) (origin : InstructionOrigin (sources index))
    (state : (process sources).GeneratedState) (compatible : Compatible sources index state.current) :
    Compatible sources index ((consume sources ⟨index, origin⟩ state).next sources).current := by
  intro claim member
  rw [consume_exact_claims] at member
  rcases List.mem_append.mp member with old | fresh
  · exact compatible claim old
  · unfold originsClaim? at fresh
    split at fresh
    · rename_i issued exactOrigin selected
      have same : claim = ⟨index, issued⟩ := by simpa only [Option.toList_some, List.mem_singleton] using fresh
      subst claim
      exact ⟨rfl, rfl⟩
    all_goals simp only [Option.toList_none, List.not_mem_nil] at fresh

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation
