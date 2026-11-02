import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source.Legacy
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

/-- Sum actual principal retirements over every closing slot bearing this
original source. The finite support is the account's existing slot list. -/
def receivedForOrigin
    {first last : ResponsibilityState (Epoch.Finance.vocabulary input depth count)}
    (run : (Epoch.Finance.process input depth count).Run first last)
    (origin : Epoch.Finance.Origin input depth count) : ℚ := by
  classical
  exact ∑ index ∈ Finset.range last.slots.length,
    if (last.slots[index]?.map (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)) = some origin
    then receivedAlong input depth count run index else 0

private theorem unique_keys_determine_the_same_slot
    (state : ResponsibilityState (Epoch.Finance.vocabulary input depth count))
    (unique : (state.slots.map (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)).Nodup)
    (first second : Nat) (origin : Epoch.Finance.Origin input depth count)
    (readFirst : (state.slots[first]?.map (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)) = some origin)
    (readSecond : (state.slots[second]?.map (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)) = some origin) :
    first = second := by
  rw [← List.getElem?_map] at readFirst readSecond
  obtain ⟨firstInside,firstExact⟩ := List.getElem?_eq_some_iff.mp readFirst
  obtain ⟨secondInside,secondExact⟩ := List.getElem?_eq_some_iff.mp readSecond
  exact unique.getElem_inj_iff.mp (firstExact.trans secondExact.symm)

theorem a_source_unique_account_reads_the_whole_receipt_from_its_original_slot
    {first last : ResponsibilityState (Epoch.Finance.vocabulary input depth count)}
    (run : (Epoch.Finance.process input depth count).Run first last)
    (index : Fin first.slots.length)
    (unique : (last.slots.map (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)).Nodup) :
    receivedForOrigin input depth count run
      ((Epoch.Finance.slotClaim input depth count (first.slots.get index)).origin input depth count) =
        receivedAlong input depth count run index.val := by
  classical
  have keeps := Epoch.Finance.run_retains_all_claims input depth count run
  obtain ⟨tail,retained⟩ := keeps
  have read : (last.slots[index.val]?.map (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)) =
      some ((Epoch.Finance.slotClaim input depth count (first.slots.get index)).origin input depth count) := by
    have claimRead : (last.slots.map (Epoch.Finance.slotClaim input depth count))[index.val]? =
        some (Epoch.Finance.slotClaim input depth count (first.slots.get index)) := by
      rw [← retained,List.getElem?_append_left (by simpa only [List.length_map] using index.isLt)]
      simp only [List.getElem?_map,List.getElem?_eq_getElem index.isLt,Option.map_some,List.get_eq_getElem]
    have projected := congrArg (Option.map (Epoch.Finance.Claim.origin input depth count)) claimRead
    simpa only [List.getElem?_map,Option.map_map,Function.comp_def,Option.map_some] using projected
  have inside : index.val < last.slots.length := by
    have lengthEq := congrArg List.length retained
    simp only [List.length_map,List.length_append] at lengthEq
    omega
  unfold receivedForOrigin
  rw [Finset.sum_eq_single index.val]
  · exact if_pos read
  · intro other _ different
    apply if_neg
    intro same
    exact different (unique_keys_determine_the_same_slot input depth count last unique other index.val _ same read)
  · intro absent
    exact (absent (Finset.mem_range.mpr inside)).elim

/-- Transporter: the owning source must generate uniqueness; arbitrary native
`admit` runs do not have it. The actual-source mouth below supplies it. -/
theorem a_source_unique_account_lifts_the_original_slot_bound
    (account : (Epoch.Finance.process input depth count).GeneratedState)
    {target : ResponsibilityState (Epoch.Finance.vocabulary input depth count)}
    (run : (Epoch.Finance.process input depth count).Run account.current target)
    (index : Fin account.current.slots.length)
    (unique : (target.slots.map (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)).Nodup) :
    receivedForOrigin input depth count run
      ((Epoch.Finance.slotClaim input depth count (account.current.slots.get index)).origin input depth count) ≤
        (Epoch.Finance.slotClaim input depth count (account.current.slots.get index)).quantity input depth count := by
  rw [a_source_unique_account_reads_the_whole_receipt_from_its_original_slot input depth count run index unique]
  exact every_actual_continuation_keeps_the_original_receipt_below_its_source_quantity input depth count account run index

theorem the_actual_source_bounds_the_whole_original_contribution_receipt (cut later : Nat)
    (index : Fin (Epoch.Finance.Legacy.generated input depth count (Financial.accountAt input cut)).current.slots.length) :
    receivedForOrigin input depth count (originalSourceContinuation input depth count cut later)
      ((Epoch.Finance.slotClaim input depth count
        ((Epoch.Finance.Legacy.generated input depth count (Financial.accountAt input cut)).current.slots.get index)).origin input depth count) ≤
      (Epoch.Finance.slotClaim input depth count
        ((Epoch.Finance.Legacy.generated input depth count (Financial.accountAt input cut)).current.slots.get index)).quantity input depth count := by
  exact a_source_unique_account_lifts_the_original_slot_bound input depth count _ _ index
    (the_actual_translated_account_has_one_slot_per_original_source input depth count (cut + later))

theorem an_original_source_contribution_cannot_fund_unbounded_cumulative_receipts (cut : Nat)
    (index : Fin (Epoch.Finance.Legacy.generated input depth count (Financial.accountAt input cut)).current.slots.length)
    (demand : Nat → ℚ) (unbounded : ∀ bound : ℚ,∃ stage,demand stage > bound) :
    ¬ (∀ stage,∃ later,demand stage ≤ receivedForOrigin input depth count
      (originalSourceContinuation input depth count cut later)
      ((Epoch.Finance.slotClaim input depth count
        ((Epoch.Finance.Legacy.generated input depth count (Financial.accountAt input cut)).current.slots.get index)).origin input depth count)) := by
  intro paid
  obtain ⟨stage,above⟩ := unbounded ((Epoch.Finance.slotClaim input depth count
    ((Epoch.Finance.Legacy.generated input depth count (Financial.accountAt input cut)).current.slots.get index)).quantity input depth count)
  obtain ⟨later,enough⟩ := paid stage
  exact (not_le_of_gt above) (enough.trans
    (the_actual_source_bounds_the_whole_original_contribution_receipt input depth count cut later index))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source
