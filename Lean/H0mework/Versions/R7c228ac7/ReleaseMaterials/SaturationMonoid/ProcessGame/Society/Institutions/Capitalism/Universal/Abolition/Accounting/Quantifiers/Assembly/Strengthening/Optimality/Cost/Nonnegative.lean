import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Channels

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (law : RawLaw Party Good Port Technology Instrument)
  (before : RawCurrent Party Good Technology Instrument)
  (request : Request Party Good Port Technology Instrument) (channel : Channel)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem part_is_within_the_original_source_debit (entry : (Party × Good) × ℚ)
    (listed : entry ∈ part law before request channel) : entry ∈ law.debit before request := by
  cases operation : request.operation with
  | produce operator =>
      simp only [part,operation] at listed
      simp only [RawLaw.debit,operation,locate,List.map_append]
      by_cases inputPart : channel = .productionInput
      · rw [if_pos inputPart] at listed
        exact List.mem_append_left _ listed
      · rw [if_neg inputPart] at listed
        by_cases maintenancePart : channel = .productionMaintenance
        · rw [if_pos maintenancePart] at listed
          exact List.mem_append_right _ listed
        · rw [if_neg maintenancePart] at listed
          cases listed
  | use bearer goods purpose =>
      simp only [part,operation] at listed
      split at listed
      · exact listed
      · cases listed
  | revise operator technology =>
      simp only [part,operation] at listed
      split at listed
      · exact listed
      · cases listed
  | transfer sender recipient goods =>
      simp only [part,operation] at listed
      cases listed
  | issue instrument issuer holder quantity =>
      simp only [part,operation] at listed
      cases listed
  | assign instrument issuer sender holder quantity =>
      simp only [part,operation] at listed
      cases listed
  | settle instrument debtor holder quantity =>
      simp only [part,operation] at listed
      cases listed
  | present =>
      simp only [part,operation] at listed
      cases listed

omit [DecidableEq Instrument] in
theorem actualPart_is_the_original_nonnegative_flow :
    NonnegativeBundle (Party × Good) (actualPart law before request channel) := by
  by_cases accepted : law.Valid before request
  · rw [actualPart,if_pos accepted]
    exact fun entry listed => accepted.2.2.2.1 entry
      (part_is_within_the_original_source_debit law before request channel entry listed)
  · simp [actualPart,accepted,NonnegativeBundle]

omit [DecidableEq Instrument] in
theorem actualPart_nonnegative (party : Party) (good : Good) :
    0 ≤ flowAt (actualPart law before request channel) party good := by
  by_cases accepted : law.Valid before request
  · rw [actualPart,if_pos accepted]
    apply amount_nonnegative
      (part law before request channel) (fun entry listed =>
        accepted.2.2.2.1 entry (part_is_within_the_original_source_debit law before request channel entry listed)) (party,good)
  · simp [actualPart,accepted,flowAt,amount]

omit [DecidableEq Instrument] in
theorem a_settlement_does_not_destroy_real_resources
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (settlement : request.operation = .settle instrument debtor holder quantity) :
    actualPart law before request channel = [] := by
  simp [actualPart,part,settlement]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
