import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (sourceLaw : RawLaw Party Good Port Technology Instrument)
  (before : RawCurrent Party Good Technology Instrument)
  (payer provider : Party) (instrument : Instrument) (purpose : Port) (net : ℚ)

local notation "law" => PublicFunction.physicalLaw sourceLaw

omit [DecidableEq Instrument] in
theorem physical_issue_is_generated_from_the_nonnegative_source_units
    (positive : 0 < sourceLaw.settlementRate instrument) :
    (law).Valid before (issue law payer provider instrument purpose net) := by
  refine ⟨⟨rfl,rfl⟩, fun _ _ => Or.inl rfl, ?_, ?_, ?_, ?_⟩
  · exact quantities_are_nonnegative law instrument net positive
  · simp [RawLaw.debit,issue,NonnegativeBundle]
  · simp [RawLaw.credit,issue,NonnegativeBundle]
  · simp [RawLaw.debit,issue]

theorem physical_resources_generate_the_actual_settlement
    (positive : 0 < sourceLaw.settlementRate instrument)
    (oldDebt : 0 ≤ before.claims instrument (debtor payer provider net) (creditor payer provider net))
    (cash : |net| ≤ before.stock (debtor payer provider net) (sourceLaw.settlementUnit instrument)) :
    (law).Valid (afterIssue law payer provider instrument purpose net before)
      (settle law payer provider instrument purpose net) := by
  have issued := physical_issue_is_generated_from_the_nonnegative_source_units sourceLaw before payer provider instrument purpose net positive
  have nonnegative := quantities_are_nonnegative law instrument net positive
  have exactAmount := the_claim_units_pay_the_exact_material_amount law instrument net positive
  have issueRead := the_first_actual_issue_keeps_material_and_adds_its_exact_claim law before payer provider instrument purpose net issued
  refine ⟨⟨trivial,rfl⟩, fun _ _ => Or.inl rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨nonnegative, ?_, positive⟩
    rw [issueRead.2]
    simp only [ite_true]
    linarith
  · change NonnegativeBundle (Party × Good)
      (locate (debtor payer provider net) [((law).settlementUnit instrument, units law instrument net * (law).settlementRate instrument)])
    rw [exactAmount]
    simp [NonnegativeBundle,locate,abs_nonneg]
  · change NonnegativeBundle (Party × Good)
      (locate (creditor payer provider net) [((law).settlementUnit instrument, units law instrument net * (law).settlementRate instrument)])
    rw [exactAmount]
    simp [NonnegativeBundle,locate,abs_nonneg]
  · intro lot member
    change lot ∈ locate (debtor payer provider net)
      [((law).settlementUnit instrument, units law instrument net * (law).settlementRate instrument)] at member
    simp only [locate,List.map_cons,List.map_nil,List.mem_singleton] at member
    subst lot
    rw [issueRead.1]
    change flowAt (locate (debtor payer provider net)
      [((law).settlementUnit instrument, units law instrument net * (law).settlementRate instrument)])
      (debtor payer provider net) ((law).settlementUnit instrument) ≤ _
    rw [exactAmount]
    simpa [flowAt,locate,amount,PublicFunction.physicalLaw] using cash

theorem sufficient_original_resources_force_the_compiler_paid_branch
    (nonzero : net ≠ 0) (positive : 0 < sourceLaw.settlementRate instrument)
    (oldDebt : 0 ≤ before.claims instrument (debtor payer provider net) (creditor payer provider net))
    (cash : |net| ≤ before.stock (debtor payer provider net) (sourceLaw.settlementUnit instrument)) :
    ∃ issued settled, compile law before payer provider instrument purpose net =
      .paid nonzero positive issued settled := by
  have issued := physical_issue_is_generated_from_the_nonnegative_source_units sourceLaw before payer provider instrument purpose net positive
  have settled := physical_resources_generate_the_actual_settlement sourceLaw before payer provider instrument purpose net positive oldDebt cash
  have actualRate : 0 < (law).settlementRate instrument := positive
  exact ⟨issued,settled,by simp only [compile,dif_neg nonzero,dif_pos actualRate,dif_pos issued,dif_pos settled]⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement
