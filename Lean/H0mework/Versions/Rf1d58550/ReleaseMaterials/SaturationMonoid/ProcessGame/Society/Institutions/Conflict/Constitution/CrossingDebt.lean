import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Aggression
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Coverage
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Discharge

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

variable {source : Root.Cut Party Good Port Technology Instrument}
  {word : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community}

abbrev debtAddress (attack : Boundary.AggressionAt source word community) : Reparation.Key Party Good :=
  (attack.victim, attack.attacker, attack.good)

theorem the_assessed_debt_includes_the_exact_m11_debit
    (attack : Boundary.AggressionAt source word community) :
    attack.quantity ≤ Reparation.gross source word community (debtAddress attack) := by
  have forced : Reparation.Coercive community attack.item (debtAddress attack) :=
    ⟨attack.foreign.symm, rfl, fun signed => attack.unassented (Or.inr signed)⟩
  have exactLoss : Reparation.loss source.native.input.law community attack.item (debtAddress attack) =
      attack.quantity := by
    rw [Reparation.loss, if_pos forced]
    exact max_eq_right attack.original.2.2.le
  rw [← exactLoss]
  exact Reparation.loss_le_gross_of_mem source word community _ attack.item attack.original.1

/-- The reparation compiler is applied to the same paid M11 occurrence
and never asks for a new signature from the aggressor to assess the debt. -/
theorem claimFor (attack : Boundary.AggressionAt source word community) :
    Reparation.ClaimAt source word community (debtAddress attack) :=
  ((Reparation.assess source word community attack.paid (debtAddress attack)).get (by
    have positive := attack.original.2.2.trans_le (the_assessed_debt_includes_the_exact_m11_debit attack)
    simp only [Reparation.assess, dif_pos positive, Option.isSome_some])).down

theorem every_aggression_address_is_in_the_original_reparation_assessment
    (attack : Boundary.AggressionAt source word community) :
    ∃ assessed ∈ Reparation.claims source word community attack.paid, assessed.val = debtAddress attack :=
  Reparation.every_positive_address_is_assessed source word community attack.paid (claimFor attack).positive

theorem assessed_address_iff_original_aggression
    (key : Reparation.Key Party Good) :
    Reparation.ClaimAt source word community key ↔
      ∃ attack : Boundary.AggressionAt source word community, debtAddress attack = key := by
  constructor
  · intro claim
    obtain ⟨item, original, positive⟩ := claim.has_original_loss
    obtain ⟨coercive, valid, _⟩ := Reparation.positive_loss_is_an_actual_foreign_debit _ _ _ _ positive
    have foreign : community item.request.signer ≠ community key.1 := by
      rw [coercive.2.1]
      exact coercive.1.symm
    let debit : Boundary.Row Party Good Port Technology Instrument := (item, key.1, key.2.2)
    have net : 0 < Boundary.loss source.native.input.law debit := by
      rw [Reparation.loss, if_pos coercive, lt_max_iff] at positive
      exact positive.resolve_left (lt_irrefl _)
    obtain ⟨certificate, belongs, read⟩ := Boundary.boundary_from_original_positive_loss
      source.native.input.law (source.raw, word) community debit original valid net foreign
    let attack := Boundary.AggressionAt.ofPaidBoundary claim.paid certificate belongs
    refine ⟨attack, ?_⟩
    have row : attack.row = debit := read
    change (attack.row.2.1, attack.row.1.request.signer, attack.row.2.2) = key
    rw [row]
    exact Prod.ext rfl (Prod.ext coercive.2.1 rfl)
  · rintro ⟨attack, rfl⟩
    exact claimFor attack

theorem a_unilateral_carry_leaves_the_original_crossing_loss_due
    (attack : Boundary.AggressionAt source word community)
    (tail : RawEvent Party Good Port Technology Instrument)
    (unilateral : ∀ request ∈ tail, community request.signer = community attack.attacker) :
    attack.quantity ≤ Reparation.remaining source word tail community (debtAddress attack) := by
  rw [Reparation.unilateral_carry_keeps_the_entire_original_debt (claimFor attack) tail unilateral]
  exact the_assessed_debt_includes_the_exact_m11_debit attack

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution
