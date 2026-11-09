import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Cost.Physical
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Runtime.Native Party Good Port Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (payer : Party) (port : Port) (goods : Bundle Good)

theorem charged_weighted_loss
    (legal : input.law.Valid (reviewItem input before.raw word payer port goods).before (reviewRequest payer port goods))
    (good : Good) (weight : ℚ) (valuable : 0 < weight)
    (actuallyDebited : 0 < amount Good goods good) :
    weight * ((afterCharge input before.raw word payer port goods).stock payer good -
      (input.law.next before.raw word).stock payer good) = -(weight * amount Good goods good) ∧
    weight * ((afterCharge input before.raw word payer port goods).stock payer good -
      (input.law.next before.raw word).stock payer good) < 0 := by
  rw [afterCharge_stock legal, if_pos rfl, sub_sub_cancel_left]
  exact ⟨mul_neg _ _, mul_neg_of_pos_of_neg valuable (neg_neg_of_pos actuallyDebited)⟩

theorem charged_weighted_portfolio
    (legal : input.law.Valid (reviewItem input before.raw word payer port goods).before (reviewRequest payer port goods))
    (observed : Finset Good) (weight : Good → ℚ) :
    (∑ good ∈ observed, weight good * ((afterCharge input before.raw word payer port goods).stock payer good -
      (input.law.next before.raw word).stock payer good)) =
    -(∑ good ∈ observed, weight good * amount Good goods good) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro good _
  rw [afterCharge_stock legal, if_pos rfl, sub_sub_cancel_left, mul_neg]

theorem a_positive_paid_lot_makes_every_positive_weighted_portfolio_strictly_worse
    (legal : input.law.Valid (reviewItem input before.raw word payer port goods).before (reviewRequest payer port goods))
    (observed : Finset Good) (weight : Good → ℚ) (valuable : ∀ good ∈ observed, 0 < weight good)
    (actual : ∃ good ∈ observed, 0 < amount Good goods good) :
    (∑ good ∈ observed, weight good * ((afterCharge input before.raw word payer port goods).stock payer good -
      (input.law.next before.raw word).stock payer good)) < 0 := by
  rw [charged_weighted_portfolio input before word payer port goods legal]
  apply neg_lt_zero.mpr
  apply Finset.sum_pos'
  · intro good listed
    exact mul_nonneg (valuable good listed).le (charged_amount_nonnegative legal good)
  · obtain ⟨good, listed, debit⟩ := actual
    exact ⟨good, listed, mul_pos (valuable good listed) debit⟩

end

/-- Disjoint readings of one charge bundle. The sum records their one
actual debit position and introduces no extra stock loss. -/
structure ChargeParts (Good : Type) where
  application : Bundle Good
  review : Bundle Good
  opportunity : Bundle Good

def ChargeParts.bundle {Good : Type} (parts : ChargeParts Good) : Bundle Good :=
  parts.application ++ parts.review ++ parts.opportunity

theorem ChargeParts.amount_bundle {Good : Type} [DecidableEq Good] (parts : ChargeParts Good) (good : Good) :
    amount Good parts.bundle good = amount Good parts.application good + amount Good parts.review good +
      amount Good parts.opportunity good := by
  simp [ChargeParts.bundle, amount, List.sum_append, add_assoc]

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint
