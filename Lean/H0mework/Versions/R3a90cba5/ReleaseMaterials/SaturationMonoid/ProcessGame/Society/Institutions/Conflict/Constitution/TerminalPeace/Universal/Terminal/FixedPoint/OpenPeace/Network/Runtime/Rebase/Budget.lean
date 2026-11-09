import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.BaseBudget

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Continuation
open private review_debit_at from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Cost.Physical

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Prog" => ProgrammeSource.Input Party Good Port Technology Instrument

variable {left right : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin leftBase rightBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  (a : Recipe left origin people leftBase quantum) (b : Recipe right origin people rightBase quantum)
  (law : left.law = right.law) (word : a.move.word = b.move.word)
  (claims : leftBase.claims = rightBase.claims) (technology : leftBase.technology = rightBase.technology)

include law word claims technology in
private theorem same_gain (person : Party) (good : Good) :
    a.gain person good = b.gain person good := by
  let upper : Raw := { leftBase with stock := fun p g => max (leftBase.stock p g) (rightBase.stock p g) }
  have inA : InReserve leftBase upper := ⟨fun _ _ => le_max_left _ _, rfl, rfl⟩
  have inB : InReserve rightBase upper := ⟨fun _ _ => le_max_right _ _, claims, technology⟩
  have first := a.next_material upper inA person good
  have second := b.next_material upper inB person good
  change (left.law.next upper (a.moveAt upper inA).word).stock person good = _ at first
  change (right.law.next upper (b.moveAt upper inB).word).stock person good = _ at second
  rw [a.moveAt_word, law, word] at first
  rw [b.moveAt_word] at second
  exact add_left_cancel (first.symm.trans second)

private theorem final_stock (input : Prog) (base : Raw)
    (recipe : Recipe input origin people base quantum) (person : Party) (good : Good) :
    (input.law.execute base 0 recipe.move.word).final.stock person good = base.stock person good + recipe.gain person good := by
  let safe : InReserve base base := ⟨fun _ _ => le_rfl, rfl, rfl⟩
  have paid := recipe.next_material base safe person good
  change (input.law.execute base 0 (recipe.moveAt base safe).word).final.stock person good = _ at paid
  rwa [recipe.moveAt_word] at paid

private theorem final_structure (input : Prog) (base : Raw)
    (recipe : Recipe input origin people base quantum) :
    let final := (input.law.execute base 0 recipe.move.word).final
    final.claims = base.claims ∧ final.technology = base.technology := by
  let safe : InReserve base base := ⟨fun _ _ => le_rfl, rfl, rfl⟩
  have afterClaims := recipe.next_claims base safe
  have afterTech := recipe.next_technology base safe
  change (input.law.execute base 0 (recipe.moveAt base safe).word).final.claims = _ at afterClaims
  change (input.law.execute base 0 (recipe.moveAt base safe).word).final.technology = _ at afterTech
  rw [recipe.moveAt_word] at afterClaims afterTech
  exact ⟨afterClaims, afterTech⟩

variable (bid : ReviewBid Party Good Port Technology Instrument)

include law word claims technology in
private theorem transport_funding (stock : ∀ p g, 0 ≤ rightBase.stock p g)
    (funded : BaseBudget left.law leftBase a.move.word bid) :
    BaseBudget right.law rightBase b.move.word bid := by
  have fits (p : Party) (g : Good) : bid.fee p g ≤ b.gain p g :=
    (same_gain a b law word claims technology p g) ▸ funded.fits p g
  let first := (left.law.execute leftBase 0 a.move.word).final
  let second := (right.law.execute rightBase 0 b.move.word).final
  have sameClaims : second.claims = first.claims :=
    (final_structure right rightBase b).1.trans (claims.symm.trans (final_structure left leftBase a).1.symm)
  have sameTech : second.technology = first.technology :=
    (final_structure right rightBase b).2.trans (technology.symm.trans (final_structure left leftBase a).2.symm)
  let req : Request Party Good Port Technology Instrument := reviewRequest bid.payer bid.port bid.expenses
  have firstLegal : right.law.Valid first req := law ▸ funded.legal
  let diff := fun p g => second.stock p g - first.stock p g
  have sameRaw : second = (first.addReserve diff).retime second.clock second.round := by
    apply RawCurrent.ext
    · funext p g
      change second.stock p g = first.stock p g + (second.stock p g - first.stock p g)
      ring
    · exact sameClaims
    · exact sameTech
    · rfl
    · rfl
  have allowed : right.law.operationAllowed second req = true := by
    conv => lhs; rw [sameRaw]
    rw [b.law.timing.operationAllowed, b.law.reserve.operationAllowed]
    exact firstLegal.1.2
  have ports : right.law.requiredPorts second req = right.law.requiredPorts first req := by
    simp only [req, RawLaw.requiredPorts, reviewRequest, RawLaw.debit, sameTech]
  refine ⟨⟨⟨firstLegal.1.1, allowed⟩, ?_, firstLegal.2.2.1,
    firstLegal.2.2.2.1, firstLegal.2.2.2.2.1, ?_⟩, funded.nonnegative, fits, ?_⟩
  · intro port listed
    rw [sameTech]
    exact firstLegal.2.1 port (ports ▸ listed)
  · intro item _
    change flowAt (locate bid.payer bid.expenses) item.1.1 item.1.2 ≤ second.stock item.1.1 item.1.2
    rw [review_debit_at, ← show bid.fee item.1.1 item.1.2 =
      (if item.1.1 = bid.payer then amount Good bid.expenses item.1.2 else 0) from rfl]
    exact (fits _ _).trans (by
      change b.gain item.1.1 item.1.2 ≤ (right.law.execute rightBase 0 b.move.word).final.stock item.1.1 item.1.2
      rw [final_stock]
      exact le_add_of_nonneg_left (stock _ _))
  · obtain ⟨p, g, strict⟩ := funded.surplus
    refine ⟨p, g, ?_⟩
    change bid.fee p g < b.gain p g
    rw [← same_gain a b law word claims technology p g]
    exact strict

include law word claims technology in
/-- Installed recipes with the same law and word pay the same bills
across different physical stock floors. Strict progress is calculated at
the shared word, while legal spending is transported to the actual stock. -/
theorem agrees_across_rebased_reserves (leftStock : ∀ p g, 0 ≤ leftBase.stock p g)
    (rightStock : ∀ p g, 0 ≤ rightBase.stock p g) :
    BaseBudget left.law leftBase a.move.word bid ↔ BaseBudget right.law rightBase b.move.word bid :=
  ⟨transport_funding a b law word claims technology bid rightStock,
    transport_funding b a law.symm word.symm claims.symm technology.symm bid leftStock⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.BaseBudget
