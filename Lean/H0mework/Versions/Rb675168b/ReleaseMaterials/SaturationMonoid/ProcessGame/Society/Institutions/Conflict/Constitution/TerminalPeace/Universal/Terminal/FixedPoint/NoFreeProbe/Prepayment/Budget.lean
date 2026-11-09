import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.PaidWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Bid" => ReviewBid Party Good Port Technology Instrument

/-- A charge funded by the publicly fixed production word at the original
reserve. The fee leaves the production floor and some net growth intact. -/
structure BaseBudget (law : Law) (base : Raw) (word : Word) (bid : Bid) : Prop where
  legal : law.Valid (law.execute base 0 word).final
    (reviewRequest bid.payer bid.port bid.expenses)
  nonnegative : ∀ person good, 0 ≤ bid.fee person good
  fits : ∀ person good, bid.fee person good ≤ Balance.gain law base word person good
  surplus : ∃ person good, bid.fee person good < Balance.gain law base word person good

namespace BaseBudget

/-- Testing at the original reserve is equivalent to legality at every
protected reserve. Neither the inquiry nor the current's surplus is an input
to the test. -/
theorem legal_at_base_iff {law : Law} {base : Raw} {word : Word} {bid : Bid}
    (timing : law.TimeIndependent) (reserve : law.ReserveInsensitive)
    (accepted : ∀ (item : ExecutionItem Party Good Port Technology Instrument),
      item ∈ (RawLaw.execute law base 0 word).items → law.Valid item.before item.request) :
    law.Valid (law.execute base 0 word).final (reviewRequest bid.payer bid.port bid.expenses) ↔
      ∀ raw, InReserve base raw →
        law.Valid (law.execute raw 0 word).final (reviewRequest bid.payer bid.port bid.expenses) := by
  constructor
  · intro legal raw safe
    let extra := InReserve.extra base raw
    have moved := RawLaw.execute_addReserve law reserve base extra safe.extra_nonnegative 0 word accepted
    have retimed := law.execute_retime timing (base.addReserve extra) raw.clock raw.round 0 word
    have same := congrArg (fun atRaw => (law.execute atRaw 0 word).final) safe.exact_raw
    change (law.execute raw 0 word).final =
      (law.execute ((base.addReserve extra).retime raw.clock raw.round) 0 word).final at same
    rw [same, retimed, moved.1]
    exact (law.valid_retime timing _ _ _ _).mpr
      (law.valid_addReserve reserve _ extra safe.extra_nonnegative _ legal)
  · intro everywhere
    exact everywhere base ⟨fun _ _ => le_rfl, rfl, rfl⟩

/-- The base test is exact for a nonnegative charge that is legal, leaves
every material position intact, and preserves strict production progress
throughout the reserve. -/
theorem iff_uniform_payment
    {input : ProgrammeSource.Input Party Good Port Technology Instrument}
    {origin base : Raw} {roster : List Party} {quantum : ℚ} {bid : Bid}
    (recipe : Recipe input origin roster base quantum) :
    BaseBudget input.law base recipe.move.word bid ↔
      (∀ person good, 0 ≤ bid.fee person good) ∧
      ∀ (raw : Raw) (safe : InReserve base raw),
        input.law.Valid (input.law.execute raw 0 recipe.move.word).final
          (reviewRequest bid.payer bid.port bid.expenses) ∧
        (∀ person good, raw.stock person good ≤
          (chargeReview (recipe.moveAt raw safe).next bid.fee).stock person good) ∧
        ∃ person good, raw.stock person good <
          (chargeReview (recipe.moveAt raw safe).next bid.fee).stock person good := by
  have legal := legal_at_base_iff (bid := bid) recipe.law.timing recipe.law.reserve
    (fun item listed => (recipe.move.paid.own item listed).valid)
  have fits (raw : Raw) (safe : InReserve base raw) (person : Party) (good : Good) :
      raw.stock person good ≤ (chargeReview (recipe.moveAt raw safe).next bid.fee).stock person good ↔
        bid.fee person good ≤ recipe.gain person good := by
    rw [recipe.review_material raw safe bid.fee]
    constructor <;> intro within <;> linarith only [within]
  constructor
  · intro budget
    refine ⟨budget.nonnegative, fun raw safe => ⟨legal.mp budget.legal raw safe, ?_, ?_⟩⟩
    · intro person good
      exact (fits raw safe person good).mpr (budget.fits person good)
    · exact (recipe.review_progress raw safe bid.fee).mpr budget.surplus
  · rintro ⟨nonnegative, uniform⟩
    have safe : InReserve base base := ⟨fun _ _ => le_rfl, rfl, rfl⟩
    obtain ⟨legal, preserved, progress⟩ := uniform base safe
    exact ⟨legal, nonnegative, fun person good => (fits base safe person good).mp (preserved person good),
      (recipe.review_progress base safe bid.fee).mp progress⟩

variable {Community : Type} [DecidableEq Port] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum

theorem atCurrent {current : State} {bid : Bid}
    (budget : BaseBudget current.programme.law cut.raw current.recipe.move.word bid) :
    ReviewLegal current bid := by
  change current.programme.law.Valid
    (current.programme.law.execute current.physical.raw 0 current.move.word).final
    (reviewRequest bid.payer bid.port bid.expenses)
  rw [current.recipe.moveAt_word current.physical.raw current.reserved]
  exact (legal_at_base_iff current.recipe.law.timing current.recipe.law.reserve
    (fun item listed => (current.recipe.move.paid.own item listed).valid)).mp budget.legal
    current.physical.raw current.reserved

/-- Pay the quoted expense on the original root before evaluating the
protected inquiry. The charge and the production use the same physical write. -/
def write {current : State} {bid : Bid}
    (budget : BaseBudget current.programme.law cut.raw current.recipe.move.word bid)
    (positive : ∃ good, 0 < amount Good bid.expenses good) : PaidReview current bid :=
  writePaidReview current bid budget.atCurrent ⟨budget.nonnegative, budget.fits⟩ budget.surplus positive

end BaseBudget

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
