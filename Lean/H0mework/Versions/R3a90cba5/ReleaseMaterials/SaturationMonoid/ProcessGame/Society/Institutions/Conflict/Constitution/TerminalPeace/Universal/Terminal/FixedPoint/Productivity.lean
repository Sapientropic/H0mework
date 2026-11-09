import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Renewal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Continuation
open Runtime.Viability (Move)

variable {Party Good Port Technology Instrument : Type}

local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Material" => Party → Good → ℚ

/-- The opening production reserve is protected coordinatewise. Claims
and technology remain those of the same productive law. -/
structure InReserve (base raw : Raw) : Prop where
  stock : ∀ person good, base.stock person good ≤ raw.stock person good
  claims : raw.claims = base.claims
  technology : raw.technology = base.technology

def InReserve.extra (base raw : Raw) : Material :=
  fun person good => raw.stock person good - base.stock person good

namespace InReserve

variable {base raw : RawCurrent Party Good Technology Instrument}

theorem extra_nonnegative (safe : InReserve base raw) (person : Party) (good : Good) :
    0 ≤ extra base raw person good :=
  sub_nonneg.mpr (safe.stock person good)

theorem exact_raw (safe : InReserve base raw) :
    raw = (base.addReserve (extra base raw)).retime raw.clock raw.round := by
  apply RawCurrent.ext
  · funext person good
    change raw.stock person good = base.stock person good + (raw.stock person good - base.stock person good)
    ring
  · exact safe.claims
  · exact safe.technology
  · rfl
  · rfl

theorem of_extra (extra : Material) (available : ∀ person good, 0 ≤ extra person good)
    (clock : ℚ) (round : Nat) :
    InReserve base ((base.addReserve extra).retime clock round) :=
  ⟨fun p g => le_add_of_nonneg_right (available p g), rfl, rfl⟩

end InReserve

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- A new recipe is checked at the same finite physical base. Its local
laws make the paid word and personal exits available throughout the reserve. -/
structure Recipe (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (origin : Raw) (roster : List Party) (base : Raw) (quantum : ℚ) where
  move : Move input origin roster base
  law : move.AccumulationLaw quantum
  registration : Move.RegistrationOnReserves input base
  positiveGain : ∃ person good, 0 < Balance.gain input.law base move.word person good

namespace Recipe

variable {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin base : RawCurrent Party Good Technology Instrument} {roster : List Party} {quantum : ℚ}
  (recipe : Recipe input origin roster base quantum)

def gain (person : Party) (good : Good) : ℚ :=
  Balance.gain input.law base recipe.move.word person good

theorem gain_nonnegative (person : Party) (good : Good) : 0 ≤ recipe.gain person good :=
  (Balance.checked_productive_period input.law base recipe.move.word recipe.law.accumulating).2 person good

variable (raw : RawCurrent Party Good Technology Instrument) (safe : InReserve base raw)

private def atExtra (extra : Material) (available : ∀ person good, 0 ≤ extra person good)
    (clock : ℚ) (round : Nat) : Move input origin roster ((base.addReserve extra).retime clock round) := by
  have duration := recipe.law.positive.trans_le (recipe.law.duration extra available clock round)
  refine ⟨recipe.move.word, recipe.registration extra available clock round _ recipe.move.registered,
    recipe.move.paid.after_reserve_and_clock recipe.law.timing recipe.law.reserve extra available clock round duration, ?_⟩
  intro person listed
  obtain ⟨word, registered, personal⟩ := recipe.move.personal person listed
  exact ⟨word, recipe.registration extra available clock round word registered,
    personal.after_reserve_and_clock recipe.law.timing recipe.law.reserve extra available clock round duration⟩

/-- This is the registered word that pays at the actual protected current,
with a separately usable word for every original person. -/
def moveAt : Move input origin roster raw :=
  safe.exact_raw.symm ▸ recipe.atExtra (InReserve.extra base raw) safe.extra_nonnegative raw.clock raw.round

private theorem cast_word {before after : Raw} (same : before = after)
    (move : Move input origin roster before) :
    (same ▸ move : Move input origin roster after).word = move.word := by
  cases same
  rfl

theorem moveAt_word : (recipe.moveAt raw safe).word = recipe.move.word :=
  cast_word safe.exact_raw.symm _

theorem next_exact :
    (recipe.moveAt raw safe).next =
      (base.addReserve (fun person good => recipe.gain person good + InReserve.extra base raw person good)).retime
        (raw.clock + max 0 (input.law.duration raw)) (raw.round + 1) := by
  change input.law.next raw (recipe.moveAt raw safe).word = _
  rw [recipe.moveAt_word raw safe]
  have exact := next_of_productive_period input recipe.law.timing recipe.law.reserve base recipe.move.word recipe.gain
    (Balance.checked_productive_period input.law base recipe.move.word recipe.law.accumulating).1
    (fun item listed => (recipe.move.paid.own item listed).valid)
    (InReserve.extra base raw) safe.extra_nonnegative raw.clock raw.round
  rwa [← safe.exact_raw] at exact

theorem next_material (person : Party) (good : Good) :
    (recipe.moveAt raw safe).next.stock person good = raw.stock person good + recipe.gain person good := by
  rw [recipe.next_exact raw safe]
  change base.stock person good + (recipe.gain person good + (raw.stock person good - base.stock person good)) = _
  ring

theorem next_reserved : InReserve base (recipe.moveAt raw safe).next := by
  rw [recipe.next_exact raw safe]
  exact InReserve.of_extra _ (fun p g => add_nonneg (recipe.gain_nonnegative p g) (safe.extra_nonnegative p g)) _ _

theorem next_clock : raw.clock + quantum ≤ (recipe.moveAt raw safe).next.clock := by
  rw [recipe.next_exact raw safe]
  change raw.clock + quantum ≤ raw.clock + max 0 (input.law.duration raw)
  have duration := recipe.law.duration _ safe.extra_nonnegative raw.clock raw.round
  rw [← safe.exact_raw] at duration
  linarith only [duration, le_max_right 0 (input.law.duration raw)]

theorem next_claims : (recipe.moveAt raw safe).next.claims = raw.claims :=
  (recipe.next_reserved raw safe).claims.trans safe.claims.symm

theorem next_technology : (recipe.moveAt raw safe).next.technology = raw.technology :=
  (recipe.next_reserved raw safe).technology.trans safe.technology.symm

end Recipe

/-- Read the physical effect of review charges in their original units. -/
def chargeReview (raw : Raw) (fee : Material) : Raw :=
  raw.addReserve (fun person good => -(fee person good))

variable {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin base : RawCurrent Party Good Technology Instrument} {roster : List Party} {quantum : ℚ}
  (recipe : Recipe input origin roster base quantum)

structure ReviewFits (fee : Material) : Prop where
  nonnegative : ∀ person good, 0 ≤ fee person good
  within : ∀ person good, fee person good ≤ recipe.gain person good

namespace Recipe

variable (raw : RawCurrent Party Good Technology Instrument) (safe : InReserve base raw)
  (fee : Party → Good → ℚ)

theorem review_material (person : Party) (good : Good) :
    (chargeReview (recipe.moveAt raw safe).next fee).stock person good =
      raw.stock person good + (recipe.gain person good - fee person good) := by
  change (recipe.moveAt raw safe).next.stock person good + -(fee person good) = _
  rw [recipe.next_material raw safe]
  ring

theorem review_reserved (funded : ReviewFits recipe fee) :
    InReserve base (chargeReview (recipe.moveAt raw safe).next fee) := by
  refine ⟨?_, (recipe.next_reserved raw safe).claims, (recipe.next_reserved raw safe).technology⟩
  intro person good
  rw [recipe.review_material raw safe fee]
  exact (safe.stock person good).trans (le_add_of_nonneg_right (sub_nonneg.mpr (funded.within person good)))

theorem review_progress :
    (∃ person good, raw.stock person good < (chargeReview (recipe.moveAt raw safe).next fee).stock person good) ↔
      ∃ person good, fee person good < recipe.gain person good := by
  simp only [recipe.review_material raw safe fee, lt_add_iff_pos_right, sub_pos]

end Recipe

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint
