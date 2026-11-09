import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt)

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community] {Observation : Type u}

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {control : RawCurrent Party Good (State Party Technology) Instrument → List Party}

theorem certify_signed_live_exit
    (paid : PaidVisit seed community anchor) (answers : OwnerAnswers seed) (word : Word)
    (live : MandateExit.LiveCertificate seed anchor paid.history community base scope control word)
    (signed : Exit.SignersChose answers paid.history word) :
    Certified paid answers word :=
  ⟨of_owned_word seed community anchor answers control paid.history word
    live.1.1.original_authority live.1.1.own signed (fun item listed => (live.1.2 item listed).2),
    live.2, live.1.1.standing⟩

theorem the_signed_exit_reopens_the_exact_paid_visit
    (paid : PaidVisit seed community anchor) (answers : OwnerAnswers seed) (word : Word)
    (live : MandateExit.LiveCertificate seed anchor paid.history community base scope control word)
    (signed : Exit.SignersChose answers paid.history word) :
    ∃ next : GuardedVisit base scope seed community anchor control,
      resume base scope control paid word = .inr next ∧ paidView next = paid ∧
      ∃ chosen : MandateExit.Chosen next answers, chosen.word = word := by
  obtain ⟨checked, available⟩ := MandateExit.a_paid_nominated_word_supplies_the_checked_continuation
    seed anchor paid.history community base scope control word paid.continues live
  unfold MandateExit.finiteProbe at available
  unfold resume
  cases inspected : MandateExit.inspectPlan seed anchor paid.history community base scope control word with
  | inl issue =>
    rw [inspected] at available
    cases available
  | inr ready =>
    exact ⟨_, rfl, rfl, ⟨word, live, signed⟩, rfl⟩

/-- A renewable supply yields the signed next exit at the actual end
of each guarded rival block. Reopening retains the full paid state. -/
theorem a_local_independent_supply_reopens_the_original_exit_under_every_rival
    (policy : Cofinal.ObservationPolicy Party Good Port M Instrument Observation)
    (answers : OwnerAnswers seed) (opening : PaidVisit seed community anchor)
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed opening.history).raw)
    (person : Party) (exposed : person ∈ bearers seed community anchor)
    (minimum : Good → ℚ) (quantum : ℚ) (positive : 0 < quantum)
    (exitAt : ∀ paid : PaidVisit seed community anchor,
      Cofinal.StockReserve person minimum (endAt seed paid.history) →
        MandateExit.LiveCertificate seed anchor paid.history community base scope control
          (Cofinal.candidate policy paid) ∧ Exit.SignersChose answers paid.history (Cofinal.candidate policy paid))
    (replenishes : ∀ paid : PaidVisit seed community anchor,
      Cofinal.StockReserve person minimum (endAt seed paid.history) →
        Cofinal.StockReserve person minimum (endAt seed (paid.history ++ Cofinal.candidate policy paid)))
    (gains : ∀ paid : PaidVisit seed community anchor,
      Cofinal.StockReserve person minimum (endAt seed paid.history) →
        (endAt seed paid.history).raw.clock + quantum ≤
          (endAt seed (paid.history ++ Cofinal.candidate policy paid)).raw.clock)
    (initial : Cofinal.StockReserve person minimum (endAt seed opening.history))
    (count : Nat → Word → Nat) (choose : Nat → Nat → Word → Input) :
    let rival : Cofinal.RivalPolicy Party Good Port M Instrument := ⟨person, count, choose⟩
    Cofinal.CofinalRun policy answers (some rival) opening ∧
      ∀ round,
        let paid := Cofinal.runAgainst policy answers (some rival) opening round
        Civil.Mandate.Released (endAt seed paid.history).raw ∧
          (∀ loss ∈ Reparation.Actual.originalLosses seed community paid.history,
            ∃ balance row, paid.state.read row = .inr (loss, balance)) ∧
          ∃ next : GuardedVisit base scope seed community anchor control,
            resume base scope control paid (Cofinal.candidate policy paid) = .inr next ∧ paidView next = paid ∧
            ∃ chosen : MandateExit.Chosen next answers, chosen.word = Cofinal.candidate policy paid := by
  let rival : Cofinal.RivalPolicy Party Good Port M Instrument := ⟨person, count, choose⟩
  have supply : Cofinal.LocalSupply (community := community) (anchor := anchor) policy answers
      (Cofinal.StockReserve person minimum) quantum := by
    refine ⟨fun paid enough => ?_, replenishes, gains⟩
    obtain ⟨live, signed⟩ := exitAt paid enough
    exact certify_signed_live_exit paid answers (Cofinal.candidate policy paid) live signed
  obtain ⟨cofinal, retained⟩ := Cofinal.an_independent_renewing_stock_forces_paid_cofinal_peace
    (policy := policy) (answers := answers) (opening := opening)
    installed released person exposed minimum quantum positive supply initial count choose
  have named (other : Cofinal.RivalPolicy Party Good Port M Instrument) (same : some rival = some other) :
      other.refuser = person := by rw [← Option.some.inj same]
  have supplied := Cofinal.every_round_retains_the_local_supply policy answers (some rival) opening
    (Cofinal.StockReserve person minimum) quantum supply initial
    (Cofinal.a_guarded_rival_preserves_the_named_stock_reserve answers (some rival) person minimum exposed named)
  refine ⟨cofinal, fun round => ⟨(retained round).1, (retained round).2, ?_⟩⟩
  let paid := Cofinal.runAgainst policy answers (some rival) opening round
  obtain ⟨live, signed⟩ := exitAt paid (supplied round)
  exact the_signed_exit_reopens_the_exact_paid_visit paid answers (Cofinal.candidate policy paid) live signed

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
