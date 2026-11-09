import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Start

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open private inspect Inspection.known commitCovered Reader.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Run
open private selects_ordinary from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Advance

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin reserveBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)
  (before : Runtime.State (seed := seed) (cut := cut) (community := community)
    origin people quantum (reserveBase := reserveBase))

variable (due : NoFreeProbe.Due Party Good Port Technology Instrument)

local notation "Input" => OpenPeace.Input.native due

private theorem known_at_due (read : Reader before) :
    ∃ covered, Inspection.known (inspect home replies before Input read (Advice.raw before Input)) = some covered := by
  unfold inspect
  split <;> exact ⟨_, rfl⟩

/-- Material renewal can always use the finite checker while a paid
request is waiting for a language comparison. -/
theorem native_due_is_committed (read : Reader before) :
    ∃ step same readNext,
      Decision.advance home replies before Input read (Advice.raw before Input) [] =
        .committed step same readNext ∧ step.write = none ∧ step.next.base.language = before.base.language := by
  obtain ⟨known, selected⟩ := known_at_due home replies before due read
  let check := Decidable.isTrue known.down
  let step := Runtime.advanceChecked home replies before Input check
  have same := Runtime.advanceChecked_eq_advance home replies before Input check
  refine ⟨step, same, Reader.mk read.probe read.words, ?_, rfl, rfl⟩
  simp only [Decision.advance, selected, commitCovered]
  rfl

def nativeSchedule (dueAt : Nat → NoFreeProbe.Due Party Good Port Technology Instrument) :
    Policy Party Good Port Technology Instrument :=
  fun n _ _ _ _ => .native (dueAt n)

variable (dueAt : Nat → NoFreeProbe.Due Party Good Port Technology Instrument)

omit [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem native_language (n : Nat) :
    (Runtime.history home replies before (nativeSchedule dueAt) n).1.base.language = before.base.language := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    rw [Runtime.history_succ]
    let now := (Runtime.history home replies before (nativeSchedule dueAt) n).1
    change (Runtime.advance home replies now (.native (dueAt n))).next.base.language = _
    rw [selects_ordinary home replies now (.native (dueAt n)) (Set.empty_subset _)]
    exact earlier

theorem native_wait_is_checked (read : Reader before) (n : Nat) :
    let reached := (Runtime.history home replies before (nativeSchedule dueAt) n).1
    let input := OpenPeace.Input.native (dueAt n)
    ∃ reader step same readNext,
      Decision.advance home replies reached input reader (Advice.raw reached input) [] =
        .committed step same readNext ∧ step.write = none := by
  intro reached input
  let reader : Reader reached := Reader.mk
    (fun point => Checked.map (by rw [native_language home replies before dueAt n]) (read.probe point))
    (fun claim => Checked.map_complete _ (read.words claim))
  obtain ⟨step, same, next, written, noWrite, _⟩ :=
    native_due_is_committed home replies reached (dueAt n) reader
  exact ⟨reader, step, same, next, written, noWrite⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision
