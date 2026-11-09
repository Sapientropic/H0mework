import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Entry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal

open Reparation.Actual (ReceiptAnswers Script)
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {answers : ReceiptAnswers seed}
  {registered : Script Party Good Port Technology Instrument → Prop}
  {offers : ProductionMenu Party Good Port Technology Instrument}
  (word : Script Party Good Port Technology Instrument) (menus : Runtime.Menus Party Good Port Technology Instrument)
  (choice : ProductionChoice offers := none)

local notation "Prior" => Occurrence.reached answers loss word
local notation "Programme" => productionInput seed loss word choice
local notation "Origin" => originalRaw loss
local notation "People" => productionRoster seed loss word choice

inductive ObstructedHistory where
  | refusedProduction (index : Fin offers.proposals.length) (person : Party)
      (proposed : choice = some index)
      (standing : person ∈ productionRoster seed loss word (some index))
      (declined : offers.replies (Occurrence.history loss ++ word) index person = false)
  | otherFirstWord (first : Capitalism.Universal.Source.Program.RawEvent Party Good Port Technology Instrument)
      (missing : ¬ ProductionStartsWith choice first)
  | nativePending (pending : ¬ Ready (endAt seed (Occurrence.history loss ++ word)))
  | reviewClosed (closed : ¬ ReviewAvailable (endAt seed (Occurrence.history loss ++ word)))
  | firstRefusal (visit : Nat) (issue : Runtime.FaultAt Prior Programme Origin People menus visit)
      (earlier : ∀ n < visit, Runtime.ReadyAt Prior Programme Origin People menus n)
  | bounded (bound : ℚ) (clock : ∀ n, Runtime.clockAt Prior Programme Origin People menus n ≤ bound)
      (ready : ∀ n, Runtime.ReadyAt Prior Programme Origin People menus n)

/-- The global obstruction is discharged on each actual registered
schedule by that history's own first refusal or its physical clock bound. -/
def explainEveryBlockedSchedule
    (unavailable : ¬ Nonempty (Realization loss answers registered word offers))
    (allowed : Occurrence.Unbounded.Allowed answers loss registered word)
    (native : Runtime.RegisteredRun Prior Programme Origin People menus) :
    ObstructedHistory (loss := loss) (answers := answers) word menus choice := by
  classical
  by_cases approved : ProductionApproved seed loss word choice
  · exact explainApproved approved
  · cases choice with
    | none => exact (approved trivial).elim
    | some i =>
      let person := Classical.choose (not_forall.mp approved)
      have refused := Classical.not_imp.mp (Classical.choose_spec (not_forall.mp approved))
      exact .refusedProduction i person rfl refused.1 (Bool.eq_false_of_not_eq_true refused.2)
where
  explainApproved (approved : ProductionApproved seed loss word choice) :
      ObstructedHistory (loss := loss) (answers := answers) word menus choice := by
    classical
    let cut := endAt seed (Occurrence.history loss ++ word)
    by_cases quiet : Ready cut
    · by_cases review : ReviewAvailable cut
      · cases Runtime.classify Prior Programme Origin People menus with
        | firstRefusal visit issue earlier => exact .firstRefusal visit issue earlier
        | bounded ready bound clock => exact .bounded bound clock ready
        | live ready clock =>
        let trajectory := Runtime.trajectoryOfActualRoot Prior Programme Origin People menus native ready clock
        by_cases pilot : ProductionStartsWith choice (trajectory.move 0).word
        · exact (unavailable ⟨⟨allowed, ⟨quiet, review⟩, choice, approved, trajectory, pilot⟩⟩).elim
        · exact .otherFirstWord (trajectory.move 0).word pilot
      · exact .reviewClosed review
    · exact .nativePending quiet

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal
