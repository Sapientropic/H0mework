import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Run
import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Original

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open NoFreeProbe
open OriginalScopes OriginalOrders
open private submit first first_novel first_exit_observed replies wrong_unpaid
  from H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Consumers.Original

deriving instance DecidableEq for Operation, Request

noncomputable section

private abbrev original := Runtime.Original.initial
private abbrev Act := OpenPeace.Input Bool Bool Bool Unit Unit

private def openingReader : Reader original :=
  Reader.start original rfl

private def firstCode : Advice original (submit 0) :=
  .attempts (fun _ => [])

private theorem checked_first :
    ∃ step exactStep readNext,
      Decision.advance registration replies original (submit 0) openingReader firstCode [exitEffect] =
        .committed step exactStep readNext ∧ step.write.isSome = true := by
  let claim : Claim Bool Bool Bool Unit Unit := ([true], TerminalPeace.Supply.personalWord true)
  have empty : original.base.language.covered = ∅ :=
    Language.covered_initial
  refine advance_follows_a_material_witness registration replies original (submit 0)
    openingReader firstCode [exitEffect] claim ?_ first_exit_observed ?_
  · exact List.mem_append_right _ List.mem_cons_self
  · rw [empty]
    exact fun impossible => impossible

/-- The executable word test spends no separate material action. Its
accepted certificate selects the exact original paid U8 write. -/
theorem the_paid_original_word_generates_a_checked_first_write :
    ∃ step exactStep readNext,
      Decision.advance registration replies original (submit 0) openingReader firstCode [exitEffect] =
        .committed step exactStep readNext ∧
      step.next.current.ledger = (Runtime.languageWrite registration replies original (submit 0) first_novel).state ∧
      step.write.isSome = true := by
  obtain ⟨step, same, next, accepted, written⟩ := checked_first
  refine ⟨step, same, next, accepted, ?_, written⟩
  rw [same]
  exact Runtime.next_ledger registration replies original (submit 0) first_novel

/-- False material and protected-term submissions cannot enter the
certificate checker as paid at the next original resident. -/
theorem the_checked_wrong_signer_erases_before_any_scope_read :
    ∃ reader : Reader first.next, ∃ step exactStep readNext,
      Decision.advance registration replies first.next (.proposal (wrongSigner 1)) reader
          (Advice.raw first.next (.proposal (wrongSigner 1))) [exitEffect, termsEffect] =
        .committed step exactStep readNext ∧ step.write = none := by
  obtain ⟨_, same, readNext, _, _⟩ := checked_first
  rw [same] at readNext
  let reader : Reader first.next := readNext
  obtain ⟨step, exactStep, next, executed, noWrite, _⟩ := unpaid_is_committed
    registration replies first.next (.proposal (wrongSigner 1)) reader
    (Advice.raw first.next (.proposal (wrongSigner 1))) [exitEffect, termsEffect] wrong_unpaid
  exact ⟨reader, step, exactStep, next, executed, noWrite⟩

end

run_cmd Lean.modifyEnv fun env =>
  let names := ["the_paid_original_word_generates_a_checked_first_write",
    "the_checked_wrong_signer_erases_before_any_scope_read"]
  names.foldl (fun env name => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name) env

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Original
