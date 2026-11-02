import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.AccessEffects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Access

open Institutions.Capitalism.Universal
open Source.Program Source.ProgrammeControl Instances.OpenReplication

private theorem actual_items (n later : Nat) :
    (law n).rawItems (currentAt n true (3 + later)) (execution n true (3 + later)).submitted =
      [⟨0, (state 1 0 0 true).retime (3 + later) (3 + later), personalCopy⟩,
        ⟨1, (state 1 0 ((n : ℚ) + 1) true).retime (3 + later) (3 + later), consume n⟩] := by
  rw [every_later_current, every_later_word]
  simp only [↓reduceIte, RawLaw.rawItems, Replay.items, public_execution, List.map_cons, List.map_nil, Replay.retime]

theorem every_later_public_execution_has_no_complete_capital_relation (n later : Nat) :
    ¬ Nonempty (Kernel.CapitalRelationKernel (law n) (currentAt n true (3 + later))
      (execution n true (3 + later)).submitted) := by
  rintro ⟨kernel⟩
  have necessity := (congrArg (fun items : List (ExecutionItem Bool Bool (Option Bool) Bool Unit) =>
    kernel.proposal.access.necessity.val ∈ items) (actual_items n later)).mp kernel.proposal.access.necessity.property
  simp only [List.mem_cons, List.not_mem_nil, or_false] at necessity
  have required := kernel.checked.1.2.2.2.1
  have recipient : kernel.proposal.access.recipient = true := by
    rcases necessity with produced | consumed
    · simp only [Kernel.AccessProposal.RequiredUsePaid, produced, personalCopy] at required
    · simp only [Kernel.AccessProposal.RequiredUsePaid, consumed, consume] at required
      exact required.1.symm
  have access := (congrArg (fun items : List (ExecutionItem Bool Bool (Option Bool) Bool Unit) =>
    kernel.proposal.access.access.val ∈ items) (actual_items n later)).mp kernel.proposal.access.access.property
  simp only [List.mem_cons, List.not_mem_nil, or_false] at access
  have port := kernel.checked.1.2.1
  have phase := kernel.checked.1.2.2.1
  rcases access with produced | consumed
  · simp [produced, RawLaw.requiredPorts, RawLaw.debit, personalCopy, law, state, RawCurrent.retime, locate] at port
    simp [produced, port, PrivatePhase, law, state, RawCurrent.retime] at phase
  · simp [consumed, RawLaw.requiredPorts, RawLaw.debit, consume, law, locate] at port
    simp [consumed, port, PrivatePhase, law, state, RawCurrent.retime, recipient] at phase

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Access
