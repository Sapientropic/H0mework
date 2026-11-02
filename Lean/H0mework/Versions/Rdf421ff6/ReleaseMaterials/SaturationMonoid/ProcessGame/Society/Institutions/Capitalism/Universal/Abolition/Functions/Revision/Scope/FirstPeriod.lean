import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Scope.Resign
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Result

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Scope

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Abolition.Root.Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (word : RawEvent Party Good Port Technology Instrument)
  (phase : before.phase = .renewal word)
  (checked : ∀ item ∈ input.law.rawItems before.raw word, input.law.Valid item.before item.request)

omit [DecidableEq Port] in
include phase checked in
theorem the_source_renewal_is_actually_accepted_without_old_consents :
    ∃ selected lawful, Physical.Public.compile input before .advance =
      .accepted (word.map (fun request => request.resign request.signer)) selected lawful := by
  have normalized := the_checked_source_word_is_its_direct_public_resign input.law before.raw word checked
  have legal := Replay.every_replay_item_is_lawful_and_has_no_controller_consents input.law before.raw 0 word
  rw [normalized] at legal
  cases produced : Physical.Public.compile input before .advance with
  | accepted actual selected lawful =>
      have same : word.map (fun request => request.resign request.signer) = actual := by
        simpa only [Physical.Public.wordAt, phase, Option.some.injEq] using selected
      cases same
      exact ⟨selected, lawful, rfl⟩
  | refused actual selected item listed failed =>
      have same : word.map (fun request => request.resign request.signer) = actual := by
        simpa only [Physical.Public.wordAt, phase, Option.some.injEq] using selected
      exact (failed ((legal item (same.symm ▸ listed)).1)).elim
  | metadata absent => simp only [Physical.Public.wordAt, phase, reduceCtorEq] at absent

omit [DecidableEq Port] in
include checked in
theorem the_public_renewal_keeps_every_original_necessity_and_maintenance_payment
    (members : List Party) :
    Exit.Necessity.AllNeedsPaid (PublicFunction.physicalLaw input.law) before.raw members
        (word.map (fun request => request.resign request.signer)) ↔
      Exit.Necessity.AllNeedsPaid input.law before.raw members word := by
  rw [← the_checked_source_word_is_its_direct_public_resign input.law before.raw word checked]
  exact Replay.every_original_livelihood_and_maintenance_requirement_is_preserved input.law before.raw word members

#print axioms the_source_renewal_is_actually_accepted_without_old_consents
#print axioms the_public_renewal_keeps_every_original_necessity_and_maintenance_payment

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Scope
