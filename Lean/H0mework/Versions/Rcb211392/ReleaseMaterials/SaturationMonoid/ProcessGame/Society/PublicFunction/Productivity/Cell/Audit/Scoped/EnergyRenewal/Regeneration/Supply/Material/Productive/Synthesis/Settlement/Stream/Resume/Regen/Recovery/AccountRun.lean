import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.AccountStep
import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Financial.Family Financial.Family.BalanceConservation

private theorem consume_origin_word_key (input : Finance.Input)
    (origins : List (Financial.InstructionOrigin input)) (state : Finance.Account)
    (current : Current) (ordinal : Nat) (actions : List JointAction)
    (sequence : origins.filterMap (Financial.InstructionOrigin.instruction? input) =
      (input.law.execute current ordinal actions).items)
    (paid : ∀ row ∈ (input.law.execute current ordinal actions).items, input.law.Valid row.before row.request)
    (retained : ∀ action ∈ actions, RetainsClaims action)
    (compatible : Compatible Finance.sources input state.current)
    (matched : nativeOwed state = owed current) :
    nativeOwed (consumeOrigins Finance.sources (origins.map (Sigma.mk input)) state) =
      owed (input.law.execute current ordinal actions).final := by
  induction origins generalizing state current ordinal actions with
  | nil =>
    have empty : actions.length = 0 := by
      rw [← input.law.inventory_length current ordinal actions, ← sequence]; rfl
    cases actions with
    | nil => exact matched
    | cons action rest => simp at empty
  | cons origin rest later =>
    cases decoded : origin.instruction? input with
    | none =>
      simp only [List.filterMap_cons, decoded] at sequence
      change nativeOwed (consumeOrigins Finance.sources (rest.map (Sigma.mk input))
        ((consume Finance.sources ⟨input, origin⟩ state).next Finance.sources)) = _
      rw [consume_without_instruction Finance.sources ⟨input, origin⟩ state decoded]
      exact later state current ordinal actions sequence paid retained compatible matched
    | some instruction =>
      cases actions with
      | nil => simp only [List.filterMap_cons, decoded, RawLaw.execute, List.cons_ne_nil] at sequence
      | cons action remaining =>
        have aligned : instruction :: rest.filterMap (Financial.InstructionOrigin.instruction? input) =
            ⟨ordinal, current, action⟩ :: (input.law.execute
              (input.law.step current action) (ordinal + 1) remaining).items := by
          simpa only [List.filterMap_cons, decoded, RawLaw.execute] using sequence
        obtain ⟨same, tail⟩ := List.cons.inj aligned
        simp only [RawLaw.execute] at paid
        have updated := consume_keeps_the_paid_delivery_key input origin state instruction decoded
          (by rw [same]; exact paid _ List.mem_cons_self)
          (by rw [same]; exact retained _ List.mem_cons_self) compatible
          (by rw [same]; exact matched)
        rw [same] at updated
        exact later ((consume Finance.sources ⟨input, origin⟩ state).next Finance.sources)
          (input.law.step current action) (ordinal + 1) remaining tail
          (fun row present => paid row (List.mem_cons_of_mem _ present))
          (fun request present => retained request (List.mem_cons_of_mem _ present))
          (consume_compatible Finance.sources input origin state compatible) updated

namespace Runtime

variable {seed : Seed} {oldRequests : Requests.Source} {permission : Material.Mode} {baseCut : Nat}
  {source : Inherited seed oldRequests permission baseCut}
  {requests : Requests.Source} {authority : Authority} {index : Nat}
  (cut : Cut source requests authority index)

local notation "startAt" => handoff (baseCut := baseCut) index
local notation "prog" => input cut
local notation "permit" => permissionAt seed requests permission (index + 1 + (0 + 1)) (run cut 0)

theorem first_repayment_clears_the_exact_native_key
    (ready : OpeningAt cut)
    (choice : OptionAt seed.basis.origin.scope permit (run cut 0).raw)
    (selected : selection seed permit (run cut 0) = .repay choice) :
    nativeOwed (account cut 0) = 0 := by
  let visit := ProgrammeHistory.visitAt prog (startAt + 0)
  let before := (run cut 0).raw
  let actions := routeWord seed.basis.origin.scope permit before choice.val
  have beforeExact : ProgrammeSource.rawCurrent prog visit.current = before := own_current cut 0
  have actionsExact : ProgrammeSource.rawEvent prog visit.current = actions := by
    change ProgrammeSource.rawEvent prog (ProgrammeHistory.visitAt prog (startAt + 0)).current = _
    rw [selected_word cut 0, admitted_word_when_ready cut ready, word, selected]
  have sequence := Financial.inventoryAt_instructions_exact prog visit
  rw [beforeExact, actionsExact] at sequence
  have result := consume_origin_word_key prog (Financial.inventoryAt prog visit) cut.after.account before 0 actions
    sequence choice.property.2.2.1 choice.property.2.2.2.1 (ready.compatible prog rfl) ready.balance
  exact result.trans choice.property.2.2.2.2

end Runtime
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery
