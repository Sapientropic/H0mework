import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation

open Institutions.Capitalism.Universal.Source.Program

def transcript (shared : Bool) (ordinal : Nat) :=
  (itemsAt shared ordinal).filterMap fun item => (decode item.request).map fun message =>
    (message.1, message.2, decide (law.Valid item.before item.request))

theorem actual_message_transcript : ∀ shared : Bool,
    ((List.range 25).flatMap fun ordinal => (transcript shared ordinal).map fun entry => (ordinal, entry)) =
      [(12, 1, Command.accept, true), (13, 1, Command.challenge, true),
       (14, 1, Command.challenge, false), (16, 1, Command.challenge, true),
       (18, 1, Command.exit, true), (19, 2, Command.refuse, true), (24, 1, Command.accept, true)] := by
  decide +kernel

theorem actual_standing_transitions : ∀ shared : Bool,
    (frameAt shared 12).register 1 = .available ∧
      (frameAt shared 13).register 1 = .active ∧
      (frameAt shared 14).register 1 = .active ∧
      (frameAt shared 15).register 1 = .active ∧
      (frameAt shared 19).register 1 = .released ∧
      (frameAt shared 20).register 2 = .declined := by
  decide +kernel

theorem authentic_challenge_has_a_real_resource_refusal : ∀ shared : Bool,
    (frameAt shared 14).raw.stock 1 .labor = 0 ∧
      (wordAt shared 14 (frameAt shared 14)).length = 1 ∧
      ¬ law.Valid (frameAt shared 14).raw (request 1 .challenge) ∧
      law.actualDebit (frameAt shared 14).raw (request 1 .challenge) = [] ∧
      law.step (frameAt shared 14).raw (request 1 .challenge) = (frameAt shared 14).raw := by
  intro shared
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals try { cases shared <;> decide +kernel }
  · rw [RawLaw.step, if_neg (by cases shared <;> decide +kernel)]

theorem withdrawn_work_is_physically_available_but_not_emitted : ∀ shared : Bool,
    (frameAt shared 21).register 1 = .released ∧
      (frameAt shared 21).register 2 = .declined ∧
      law.Valid (frameAt shared 21).raw (audit 1) ∧
      (wordAt shared 21 (frameAt shared 21)).isEmpty = true := by
  decide +kernel

theorem withdrawal_does_not_cancel_own_production : ∀ shared : Bool,
    (frameAt shared 22).register 1 = .released ∧
      (wordAt shared 22 (frameAt shared 22)).length = 3 ∧
      (∀ item ∈ itemsAt shared 22, law.Valid item.before item.request) ∧
      (frameAt shared 23).raw.stock 1 .seed = (frameAt shared 22).raw.stock 1 .seed + 2 ∧
      1 ≤ (frameAt shared 23).raw.stock 1 .life ∧ 1 ≤ (frameAt shared 23).raw.stock 1 .spare := by
  decide +kernel

theorem voluntary_return_is_an_actual_paid_choice : ∀ shared : Bool,
    (frameAt shared 24).register 1 = .released ∧
      law.Valid (frameAt shared 24).raw (request 1 .accept) ∧
      (frameAt shared 25).register 1 = .active ∧
      flowAt (law.actualDebit (frameAt shared 24).raw (request 1 .accept)) 1 .labor = 1 := by
  decide +kernel

theorem full_final_inventory_difference : ∀ actor : Fin 6, ∀ good : Good,
    (frameAt true 25).raw.stock actor good = (frameAt false 25).raw.stock actor good +
      if actor.val = 0 ∧ good = .labor then 1 else 0 := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
