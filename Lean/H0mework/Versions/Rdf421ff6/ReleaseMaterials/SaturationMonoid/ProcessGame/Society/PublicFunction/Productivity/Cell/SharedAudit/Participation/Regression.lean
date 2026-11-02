import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation

open ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.Program

theorem malformed_or_foreign_messages_do_not_decode :
    decode { request 1 .exit with signer := 0 } = none ∧
    decode { request 1 .exit with consents := [0] } = none ∧
    decode { request 1 .exit with gates := [] } = none ∧
    decode { request 1 .exit with purpose := .common } = none ∧
    decode { request 1 .exit with operation := .use 1 [] .contribution } = none := by
  decide +kernel

theorem exit_and_refusal_leave_the_owner_a_real_return_path :
    CanRun .released .accept ∧ CanRun .declined .accept ∧
      ¬ CanRun .released .challenge ∧ ¬ CanRun .declined .exit := by
  decide +kernel

theorem actual_commands_have_no_free_success (shared : Bool) :
    flowAt (law.actualDebit (frameAt shared 12).raw (request 1 .accept)) 1 .labor = 1 ∧
      flowAt (law.actualDebit (frameAt shared 13).raw (request 1 .challenge)) 1 .labor = 2 ∧
      law.actualDebit (frameAt shared 14).raw (request 1 .challenge) = [] ∧
      flowAt (law.actualDebit (frameAt shared 18).raw (request 1 .exit)) 1 .labor = 1 ∧
      flowAt (law.actualDebit (frameAt shared 19).raw (request 2 .refuse)) 2 .labor = 1 ∧
      flowAt (law.actualDebit (frameAt shared 24).raw (request 1 .accept)) 1 .labor = 1 := by
  cases shared <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
