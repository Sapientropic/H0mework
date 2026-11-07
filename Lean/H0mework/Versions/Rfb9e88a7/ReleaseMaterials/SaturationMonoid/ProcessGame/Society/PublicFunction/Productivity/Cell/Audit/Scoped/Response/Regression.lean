import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Response

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Response
open Institutions.Capitalism.Universal.Source.Program

namespace Regression

def before (cut : Nat) := fastCurrent defaultQuery false cut
def expected (cut : Nat) : Record :=
  (expectedAt defaultQuery false (cut - 1)).getD ⟨cut-1,0,defaultQuery (cut-1),.unauthorized,0,0,0,[]⟩
def objection (cut : Nat) : Objection :=
  ⟨0,cut-1,(before cut).technology,some { expected cut with laborCost := (expected cut).laborCost + 1 }⟩
def actions (cut : Nat) := word (before cut) (expected cut) (objection cut)

theorem actual_source_replacement_is_paid_and_verified :
    (failures (before 5) (actions 5)).isEmpty = true ∧
    actualNetLabor (before 5) (actions 5) = 5 ∧
    (auditLaw.next (before 5) (actions 5)).technology.holder = some 2 ∧
    ¬ auditLaw.Valid (auditLaw.next (before 5) (actions 5)) (Scoped.accessRequest 1 (defaultQuery 4)) := by
  decide +kernel

theorem exhausted_original_source_pays_revoke_and_keeps_refusal :
    (before 20).stock 0 .labor = 0 ∧ (before 20).stock 1 .labor = 1 ∧
    (actions 20).length = 4 ∧
    (Mandate.commandsAt baseLaw scope (before 20) (actions 20)).length = 1 ∧
    (auditLaw.next (before 20) (actions 20)).technology.holder = none ∧
    actualNetLabor (before 20) (actions 20) = 1 ∧
    (failures (before 20) (actions 20)).length = 1 ∧
    (deliveries (before 20) (actions 20) (defaultQuery 20)).isEmpty = true := by
  decide +kernel

theorem expiry_cannot_mint_replacement_authority :
    auditTask.deadline < (before 21).clock ∧
    (auditLaw.next (before 21) (actions 21)).technology.holder = none ∧
    (failures (before 21) (actions 21)).length = 1 ∧
    (deliveries (before 21) (actions 21) (defaultQuery 21)).isEmpty = true := by
  decide +kernel

theorem missing_equal_stale_and_foreign_objections_do_not_revoke :
    word (before 4) (expected 4) { objection 4 with alleged := none } = [] ∧
    word (before 4) (expected 4) { objection 4 with alleged := some (expected 4) } = [] ∧
    word (before 4) (expected 4) { objection 4 with snapshot := { (before 4).technology with version := 0 } } = [] ∧
    word (before 4) (expected 4) { objection 4 with challenger := 3 } = [] := by
  decide +kernel

def actualTests : List (String × Bool) :=
  [("replacement-delivered", (deliveries (before 5) (actions 5) (defaultQuery 4)).length == 1),
   ("replacement-cost-five",actualNetLabor (before 5) (actions 5) == 5),
   ("original-exhausted-revoke-paid",(auditLaw.next (before 20) (actions 20)).technology.holder == none),
   ("original-exhausted-one-labor",actualNetLabor (before 20) (actions 20) == 1),
   ("original-refusal-retained",(failures (before 20) (actions 20)).length == 1),
   ("expired-no-delivery",(deliveries (before 21) (actions 21) (defaultQuery 21)).isEmpty),
   ("incomplete-no-action",(word (before 4) (expected 4) { objection 4 with alleged := none }).isEmpty),
   ("same-record-no-action",(word (before 4) (expected 4) { objection 4 with alleged := some (expected 4) }).isEmpty),
   ("missing-evidence-insufficient",(word (before 5) (expected 5)
      { objection 5 with alleged := some { expected 5 with evidence := [] } }).isEmpty),
   ("missing-fee-rejected",(deliveries (before 5) ((actions 5).take 5) (defaultQuery 4)).isEmpty),
   ("wrong-query-rejected",(deliveries (before 5) (actions 5) ⟨0,0⟩).isEmpty)]

def packets := release (before 5) (actions 5)
def deliveryTests : List (String × Bool) :=
  [("actual-packet-created",packets.length == 1),
   ("actual-packet-verified",packets.all (verify (before 5) (actions 5))),
   ("tampered-payload-refused",packets.all fun packet => !verify (before 5) (actions 5)
      { packet with payload := { packet.payload with evidence := [] } }),
   ("changed-actor-refused",packets.all fun packet => !verify (before 5) (actions 5)
      { packet with payload := { packet.payload with actor := 1 } }),
   ("foreign-row-refused",packets.all fun packet => !verify (before 5) (actions 5)
      { packet with accessIndex := packet.accessIndex + 1 })]

#eval actualTests
#eval deliveryTests

end Regression

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Response
