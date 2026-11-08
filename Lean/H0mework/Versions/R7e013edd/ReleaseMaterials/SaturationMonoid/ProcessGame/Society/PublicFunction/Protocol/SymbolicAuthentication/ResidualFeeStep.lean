import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualFeeLaw

set_option autoImplicit false
set_option maxRecDepth 10000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualFeeStep
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code start protocols resources)
open Repayment.Recovery (Good)

abbrev Memory := Fin code.sites → Fin code.signals
def localDue (memory : Memory) : Nat := (4 - (memory 0).val) + (4 - (memory 1).val)
structure Live (memory : Memory) : Prop where
  first : 2 ≤ (memory 0).val
  second : 2 ≤ (memory 1).val
  worker : memory 2 = 4

def bump (memory : Memory) (site : Fin code.sites) : Memory := fun other =>
  if other = site then code.afterSend site 2 (memory other) 0 else memory other

set_option linter.unusedSimpArgs false in
theorem one_paid_local_word_spends_one_counter
    (memory : Memory) (live : Live memory) (site : Fin code.sites)
    (voter : site = 0 ∨ site = 1) (active : (memory site).val < 4) :
    Live (bump memory site) ∧ localDue (bump memory site) + 1 = localDue memory := by
  rcases live with ⟨first,second,worker⟩
  rcases voter with rfl | rfl
  all_goals refine ⟨⟨?_,?_,?_⟩,?_⟩
  all_goals simp_all [bump,localDue,code,RenewedQuorumSource.code] <;> omega

abbrev phaseRule (second : Bool) := RenewedQuorumSource.protocol resources 2 true false second
abbrev activate (site : Fin code.sites) := (RenewedQuorumSource.activation resources 2 true site).val
abbrev send (site : Fin code.sites) := (RenewedQuorumSource.sending resources 2 true site).val

def OwnShape (memory : Memory) (move : Move code) : Prop :=
  move = none ∨
    (∃ site, (site = 0 ∨ site = 1) ∧ memory site = 2 ∧ move = activate site) ∨
    (∃ site, (site = 0 ∨ site = 1) ∧ memory site = 3 ∧ move = send site)

set_option linter.unusedSimpArgs false in
theorem original_phase_rule_has_only_four_local_fee_positions
    (memory : Memory) (live : Live memory) (second : Bool) (site : Fin code.sites) :
    OwnShape memory (localEvent code (phaseRule second) site (memory site)) := by
  rcases live with ⟨first,other,worker⟩
  fin_cases site
  · generalize hs : memory 0 = signal at *
    fin_cases signal <;> cases second <;>
      simp_all [OwnShape,localEvent,phaseRule,RenewedQuorumSource.protocol,activate,send]
  · generalize hs : memory 1 = signal at *
    fin_cases signal <;> cases second <;>
      simp_all [OwnShape,localEvent,phaseRule,RenewedQuorumSource.protocol,activate,send]
  · simp [OwnShape,localEvent,phaseRule,RenewedQuorumSource.protocol,worker]

 theorem actual_later_protocol_is_the_original_phase_rule (n : Nat) (later : 23 ≤ n) :
    protocols n = phaseRule (decide (24 ≤ n)) := by
  simp [RenewedQuorumConsumer.protocols,RenewedQuorumSource.protocols,phaseRule,
    show ¬ n < 6 by omega]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualFeeStep
