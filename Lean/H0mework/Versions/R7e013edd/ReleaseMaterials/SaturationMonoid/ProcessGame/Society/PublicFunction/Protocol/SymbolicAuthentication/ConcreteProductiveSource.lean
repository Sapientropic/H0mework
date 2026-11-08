import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveSigningArchive
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecycledQuorumSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ConcreteProductiveSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
noncomputable section

abbrev resources : Repayment.Recovery.Resources := ⟨4,4,true⟩
abbrev source := RecycledQuorumSource.source resources 3 false
abbrev bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
 (Technology := Bool) (Instrument := Unit) :=
 ⟨Repayment.Recovery.base,Repayment.Recovery.scope,source,rfl,rfl⟩
abbrev genesis := RecycledQuorumSource.start resources 3 false
abbrev parent := RecursiveSigningSource.next bound genesis (RecursiveSigningSource.initial bound genesis) []
abbrev base := RecycledQuorumSource.vocabulary
abbrev scope := RecycledQuorumSource.slot false
abbrev laws (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Bool) (Instrument := Unit)) : StageReception.Law model.source.code := ⟨fun _ _ => scope,64⟩

abbrev acceptance : RecycledQuorumMaterial.Action := ⟨2,[],.reserve 2,[],.present⟩
-- The recycler accepts one actually transferred waste unit for a fixed window.
def contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Bool) (Instrument := Unit) :=
 ⟨1,2,.waste,1,36,RecycledQuorumMaterial.waste,acceptance⟩
abbrev before := JointReceptionSource.initial bound genesis parent
abbrev produced := JointReceptionSource.advance contract before (.execute [.command 2])
-- The original scheduler alternates local and external admission.
abbrev ready := JointReceptionSource.advance contract produced (.execute [.idle])
abbrev commands : List RenewableArchiveSource.Command := [.execute [.command 2],.execute [.idle]]
def request : FreshSigningSource.Request (Party := Party) (Good := Good) (Port := Port)
 (Technology := Bool) (Instrument := Unit) :=
 ⟨true,true,scope,true,18,0,[RecycledQuorumMaterial.production,RecycledQuorumSource.fee false]⟩
abbrev endpoint := FreshSigningSource.cycle contract base laws ready request
abbrev candidate := (SourceRepairSearch.cases contract 0 ready).head (by simp [SourceRepairSearch.cases])

theorem the_two_primitive_commands_are_in_the_original_source_menu :
 SourceRepairSearch.Path contract before commands := by
 change (.execute [.command 2]∈SourceRepairSearch.menu before) ∧
  (.execute [.idle]∈SourceRepairSearch.menu produced) ∧ True
 exact ⟨List.mem_append_left _ (List.mem_map.mpr ⟨.command 2,by decide +kernel,rfl⟩),
  List.mem_append_left _ (List.mem_map.mpr ⟨.idle,by decide +kernel,rfl⟩),trivial⟩

theorem the_prefix_replays_the_same_actual_successor :
 SourceRepairSearch.execute contract before commands=ready := rfl

theorem the_public_entry_recognizes_the_original_slot :
 ProductiveSigningArchive.begin bound contract base laws genesis parent scope true (fun _ => request) 0 0 0=
  some before := rfl

theorem the_current_waste_transfer_and_provider_acceptance_buy_the_new_window :
 PaidInvocationSource.admitted ready.actual.model.source.code contract ready.actual.point true true=true := by
 decide +kernel

theorem the_transfer_at_the_external_cut_cannot_open_a_window :
 PaidInvocationSource.admitted produced.actual.model.source.code contract produced.actual.point true true=false := by
 decide +kernel

theorem removing_provider_acceptance_cannot_open_a_window :
 PaidInvocationSource.admitted ready.actual.model.source.code contract ready.actual.point true false=false := by
 decide +kernel

theorem the_literal_full_cycle_has_exact_total_service_and_the_original_debt :
 ProductiveSigningSource.total before .service=3 ∧
 ProductiveSigningSource.total ready .service=6 ∧
 ProductiveSigningSource.total endpoint .service=6 ∧
 (ProductiveSigningSource.current before).claims () 1 2=7 := by
 and_intros <;> decide +kernel

theorem the_actual_full_cycle_has_three_net_service_units_and_a_new_quorum :
 ProductiveSigningSource.accepts contract base laws request .service 3 1 before candidate=true := by
 decide +kernel

theorem the_original_source_producer_computes_a_positive_success :
 ∃ branch positive generated checked,
 ProductiveSigningSource.produce contract base laws request .service 3 1 before 2=
  .produced branch positive generated checked := by
 obtain ⟨branch,member,_literal,actual⟩ := SourceRepairSearch.every_bounded_original_source_path_is_generated
  contract 2 before commands the_two_primitive_commands_are_in_the_original_source_menu (by decide)
 have same : branch.final=candidate.final := actual
 have checked : ProductiveSigningSource.accepts contract base laws request .service 3 1 before branch=true := by
  let test (state : JointReceptionSource.State bound.source.code) :=
   ProductiveSigningSource.accepts contract base laws request .service 3 1 before
    ((SourceRepairSearch.cases contract 0 state).head (by simp [SourceRepairSearch.cases]))
  change test branch.final=true
  exact (congrArg test same).trans the_actual_full_cycle_has_three_net_service_units_and_a_new_quorum
 have positive : (0 : ℚ)<3 := by norm_num
 obtain ⟨selected,generated,accepted,computed⟩ := ProductiveSigningSource.a_real_accepted_source_branch_is_found
  contract base laws request .service 3 1 before 2 positive branch member checked
 exact ⟨selected,positive,generated,accepted,computed⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ConcreteProductiveSource
