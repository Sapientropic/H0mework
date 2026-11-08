import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveSigningConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveSigningArchive
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ProductiveSigningSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 [Fintype Party] [Fintype Instrument]
 (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (laws : (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) → StageReception.Law model.source.code)
 (genesis : Cursor bound.source.code) (parent : RecursiveSigningSource.State bound genesis)
 (oldScope : Scope) (oldValue : Bool) (control : FreshSigningSource.Controller (root := bound.source.code))
 (slot oldDepth rounds : Nat)
 (request : FreshSigningSource.Request (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (good : Good) (quota : ℚ) (threshold : Nat)

abbrev begin := FreshSigningConsumer.continueFrom contract base laws bound genesis parent oldScope oldValue control slot oldDepth rounds

def produce (depth : Nat) : Option ((before : JointReceptionSource.State bound.source.code) ×
 Result contract base laws request good quota threshold before depth) :=
 match begin bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds with
 | none => none
 | some before => some ⟨before,ProductiveSigningSource.produce contract base laws request good quota threshold before depth⟩

def run (depth count : Nat) : Option (JointReceptionSource.State bound.source.code) :=
 match begin bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds with
 | none => none
 | some before => some (ProductiveSigningSource.run contract base laws request good quota threshold before depth count)

theorem the_public_run_keeps_the_original_finances_and_counts_actual_net_production
 (before : JointReceptionSource.State bound.source.code)
 (actual : begin bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds=some before)
 (depth count : Nat) :
 ∃ final, run bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds request good quota threshold depth count=some final ∧
 total before good+(producedCount contract base laws request good quota threshold before depth count : ℚ)*quota≤total final good ∧
 (current final).claims=(current before).claims ∧
 before.actual.archive <+: final.actual.archive ∧ before.actual.windows <+: final.actual.windows ∧
 before.rows <+: final.rows ∧ ArchivedDeliveryConsumer.NativeContinuation final.actual.model final.actual.point := by
 refine ⟨ProductiveSigningSource.run contract base laws request good quota threshold before depth count,?_,?_,?_,?_⟩
 · simp only [run,actual]
 · exact ProductiveSigningConsumer.repeated_actual_cycles_generate_cumulative_net_new_material contract base laws request good quota threshold before depth count
 · exact ProductiveSigningConsumer.repeated_actual_cycles_keep_every_original_financial_position contract base laws request good quota threshold before depth count
 · exact ProductiveSigningConsumer.repeated_actual_cycles_keep_all_original_history_and_own_next contract base laws request good quota threshold before depth count

theorem each_accepted_original_source_cycle_has_net_new_material_production_and_an_actual_quorum
 (before : JointReceptionSource.State bound.source.code)
 (actual : begin bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds=some before)
 (depth : Nat) (branch : SourceRepairSearch.Branch bound.source.code) (positive : 0<quota)
 (generated : branch∈SourceRepairSearch.cases contract depth before)
 (checked : accepts contract base laws request good quota threshold before branch=true)
 (selected : ProductiveSigningSource.produce contract base laws request good quota threshold before depth=.produced branch positive generated checked) :
 produce bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds request good quota threshold depth=
  some ⟨before,.produced branch positive generated checked⟩ ∧
 total before good+quota≤total (endpoint contract base laws request branch) good ∧
 (current (endpoint contract base laws request branch)).claims=(current before).claims ∧
 (∃ row∈(endpoint contract base laws request branch).rows.drop before.rows.length,
  ∃ item∈StageTrace.items row.actual, ∃ operator,
  item.request.operation=.produce operator ∧ row.code.law.Valid item.before item.request) ∧
 (∃ answer∈decisions contract base laws request threshold branch,
  FreshSigningConsumer.decision contract base laws (prepared contract request branch) request answer.1 threshold=.decided answer.2) ∧
 before.actual.archive <+: (endpoint contract base laws request branch).actual.archive ∧
 before.actual.windows <+: (endpoint contract base laws request branch).actual.windows ∧
 before.rows <+: (endpoint contract base laws request branch).rows ∧
 ArchivedDeliveryConsumer.NativeContinuation (endpoint contract base laws request branch).actual.model
  (endpoint contract base laws request branch).actual.point := by
 have verified := acceptance_checks_the_actual_full_cycle contract base laws request good quota threshold before branch checked
 have nonempty : decisions contract base laws request threshold branch≠[] := List.isEmpty_eq_false_iff.mp verified.2.2.2
 obtain ⟨answer,member⟩ := List.exists_mem_of_ne_nil _ nonempty
 refine ⟨?_,verified.1,?_,?_,?_,?_⟩
 · simp only [produce,actual,selected]
 · exact ProductiveSigningConsumer.accepted_claims_are_the_entire_original_financial_matrix contract base laws request good quota threshold before branch checked
 · exact ProductiveSigningConsumer.accepted_growth_contains_a_new_actual_valid_production_occurrence contract base laws request good quota threshold before branch checked
 · exact ⟨answer,member,ProductiveSigningConsumer.every_readout_is_an_actual_new_global_quorum contract base laws request threshold branch answer member⟩
 · exact ProductiveSigningConsumer.a_selected_cycle_keeps_all_original_history_and_its_own_next contract base laws request before depth branch generated

theorem a_computed_block_keeps_the_original_state_and_excludes_the_bounded_source_domain
 (before : JointReceptionSource.State bound.source.code) (depth : Nat) (positive : 0<quota)
 (exhausted : ∀ branch∈SourceRepairSearch.cases contract depth before,
  accepts contract base laws request good quota threshold before branch=false)
 (blocked : ProductiveSigningSource.produce contract base laws request good quota threshold before depth=.blocked positive exhausted) :
 ProductiveSigningSource.next contract base laws request good quota threshold before depth=before ∧
 increment contract base laws request good quota threshold before depth=0 ∧
 ∀ branch∈SourceRepairSearch.cases contract depth before,
  accepts contract base laws request good quota threshold before branch≠true := by
 refine ⟨?_,?_,?_⟩
 · simp only [ProductiveSigningSource.next,blocked]
 · simp only [increment,blocked]
 · intro branch member accepted
   rw [exhausted branch member] at accepted
   contradiction

theorem deleting_the_original_source_removes_both_production_and_continuation
 (missing : parent.archive[slot]?=none) (depth count : Nat) :
 produce bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds request good quota threshold depth=none ∧
 run bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds request good quota threshold depth count=none := by
 simp only [produce,run,begin,FreshSigningConsumer.continueFrom,SourceRepairArchive.produce,missing,and_self]

-- The original source inventories cover the whole carrier, including off-site parties.
def sourceRun (depth count : Nat) : Option (JointReceptionSource.State bound.source.code) :=
 letI : Fintype Party := Fintype.ofList bound.source.code.parties bound.source.code.parties_cover
 letI : Fintype Instrument := Fintype.ofList bound.source.code.instruments bound.source.code.instruments_cover
 run bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds request good quota threshold depth count

omit [Fintype Party] [Fintype Instrument] in
theorem the_source_inventories_generate_the_net_production_carrier
 (before : JointReceptionSource.State bound.source.code)
 (actual : begin bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds=some before)
 (depth count : Nat) :
 letI : Fintype Party := Fintype.ofList bound.source.code.parties bound.source.code.parties_cover
 letI : Fintype Instrument := Fintype.ofList bound.source.code.instruments bound.source.code.instruments_cover
 ∃ final, sourceRun bound contract base laws genesis parent oldScope oldValue control slot oldDepth rounds request good quota threshold depth count=some final ∧
 total before good+(producedCount contract base laws request good quota threshold before depth count : ℚ)*quota≤total final good ∧
 (current final).claims=(current before).claims ∧
 before.actual.archive <+: final.actual.archive ∧ before.actual.windows <+: final.actual.windows ∧
 before.rows <+: final.rows ∧ ArchivedDeliveryConsumer.NativeContinuation final.actual.model final.actual.point := by
 let _ : Fintype Party := Fintype.ofList bound.source.code.parties bound.source.code.parties_cover
 let _ : Fintype Instrument := Fintype.ofList bound.source.code.instruments bound.source.code.instruments_cover
 exact the_public_run_keeps_the_original_finances_and_counts_actual_net_production bound contract base laws genesis parent oldScope oldValue
  control slot oldDepth rounds request good quota threshold before actual depth count

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveSigningArchive
