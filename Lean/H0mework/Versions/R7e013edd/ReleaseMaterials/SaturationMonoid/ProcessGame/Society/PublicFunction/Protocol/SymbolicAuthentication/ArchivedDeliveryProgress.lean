import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliverySource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliveryProgress
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource ArchivedDeliverySource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code) (genesis : Cursor bound.source.code)

-- Birth identities come from the finite original issuing table. Repeated packets
-- and later phases cannot refill these original receipt obligations.
def outstanding (state : State bound genesis) (origin : Segment bound)
 (receiver : Fin bound.source.code.sites) : Finset (Nat × Nat) :=
 (((origin.wires bound base).filter (fun wire => decide (wire.recipient=receiver))).map
  (fun wire => (wire.ballot.cut,wire.ballot.position))).toFinset \
 ((previous bound base law genesis state receiver origin).receipts.map
  (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))).toFinset

theorem service_strictly_reduces_the_original_unreceived_births
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (service : Service bound base law genesis state slot receiver) :
 ∃ origin, state.archive[slot]?=some origin ∧
  (outstanding bound base law genesis (next bound genesis state [service.input]) origin receiver).card+1 =
  (outstanding bound base law genesis state origin receiver).card := by
 obtain ⟨origin,wire,located,_,updated,member,address,fresh⟩ :=
  a_service_executes_and_generates_its_next_real_receipt bound base law genesis state slot receiver service
 have missing : (wire.ballot.cut,wire.ballot.position) ∈
  outstanding bound base law genesis state origin receiver := by
  apply Finset.mem_sdiff.mpr
  exact ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨wire,List.mem_filter.mpr ⟨member,decide_eq_true address⟩,rfl⟩),by simpa only [List.mem_toFinset] using fresh⟩
 have decreased : outstanding bound base law genesis (next bound genesis state [service.input]) origin receiver =
  (outstanding bound base law genesis state origin receiver).erase (wire.ballot.cut,wire.ballot.position) := by
  unfold outstanding previous
  rw [updated]
  simp only [List.map_append,List.map_cons,List.map_nil,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
   Finset.insert_empty,Finset.union_singleton,Finset.sdiff_insert]
 refine ⟨origin,located,?_⟩
 rw [decreased]
 exact Finset.card_erase_add_one missing

def step (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites) : State bound genesis :=
 (produce bound base law genesis state slot receiver).after bound base law genesis state slot receiver

theorem every_generated_step_is_either_a_real_receipt_or_an_exact_source_refusal
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites) :
 (∃ service, produce bound base law genesis state slot receiver=.served service ∧
   step bound base law genesis state slot receiver=next bound genesis state [service.input] ∧
   ∃ origin, state.archive[slot]?=some origin ∧
    (outstanding bound base law genesis (step bound base law genesis state slot receiver) origin receiver).card+1=
     (outstanding bound base law genesis state origin receiver).card) ∨
 (step bound base law genesis state slot receiver=state ∧
  ∀ input ∈ CommandWindowSource.menu bound, available bound base law genesis state slot receiver input=false) := by
 cases outcome : produce bound base law genesis state slot receiver with
 | served service =>
  have actual : step bound base law genesis state slot receiver=next bound genesis state [service.input] := by
   simp only [step,outcome,Result.after]
  refine Or.inl ⟨service,rfl,actual,?_⟩
  rw [actual]
  exact service_strictly_reduces_the_original_unreceived_births bound base law genesis state slot receiver service
 | blocked absent => exact Or.inr ⟨by simp only [step,outcome,Result.after],absent⟩

def run (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites) : Nat → State bound genesis :=
 Nat.rec state fun _ current => step bound base law genesis current slot receiver

theorem run_after_the_first_actual_step (state : State bound genesis) (slot : Nat)
 (receiver : Fin bound.source.code.sites) (count : Nat) :
 run bound base law genesis (step bound base law genesis state slot receiver) slot receiver count =
 run bound base law genesis state slot receiver (count+1) := by
 induction count with
 | zero => rfl
 | succ count ih => exact congrArg (fun current => step bound base law genesis current slot receiver) ih

theorem original_birth_count_bounds_the_actual_service_run
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (origin : Segment bound) (located : state.archive[slot]?=some origin) :
 ∃ count ≤ (outstanding bound base law genesis state origin receiver).card,
  ∀ input ∈ CommandWindowSource.menu bound,
   available bound base law genesis (run bound base law genesis state slot receiver count) slot receiver input=false := by
 generalize size : (outstanding bound base law genesis state origin receiver).card = budget
 induction budget using Nat.strong_induction_on generalizing state with
 | h budget ih =>
  cases selected : produce bound base law genesis state slot receiver with
  | blocked absent => exact ⟨0,Nat.zero_le _,absent⟩
  | served service =>
   obtain ⟨original,whereAt,decrease⟩ :=
    service_strictly_reduces_the_original_unreceived_births bound base law genesis state slot receiver service
   have same : original=origin := Option.some.inj (whereAt.symm.trans located)
   subst original
   have actual : step bound base law genesis state slot receiver=next bound genesis state [service.input] := by
    simp only [step,selected,Result.after]
   have smaller : (outstanding bound base law genesis (step bound base law genesis state slot receiver) origin receiver).card < budget := by
    rw [actual] at ⊢
    omega
   have kept : (step bound base law genesis state slot receiver).archive[slot]?=some origin := by
    rw [actual]
    exact an_archived_origin_keeps_its_index bound genesis state slot service.input origin located
   obtain ⟨count,bounded,absent⟩ := ih _ smaller _ kept rfl
   simp only [run_after_the_first_actual_step] at absent
   exact ⟨count+1,by omega,absent⟩

theorem explicit_source_opportunities_flush_the_original_receipt_obligations
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (origin : Segment bound) (located : state.archive[slot]?=some origin)
 (opportunities : ∀ count ≤ (outstanding bound base law genesis state origin receiver).card,
   (outstanding bound base law genesis (run bound base law genesis state slot receiver count) origin receiver).Nonempty →
   ∃ input ∈ CommandWindowSource.menu bound,
    available bound base law genesis (run bound base law genesis state slot receiver count) slot receiver input=true) :
 ∃ count ≤ (outstanding bound base law genesis state origin receiver).card,
  outstanding bound base law genesis (run bound base law genesis state slot receiver count) origin receiver=∅ := by
 obtain ⟨count,bounded,absent⟩ :=
  original_birth_count_bounds_the_actual_service_run bound base law genesis state slot receiver origin located
 refine ⟨count,bounded,?_⟩
 by_contra remaining
 obtain ⟨input,registered,accepted⟩ := opportunities count bounded (Finset.nonempty_iff_ne_empty.mpr remaining)
 have impossible := absent input registered
 rw [accepted] at impossible
 contradiction

theorem every_step_retains_all_original_stages_and_issuing_contexts
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites) :
 state.stages <+: (step bound base law genesis state slot receiver).stages ∧
 state.archive <+: (step bound base law genesis state slot receiver).archive := by
 unfold step
 cases produce bound base law genesis state slot receiver with
 | served service => exact every_round_keeps_the_entire_actual_prefix bound genesis state [service.input]
 | blocked => exact ⟨List.prefix_refl _,List.prefix_refl _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliveryProgress
