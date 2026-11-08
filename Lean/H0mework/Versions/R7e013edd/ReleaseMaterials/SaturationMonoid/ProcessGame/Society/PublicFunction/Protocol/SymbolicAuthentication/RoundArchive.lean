import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SubjectQuorum
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.HistoryCoupling

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundArchive
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Machine Party Good Port Technology Instrument) (count : Nat)

abbrev depth := old.history.length + 1 + count
def snapshot : List (RawEvent Party Good Port Technology Instrument) :=
  List.ofFn fun index : Fin (depth old count) => (old.actualExecution index.val).submitted

theorem snapshot_length : (snapshot old count).length = depth old count := List.length_ofFn

theorem old_history_is_an_actual_snapshot_prefix : old.history <+: snapshot old count := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by rw [snapshot_length];dsimp [depth];omega,?_⟩
  intro index bound
  simp only [snapshot,List.getElem_ofFn]
  exact (old.history_word_is_actual index bound).symm

theorem public_prefix_is_retained : old.code.publicPrefix <+: snapshot old count := by
  obtain ⟨suffix,_,shape⟩ := List.mem_map.mp old.original
  have retained : old.code.publicPrefix <+: old.history := ⟨suffix,shape⟩
  exact retained.trans (old_history_is_an_actual_snapshot_prefix old count)

variable (arrival : RawEvent Party Good Port Technology Instrument)
  (request fee : Request Party Good Port Technology Instrument)

def suffix := (snapshot old count).drop old.code.publicPrefix.length ++ [arrival]

-- Only the observed past expands historical admission. Genesis/law/bootstrap and the old
-- action alphabet/word bound remain; the atomic request has its own local interface.
abbrev code : Code Party Good Port Technology Instrument where
  law := old.code.law
  initial := old.code.initial
  bootstrap := old.code.bootstrap
  task := old.code.task
  actions := old.code.actions ++ [request]
  actionLimit := max old.code.actionLimit 1
  sites := 1
  signals := 3
  initialSignal := 0
  siteParty := fun _ => request.signer
  readLocal := fun _ _ => 1
  afterAction := fun _ _ _ => 1
  afterSend := fun _ _ _ _ => 2
  afterDelivery := fun _ _ old _ => old
  sendCost := fun _ _ => [fee]
  deliveryCost := fun _ => [fee]
  historyAlphabet := suffix old count arrival
  historyLimit := (suffix old count arrival).length
  eventAlphabet := [.activate 0,.send 0 0,.deliver 0]
  eventLimit := 0
  eligible := fun _ => true
  parties := old.code.parties
  goods := old.code.goods
  instruments := old.code.instruments
  parties_cover := old.code.parties_cover
  goods_cover := old.code.goods_cover
  instruments_cover := old.code.instruments_cover

def history := old.code.publicPrefix ++ suffix old count arrival

theorem history_is_the_entire_actual_snapshot_and_new_arrival :
    history old count arrival = snapshot old count ++ [arrival] := by
  have retained := (List.prefix_iff_eq_take.mp (public_prefix_is_retained old count))
  change old.code.publicPrefix ++ ((snapshot old count).drop old.code.publicPrefix.length ++ [arrival]) = _
  rw [← List.append_assoc]
  apply congrArg (fun front => front ++ [arrival])
  exact (congrArg (fun front => front ++ (snapshot old count).drop old.code.publicPrefix.length) retained).trans
    (List.take_append_drop _ _)

def admissible : Bool := (code old count arrival request fee).historyLegal
  ((code old count arrival request fee).historyCurrent (code old count arrival request fee).publicPrefix)
  (suffix old count arrival)

structure Ready : Type where
  private mk ::
  admitted : admissible old count arrival request fee = true

def inspect : Option (Ready old count arrival request fee) :=
  if admitted : admissible old count arrival request fee then some ⟨admitted⟩ else none

variable {old count arrival request fee}

abbrev Ready.source (ready : Ready old count arrival request fee) : Machine Party Good Port Technology Instrument where
  code := code old count arrival request fee
  reference := fun _ _ => [request]
  reference_generated := by
    apply (code old count arrival request fee).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr ⟨by simp,by simp⟩
  history := history old count arrival
  original := by
    apply List.mem_map.mpr
    refine ⟨suffix old count arrival,List.mem_filter.mpr ⟨?_,ready.admitted⟩,rfl⟩
    exact (mem_sequences_iff _ _ _).mpr ⟨Nat.le_refl _,fun _ member => member⟩
  opponent := fun _ _ _ => none
  side := .original

variable (old count arrival request fee) (ready : Ready old count arrival request fee)

theorem no_genesis_stock_or_claim_is_reset :
    ready.source.code.initial = old.code.initial ∧ ready.source.code.law = old.code.law ∧
      ready.source.history = snapshot old count ++ [arrival] :=
  ⟨rfl,rfl,history_is_the_entire_actual_snapshot_and_new_arrival old count arrival⟩

theorem prior_body (ordinal : Nat) (earlier : ordinal < depth old count) :
    ready.source.body (old.currentAt (ordinal+1)) = old.body (old.currentAt (ordinal+1)) := by
  have address : (old.currentAt (ordinal+1)).round - old.code.initial.round - 1 = ordinal := by
    rw [old.current_round];omega
  unfold Machine.body
  change (match (history old count arrival)[(old.currentAt (ordinal+1)).round-old.code.initial.round-1]? with
    | some word => word | none => _) = _
  rw [address,history_is_the_entire_actual_snapshot_and_new_arrival]
  rw [List.getElem?_append_left (by rw [snapshot_length];exact earlier)]
  simp only [snapshot,List.getElem?_ofFn,dif_pos earlier]
  simpa only [Machine.body,address] using old.actual_word ordinal

theorem prior_events (ordinal : Nat) (earlier : ordinal < depth old count+1) :
    ProgrammeSource.rawEvent ready.source.input (ProgrammeHistory.visitAt old.input ordinal).current =
      ProgrammeSource.rawEvent old.input (ProgrammeHistory.visitAt old.input ordinal).current := by
  cases ordinal with
  | zero => rfl
  | succ ordinal =>
    have view : ∃ current past, (ProgrammeHistory.visitAt old.input (ordinal+1)).current = .running current past := by
      cases state : (ProgrammeHistory.visitAt old.input ordinal).current <;>
        simp only [ProgrammeHistory.visitAt,ProgrammeSource.next,state] <;> exact ⟨_,_,rfl⟩
    obtain ⟨current,past,view⟩ := view
    have same := prior_body old count arrival request fee ready ordinal (by omega)
    change ProgrammeSource.rawEvent ready.source.input _ = _
    rw [view]
    change ready.source.body current = old.body current
    simpa only [Machine.currentAt,view,ProgrammeSource.rawCurrent] using same

theorem every_original_raw_occurrence_is_preserved (ordinal : Nat) (earlier : ordinal < depth old count+1) :
    (ProgrammeHistory.visitAt ready.source.input ordinal).current = (ProgrammeHistory.visitAt old.input ordinal).current ∧
      ProgrammeSource.rawEvent ready.source.input (ProgrammeHistory.visitAt ready.source.input ordinal).current =
        ProgrammeSource.rawEvent old.input (ProgrammeHistory.visitAt old.input ordinal).current :=
  Native.Coupling.History.occurrences old.input ready.source.input rfl rfl (depth old count+1)
    (prior_events old count arrival request fee ready) ordinal earlier

theorem every_original_financial_account_is_preserved (ordinal : Nat) (earlier : ordinal ≤ depth old count+1) :
    Native.Coupling.Match old.code old.input ready.source.input (Financial.accountAt old.input ordinal)
      (Financial.accountAt ready.source.input ordinal) :=
  Native.Coupling.History.complete_accounts old.code old.input ready.source.input rfl rfl (depth old count+1)
    (prior_events old count arrival request fee ready) old.body ready.source.body rfl rfl ordinal earlier

theorem arrival_is_an_actual_new_raw_occurrence :
    (ready.source.actualExecution (depth old count)).submitted = arrival ∧
      (ready.source.actualExecution (depth old count)).before = old.currentAt (depth old count+1) ∧
      (ready.source.actualExecution (depth old count)).after = old.code.law.next (old.currentAt (depth old count+1)) arrival := by
  have length : (history old count arrival).length = depth old count+1 := by
    rw [history_is_the_entire_actual_snapshot_and_new_arrival,List.length_append,snapshot_length];rfl
  have bounded : depth old count < ready.source.history.length := by change depth old count < (history old count arrival).length;omega
  have submitted := ready.source.history_word_is_actual (depth old count) bounded
  change _ = (history old count arrival)[depth old count] at submitted
  have word : (ready.source.actualExecution (depth old count)).submitted = arrival := by
    apply Option.some.inj
    have indexed := List.getElem?_eq_getElem bounded
    calc
      some (ready.source.actualExecution (depth old count)).submitted = (history old count arrival)[depth old count]? :=
        (congrArg some submitted).trans indexed.symm
      _ = some arrival := by
        rw [history_is_the_entire_actual_snapshot_and_new_arrival,List.getElem?_append_right (by rw [snapshot_length])]
        simp only [snapshot_length,Nat.sub_self,List.getElem?_cons_zero]
  have current := Machine.actual_prefix_from_events old.input ready.source.input rfl rfl (depth old count+1)
    (prior_events old count arrival request fee ready) (depth old count+1) (Nat.le_refl _)
  have before : (ready.source.actualExecution (depth old count)).before = old.currentAt (depth old count+1) := by
    change ready.source.currentAt (depth old count+1) = _
    unfold Machine.currentAt
    rw [current]
    rfl
  exact ⟨word,before,by rw [(ready.source.actualExecution _).after_exact,word,before];rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundArchive
