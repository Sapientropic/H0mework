import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CandidateDetailed
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

structure Approval (prepared : Prepared input) (units : Nat) : Type where
  private mk ::
  shape : Allowance.Shape prepared units
  source : shape = Allowance.describe prepared units
  paid : ∀ index : Index prepared,(shape.funding.resultAt index).funded
  ready : readyFor shape.body.menu = true
  enough : shape.amount ≤ units
inductive Failure {units : Nat} (shape : Allowance.Shape prepared units) where
  | unpaid (index : Index prepared) (failed : ¬ (shape.funding.resultAt index).funded)
  | outside (broken : readyFor shape.body.menu = false)
  | short (under : ¬ shape.amount ≤ units)
inductive Decision {units : Nat} (shape : Allowance.Shape prepared units) where
  | rejected (failure : Failure shape)
  | accepted (paid : ∀ index : Index prepared,(shape.funding.resultAt index).funded)
      (ready : readyFor shape.body.menu = true) (enough : shape.amount ≤ units)
structure Receipt (prepared : Prepared input) (units : Nat) where
  private mk ::
  shape : Allowance.Shape prepared units
  source : shape = Allowance.describe prepared units
  decision : Decision shape

def Receipt.approval? {units : Nat} (made : Receipt prepared units) : Option (Approval prepared units) :=
  match made.decision with
  | .rejected _ => none
  | .accepted paid ready enough => some ⟨made.shape,made.source,paid,ready,enough⟩

theorem Receipt.absent_has_a_source_reason {units : Nat} (made : Receipt prepared units) (absent : made.approval? = none) :
    (∃ index : Index prepared,¬ (made.shape.funding.resultAt index).funded) ∨
      readyFor made.shape.body.menu = false ∨ ¬ made.shape.amount ≤ units := by
  cases found : made.decision with
  | rejected failure => cases failure with
    | unpaid index failed => exact .inl ⟨index,failed⟩
    | outside broken => exact .inr (.inl broken)
    | short under => exact .inr (.inr under)
  | accepted => simp only [Receipt.approval?,found,reduceCtorEq] at absent

inductive Frame (prepared : Prepared input) (units : Nat) where
  | describing (cursor : Allowance.CandidateDescription.State prepared units)
  | checking (shape : Allowance.Shape prepared units) (source : shape = Allowance.describe prepared units)
      (amount : Nat) (amount_exact : amount = shape.amount) (todo : List (Index prepared))
      (passed : (∀ index ∈ todo,(shape.funding.resultAt index).funded) → ∀ index : Index prepared,(shape.funding.resultAt index).funded)
  | budget (shape : Allowance.Shape prepared units) (source : shape = Allowance.describe prepared units)
      (paid : ∀ index : Index prepared,(shape.funding.resultAt index).funded) (ready : readyFor shape.body.menu = true)
      (amount : Nat) (amount_exact : amount = shape.amount)
  | refused (shape : Allowance.Shape prepared units) (source : shape = Allowance.describe prepared units) (failure : Failure shape)
  | approved (made : Approval prepared units)

def Frame.rank {units : Nat} : Frame prepared units → Nat
  | .describing cursor => cursor.rank+(keys prepared).length+4
  | .checking _ _ _ _ todo _ => todo.length+3
  | .budget .. => 2
  | .refused .. | .approved _ => 1

variable {source : SourceQuota.Generated prepared} (catalogue : SourceQuota.Catalogue source.snapshot)
abbrev Row := Sigma fun quota : catalogue.Quota => Receipt prepared quota.val

def quotaWeight (quota : catalogue.Quota) := (Allowance.CandidateDescription.initial prepared quota.val).rank+(keys prepared).length+5
def remainingWeight (quotas : List catalogue.Quota) := (quotas.map (quotaWeight catalogue)).sum
inductive State where
  | waiting (cached : List (Row catalogue)) (remaining : List catalogue.Quota)
      (conserved : cached.map Sigma.fst ++ remaining = catalogue.quotas)
      (denied : ∀ row ∈ cached,row.2.approval? = none)
  | checking (cached : List (Row catalogue)) (quota : catalogue.Quota) (rest : List catalogue.Quota)
      (conserved : cached.map Sigma.fst ++ quota::rest = catalogue.quotas)
      (denied : ∀ row ∈ cached,row.2.approval? = none) (frame : Frame prepared quota.val)
  | released (cached : List (Row catalogue)) (quota : catalogue.Quota) (rest : List catalogue.Quota)
      (conserved : cached.map Sigma.fst ++ quota::rest = catalogue.quotas)
      (denied : ∀ row ∈ cached,row.2.approval? = none) (made : Approval prepared quota.val)
  | exhausted (cached : List (Row catalogue)) (complete : cached.map Sigma.fst = catalogue.quotas)
      (denied : ∀ row ∈ cached,row.2.approval? = none)

def initial : State catalogue := .waiting [] catalogue.quotas rfl (by intro row inside;cases inside)
inductive Event where
  | opened (quota : catalogue.Quota)
  | description (quota : catalogue.Quota) (event : Allowance.CandidateDescription.Event prepared quota.val)
  | described (quota : catalogue.Quota) (shape : Allowance.Shape prepared quota.val) (source : shape = Allowance.describe prepared quota.val)
  | paid (quota : catalogue.Quota) (shape : Allowance.Shape prepared quota.val) (index : Index prepared) (actual : (shape.funding.resultAt index).funded)
  | unpaid (quota : catalogue.Quota) (shape : Allowance.Shape prepared quota.val) (index : Index prepared) (actual : ¬ (shape.funding.resultAt index).funded)
  | ready (quota : catalogue.Quota) (shape : Allowance.Shape prepared quota.val) (actual : readyFor shape.body.menu = true)
  | outside (quota : catalogue.Quota) (shape : Allowance.Shape prepared quota.val) (actual : readyFor shape.body.menu = false)
  | enough (quota : catalogue.Quota) (shape : Allowance.Shape prepared quota.val) (actual : shape.amount ≤ quota.val)
  | short (quota : catalogue.Quota) (shape : Allowance.Shape prepared quota.val) (actual : ¬ shape.amount ≤ quota.val)
  | rejected (quota : catalogue.Quota) (receipt : Receipt prepared quota.val) (absent : receipt.approval? = none)
  | accepted (quota : catalogue.Quota) (made : Approval prepared quota.val)
  | complete

def move : State catalogue → Option (State catalogue × Event catalogue)
  | .waiting cached [] conserved denied => some (.exhausted cached (by simpa only [List.append_nil] using conserved) denied,.complete)
  | .waiting cached (quota::rest) conserved denied => some (.checking cached quota rest conserved denied (.describing (Allowance.CandidateDescription.initial prepared quota.val)),.opened quota)
  | .checking cached quota rest conserved denied (.describing (.finished output)) =>
      some (.checking cached quota rest conserved denied (.checking output.shape output.source output.amount output.amount_exact (keys prepared)
        (fun passed index => passed index (List.mem_finRange _))),.described quota output.shape output.source)
  | .checking cached quota rest conserved denied (.describing cursor@(.funding ..))
  | .checking cached quota rest conserved denied (.describing cursor@(.body ..))
  | .checking cached quota rest conserved denied (.describing cursor@(.measuring ..)) =>
      match _actual : Allowance.CandidateDescription.move cursor with
      | none => none
      | some (after,event) => some (.checking cached quota rest conserved denied (.describing after),.description quota event)
  | .checking cached quota rest conserved denied (.checking shape generated amount amountExact [] passed) =>
      let paid := passed (by intro index inside;cases inside)
      if ready : readyFor shape.body.menu = true then
        some (.checking cached quota rest conserved denied (.budget shape generated paid ready amount amountExact),.ready quota shape ready)
      else
        let broken := Bool.eq_false_iff.mpr ready
        some (.checking cached quota rest conserved denied (.refused shape generated (.outside broken)),.outside quota shape broken)
  | .checking cached quota rest conserved denied (.checking shape generated amount amountExact (index::todo) passed) =>
      if paid : (shape.funding.resultAt index).funded then
        some (.checking cached quota rest conserved denied (.checking shape generated amount amountExact todo (by
          intro later
          apply passed
          intro other inside
          rcases List.mem_cons.mp inside with same | following
          · subst other;exact paid
          · exact later other following)),.paid quota shape index paid)
      else some (.checking cached quota rest conserved denied (.refused shape generated (.unpaid index paid)),.unpaid quota shape index paid)
  | .checking cached quota rest conserved denied (.budget shape generated paid ready amount amountExact) =>
      if enough : amount ≤ quota.val then
        some (.checking cached quota rest conserved denied (.approved ⟨shape,generated,paid,ready,(by rw [← amountExact];exact enough)⟩),.enough quota shape (by rw [← amountExact];exact enough))
      else some (.checking cached quota rest conserved denied (.refused shape generated (.short (by rw [← amountExact];exact enough))),.short quota shape (by rw [← amountExact];exact enough))
  | .checking cached quota rest conserved denied (.refused shape generated failure) =>
      let receipt : Receipt prepared quota.val := ⟨shape,generated,.rejected failure⟩
      let row : Row catalogue := ⟨quota,receipt⟩
      some (.waiting (cached++[row]) rest (by
          simp only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]
          exact conserved) (by
          intro other inside
          rcases List.mem_append.mp inside with old | last
          · exact denied other old
          · have same := List.mem_singleton.mp last
            subst other;rfl),.rejected quota receipt rfl)
  | .checking cached quota rest conserved denied (.approved made) =>
      some (.released cached quota rest conserved denied made,.accepted quota made)
  | .released .. | .exhausted .. => none

def State.finished : State catalogue → Bool
  | .released .. | .exhausted .. => true
  | _ => false
def State.rank : State catalogue → Nat
  | .waiting _ remaining .. => remainingWeight catalogue remaining+1
  | .checking _ _ rest _ _ frame => remainingWeight catalogue rest+frame.rank+1
  | .released .. | .exhausted .. => 0

theorem each_actual_step_decreases_source_rank {before after : State catalogue} {event : Event catalogue}
    (actual : move catalogue before = some (after,event)) : after.rank catalogue < before.rank catalogue := by
  cases before with
  | waiting cached remaining conserved denied =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,Frame.rank,remainingWeight,quotaWeight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil];omega
  | checking cached quota rest conserved denied frame =>
      cases frame with
      | describing cursor =>
          cases cursor with
          | finished =>
              dsimp only [move] at actual;cases Option.some.inj actual
              simp only [State.rank,Frame.rank,Allowance.CandidateDescription.State.rank];omega
          | funding =>
              dsimp only [move] at actual;split at actual
              · cases actual
              · rename_i after event step
                cases Option.some.inj actual
                have less := Allowance.CandidateDescription.progress step
                simp only [State.rank,Frame.rank];omega
          | body =>
              dsimp only [move] at actual;split at actual
              · cases actual
              · rename_i after event step
                cases Option.some.inj actual
                have less := Allowance.CandidateDescription.progress step
                simp only [State.rank,Frame.rank];omega
          | measuring =>
              dsimp only [move] at actual;split at actual
              · cases actual
              · rename_i after event step
                cases Option.some.inj actual
                have less := Allowance.CandidateDescription.progress step
                simp only [State.rank,Frame.rank];omega
      | checking shape generated amount amountExact todo passed =>
          cases todo <;> dsimp only [move] at actual <;> split at actual
          all_goals cases Option.some.inj actual
          all_goals simp only [State.rank,Frame.rank,List.length_cons,List.length_nil];omega
      | budget =>
          dsimp only [move] at actual;split at actual
          all_goals cases Option.some.inj actual
          all_goals simp only [State.rank,Frame.rank];omega
      | refused =>
          dsimp only [move] at actual;cases Option.some.inj actual
          simp only [State.rank,Frame.rank];omega
      | approved =>
          dsimp only [move] at actual;cases Option.some.inj actual
          simp only [State.rank,Frame.rank];omega
  | released | exhausted => cases actual

theorem no_move_iff_finished (before : State catalogue) : move catalogue before = none ↔ before.finished catalogue = true := by
  cases before with
  | waiting cached remaining conserved denied => cases remaining <;> simp [move,State.finished]
  | checking cached quota rest conserved denied frame =>
      cases frame with
      | describing cursor =>
          cases cursor with
          | finished => simp [move,State.finished]
          | funding | body | measuring =>
              all_goals dsimp only [move,State.finished];split
              all_goals first
                | (rename_i stopped;have done := (Allowance.CandidateDescription.no_move_iff_done _).mp stopped;cases done)
                | simp
      | refused | approved => simp [move,State.finished]
      | checking shape generated amount amountExact todo passed => cases todo <;> dsimp only [move,State.finished] <;> split <;> simp
      | budget => dsimp only [move,State.finished];split <;> simp
  | released | exhausted => simp [move,State.finished]

structure Chosen where
  private mk ::
  quota : catalogue.Quota
  approval : Approval prepared quota.val
  cached : List (Row catalogue)
  remaining : List catalogue.Quota
  conserved : cached.map Sigma.fst ++ quota::remaining = catalogue.quotas
  denied : ∀ row ∈ cached,row.2.approval? = none

def State.selection : State catalogue → Option (Chosen catalogue)
  | .released cached quota rest conserved denied made => some ⟨quota,made,cached,rest,conserved,denied⟩
  | _ => none

theorem exhausted_covers_every_original_quota (cached : List (Row catalogue)) (complete : cached.map Sigma.fst = catalogue.quotas)
    (denied : ∀ row ∈ cached,row.2.approval? = none) (quota : catalogue.Quota) :
    ∃ row ∈ cached,row.1 = quota ∧ row.2.approval? = none := by
  have listed : quota ∈ cached.map Sigma.fst := by rw [complete];exact List.mem_finRange _
  obtain ⟨row,inside,same⟩ := List.mem_map.mp listed
  exact ⟨row,inside,same,denied row inside⟩

inductive Trace : State catalogue → State catalogue → List (Event catalogue) → Prop
  | nil (before) : Trace before before []
  | step {before middle after event work} (actual : move catalogue before = some (middle,event)) (later : Trace middle after work) : Trace before after (event::work)
structure Calculation (before : State catalogue) (capacity : Nat) where
  private mk ::
  endpoint : State catalogue
  work : List (Event catalogue)
  history : Trace catalogue before endpoint work
  fits : work.length ≤ capacity

def execute : (capacity : Nat) → (before : State catalogue) → Calculation catalogue before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match actual : move catalogue before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) => let later := execute capacity after
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩
theorem sufficient_source_rank_finishes (capacity : Nat) (before : State catalogue) (enough : before.rank catalogue ≤ capacity) :
    (execute catalogue capacity before).endpoint.finished catalogue = true := by
  induction capacity generalizing before with
  | zero => cases before <;> simp_all [State.rank,State.finished,Frame.rank,remainingWeight,Allowance.CandidateDescription.State.rank,execute]
  | succ capacity ih =>
    unfold execute;split
    · rename_i stopped;exact (no_move_iff_finished catalogue before).mp stopped
    · rename_i after event actual;exact ih after (by have := each_actual_step_decreases_source_rank catalogue actual;omega)
theorem unfinished_uses_all (capacity : Nat) (before : State catalogue)
    (pending : (execute catalogue capacity before).endpoint.finished catalogue = false) : (execute catalogue capacity before).work.length = capacity := by
  induction capacity generalizing before with
  | zero => rfl
  | succ capacity ih =>
    unfold execute at pending ⊢;split at pending
    · rename_i stopped;rw [(no_move_iff_finished catalogue before).mp stopped] at pending;cases pending
    · rename_i after event actual;exact congrArg Nat.succ (ih after pending)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CandidateDetailed
