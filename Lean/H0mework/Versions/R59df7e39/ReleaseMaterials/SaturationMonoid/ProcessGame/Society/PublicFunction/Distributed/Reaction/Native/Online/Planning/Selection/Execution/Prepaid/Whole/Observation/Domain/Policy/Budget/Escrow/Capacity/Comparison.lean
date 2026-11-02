import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Comparison.Pool
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.Comparison
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Pool catalogue) (index : Index prepared)

structure Branch where
  private mk ::
  entry : Cached catalogue
  listed : entry ∈ pool.cached
  scope : Whole.Scope (initial input prepared.saved[index].point) input.pricing input.future
    (reference input prepared.saved[index].point) input.actor input.position
  ready : stageAt entry.2.attempt index = .ready scope
  intent : Intent scope

def branches : List (Branch pool index) := pool.cached.attach.flatMap fun entry =>
  match ready : stageAt entry.val.2.attempt index with
  | .ready scope => (Whole.intents scope).map fun intent => ⟨entry.val,entry.property,scope,ready,intent⟩
  | .stopped _ | .blocked _ => []

namespace Branch
variable {pool index}
theorem scope_included (branch : Branch pool index) : branch.scope ∈ pool.scopes index :=
  pool.each_cached_ready_scope_is_included branch.entry branch.listed index branch.scope branch.ready

theorem generated (branch : Branch pool index) : branch ∈ branches pool index := by
  rcases branch with ⟨entry,listed,scope,ready,intent⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨entry,listed⟩,List.mem_attach _ _,?_⟩
  split
  · rename_i actual same
    cases Stage.ready.inj (same.symm.trans ready)
    exact List.mem_map.mpr ⟨intent,Whole.every_intent_is_generated scope intent,rfl⟩
  · rename_i header same
    cases same.symm.trans ready
  · rename_i failure same
    cases same.symm.trans ready

def tensor (branch : Branch pool index) (rival : Opponent (initial input prepared.saved[index].point).source.val.code) :=
  Whole.tensor branch.scope input.span branch.intent rival

def Covered (branch : Branch pool index) : Prop :=
  input.future ≤ (comparisonPoint branch.scope).state.remaining
instance (branch : Branch pool index) : Decidable branch.Covered := inferInstanceAs (Decidable (_ ≤ _))

def Deployable (branch : Branch pool index) : Prop := Whole.Deployable branch.scope branch.intent
instance (branch : Branch pool index) : Decidable branch.Deployable := by unfold Deployable;infer_instance
end Branch

abbrev Table := QuotaJoint.Table (pool.scopes index)
def tables := QuotaJoint.tables (pool.scopes index)
abbrev rival (table : Table pool index) := QuotaJoint.opponent (pool.scopes index) table

def OldCovered : Prop := input.span ≤ (initial input prepared.saved[index].point).state.remaining
instance : Decidable (OldCovered index) := inferInstanceAs (Decidable (_ ≤ _))

def NoWorse (new previous : Branch pool index) : Prop :=
  OldCovered index ∧ new.Covered ∧ previous.Covered ∧ new.Deployable ∧
    ∀ table ∈ tables pool index,accepts (initial input prepared.saved[index].point)
      (new.tensor (rival pool index table)) (previous.tensor (rival pool index table))
instance (new previous : Branch pool index) : Decidable (NoWorse pool index new previous) := by unfold NoWorse;infer_instance

theorem comparison_iff_every_same_adaptive_opponent (new previous : Branch pool index)
    (old : OldCovered index) (newBound : new.Covered) (previousBound : previous.Covered) :
    (∀ table ∈ tables pool index,accepts (initial input prepared.saved[index].point)
      (new.tensor (rival pool index table)) (previous.tensor (rival pool index table))) ↔
    ∀ opponent : Opponent (initial input prepared.saved[index].point).source.val.code,
      accepts (initial input prepared.saved[index].point) (new.tensor opponent) (previous.tensor opponent) :=
  QuotaJoint.finite_comparison_iff_every_same_adaptive_opponent (pool.scopes index) input.span
    new.scope previous.scope new.scope_included previous.scope_included new.intent previous.intent
    old newBound previousBound (accepts (initial input prepared.saved[index].point))

inductive Row where
  | originalCoverage
  | currentCoverage
  | previousCoverage
  | deployment
  | present (table : Table pool index)
  | future (table : Table pool index) (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model))
  | funding (table : Table pool index) (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model))

def economicRows : List (Row pool index) := (tables pool index).flatMap fun table =>
  [.present table] ++ (Future.Recovery.capabilities (initial input prepared.saved[index].point).model
    (initial input prepared.saved[index].point).depth).map (.future table) ++
    (Future.Recovery.capabilities (initial input prepared.saved[index].point).model
    (initial input prepared.saved[index].point).depth).map (.funding table)
def rows : List (Row pool index) := [.originalCoverage,.currentCoverage,.previousCoverage,.deployment] ++ economicRows pool index

def Holds (new previous : Branch pool index) : Row pool index → Prop
  | .originalCoverage => OldCovered index
  | .currentCoverage => new.Covered
  | .previousCoverage => previous.Covered
  | .deployment => new.Deployable
  | .present table => Synthesis.accepts (initial input prepared.saved[index].point).source.val.code
      (Window.axes (initial input prepared.saved[index].point).model (initial input prepared.saved[index].point).depth)
      (new.tensor (rival pool index table)).present (previous.tensor (rival pool index table)).present
  | .future table word => futureNoWorse (initial input prepared.saved[index].point)
      ((new.tensor (rival pool index table)).future _ word) ((previous.tensor (rival pool index table)).future _ word)
  | .funding table word => ((previous.tensor (rival pool index table)).funding _ word).isNone = true →
      ((new.tensor (rival pool index table)).funding _ word).isNone = true
instance (new previous : Branch pool index) (row : Row pool index) : Decidable (Holds pool index new previous row) := by
  cases row <;> unfold Holds <;> infer_instance

theorem rows_iff (new previous : Branch pool index) :
    (∀ row ∈ rows pool index,Holds pool index new previous row) ↔ NoWorse pool index new previous := by
  constructor
  · intro all
    refine ⟨all .originalCoverage (by simp [rows]),all .currentCoverage (by simp [rows]),
      all .previousCoverage (by simp [rows]),all .deployment (by simp [rows]),?_⟩
    intro table inside
    refine ⟨all (.present table) ?_,?_,?_⟩
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨table,inside,
        List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)⟩)
    · intro word member
      exact all (.future table word) (List.mem_append_right _ (List.mem_flatMap.mpr ⟨table,inside,
        List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨word,member,rfl⟩))⟩))
    · intro word member
      exact all (.funding table word) (List.mem_append_right _ (List.mem_flatMap.mpr ⟨table,inside,
        List.mem_append_right _ (List.mem_map.mpr ⟨word,member,rfl⟩)⟩))
  · rintro ⟨old,newBound,previousBound,deployable,all⟩ row inside
    rcases List.mem_append.mp inside with gate | economic
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at gate
      rcases gate with same | same | same | same <;> subst row
      · exact old
      · exact newBound
      · exact previousBound
      · exact deployable
    · obtain ⟨table,member,generated⟩ := List.mem_flatMap.mp economic
      have valid := all table member
      simp only [List.mem_append,List.mem_singleton,List.mem_map] at generated
      rcases generated with (same | ⟨word,registered,same⟩) | ⟨word,registered,same⟩
      · subst row;exact valid.1
      · subst row;exact valid.2.1 word registered
      · subst row;exact valid.2.2 word registered

structure Rejection (new previous : Branch pool index) where
  row : Row pool index
  listed : row ∈ rows pool index
  broken : ¬ Holds pool index new previous row
inductive Checked (new previous : Branch pool index) where
  | accepted (valid : NoWorse pool index new previous)
  | rejected (why : Rejection pool index new previous)

def compare (new previous : Branch pool index) : Checked pool index new previous :=
  match Distributed.inspect (Holds pool index new previous) (rows pool index) with
  | .accepted all => .accepted ((rows_iff pool index new previous).mp all)
  | .rejected row listed broken => .rejected ⟨row,listed,broken⟩


def verify (new previous : Branch pool index) : Bool := decide (NoWorse pool index new previous)
theorem independent_verification_accepts (new previous : Branch pool index)
    (accepted : NoWorse pool index new previous) : verify pool index new previous = true := decide_eq_true accepted

abbrev PairIndex := Fin (branches pool index).length × Fin (branches pool index).length
def pairKeys : List (PairIndex pool index) :=
  (List.finRange (branches pool index).length).flatMap fun first =>
    (List.finRange (branches pool index).length).map (first,·)
theorem every_pair_is_generated (key : PairIndex pool index) : key ∈ pairKeys pool index :=
  List.mem_flatMap.mpr ⟨key.1,List.mem_finRange _,List.mem_map.mpr ⟨key.2,List.mem_finRange _,rfl⟩⟩

structure Test (key : PairIndex pool index) where
  private mk ::
  outcome : Checked pool index (branches pool index)[key.1] (branches pool index)[key.2]
  generated : outcome = compare pool index (branches pool index)[key.1] (branches pool index)[key.2]
def test (key : PairIndex pool index) : Test pool index key :=
  ⟨compare pool index (branches pool index)[key.1] (branches pool index)[key.2],rfl⟩
abbrev CachedTest := Sigma (Test pool index)
def tests : List (CachedTest pool index) := (pairKeys pool index).map fun key => ⟨key,test pool index key⟩
structure Matrix where
  private mk ::
  cached : List (CachedTest pool index)
  generated : cached = tests pool index
  keys_exact : cached.map Sigma.fst = pairKeys pool index

def generateMatrix : Matrix pool index := ⟨tests pool index,rfl,by
  simp only [tests,List.map_map,Function.comp_def]
  exact List.map_id (pairKeys pool index)⟩

namespace Matrix
variable {pool index} (matrix : Matrix pool index)
theorem every_generated_branch_pair_is_tested (key : PairIndex pool index) :
    ∃ cached ∈ matrix.cached,cached.1 = key := by
  have inside := every_pair_is_generated pool index key
  rw [←matrix.keys_exact] at inside
  exact List.mem_map.mp inside

theorem every_source_branch_pair_is_tested (first second : Branch pool index) :
    ∃ cached ∈ matrix.cached,(branches pool index)[cached.1.1] = first ∧ (branches pool index)[cached.1.2] = second := by
  obtain ⟨left,boundedLeft,sameLeft⟩ := List.mem_iff_getElem.mp first.generated
  obtain ⟨right,boundedRight,sameRight⟩ := List.mem_iff_getElem.mp second.generated
  obtain ⟨cached,listed,same⟩ := matrix.every_generated_branch_pair_is_tested (⟨left,boundedLeft⟩,⟨right,boundedRight⟩)
  refine ⟨cached,listed,?_,?_⟩
  · have located := congrArg (fun key : PairIndex pool index => (branches pool index).get key.1) same
    exact located.trans sameLeft
  · have located := congrArg (fun key : PairIndex pool index => (branches pool index).get key.2) same
    exact located.trans sameRight
inductive Debt (matrix : Matrix pool index) where
  | prior (debt : Pool.Debt pool)
  | test (cached : CachedTest pool index)
  | tensorConstruction
  | rowInspection
  | independentVerification

def pending : List (Debt matrix) :=
  pool.pending.map Debt.prior ++ matrix.cached.map Debt.test ++
    [.tensorConstruction,.rowInspection,.independentVerification]
end Matrix


/- Source grammar for the original keep/control/own/invoice order. Operands are loaded
only when their constructor is reached; their native internals remain separate debt. -/
namespace IntentSource
variable {pool index}
variable (scope : Whole.Scope (initial input prepared.saved[index].point) input.pricing input.future
  (reference input prepared.saved[index].point) input.actor input.position)
inductive Task where
  | keep
  | loadControl
  | control (remaining : List (Term (paidPoint scope)))
  | loadOwn
  | own (remaining : List (Whole.OwnOption scope))
  | ownTerms (own : Whole.OwnOption scope) (remaining : List (Term (paidPoint scope)))
  | loadInvoice
  | invoices (remaining : List (Whole.InvoiceOption scope))
  | invoiceTerms (invoice : Whole.InvoiceOption scope) (remaining : List (Term (paidPoint scope)))
abbrev Cursor := List (Task scope)
def start : Cursor scope := [.keep,.loadControl,.loadOwn,.loadInvoice]

def Task.denote : Task scope → List (Whole.Intent scope)
  | .keep => [.keep]
  | .loadControl => (terms (paidPoint scope)).map fun term => .paid (.control term)
  | .control remaining => remaining.map fun term => .paid (.control term)
  | .loadOwn => (Whole.ownOptions scope).attach.flatMap fun own =>
      (terms (paidPoint scope)).map fun term => .paid (.own own term)
  | .own remaining => remaining.flatMap fun own =>
      (terms (paidPoint scope)).map fun term => .paid (.own own term)
  | .ownTerms option remaining => remaining.map fun term => .paid (.own option term)
  | .loadInvoice => (Whole.invoiceOptions scope).attach.flatMap fun invoice =>
      (terms (paidPoint scope)).map fun term => .paid (.invoiced invoice term)
  | .invoices remaining => remaining.flatMap fun invoice =>
      (terms (paidPoint scope)).map fun term => .paid (.invoiced invoice term)
  | .invoiceTerms option remaining => remaining.map fun term => .paid (.invoiced option term)
def denote (cursor : Cursor scope) := cursor.flatMap (Task.denote scope)

theorem start_is_the_original_intent_order : denote scope (start scope) = Whole.intents scope := by
  simp [denote,start,Task.denote,Whole.intents,Whole.continuations,List.map_append,List.map_flatMap,List.map_map,Function.comp_def]

inductive Event where
  | emit (intent : Whole.Intent scope)
  | loadControl | loadOwn | loadInvoice | openOwn | openInvoice | close

def step : Cursor scope → Option (Cursor scope × Option (Whole.Intent scope) × Event scope)
  | [] => none
  | .keep::rest => some (rest,some .keep,.emit .keep)
  | .loadControl::rest => some (.control (terms (paidPoint scope))::rest,none,.loadControl)
  | .control []::rest => some (rest,none,.close)
  | .control (term::tail)::rest => some (.control tail::rest,some (.paid (.control term)),.emit (.paid (.control term)))
  | .loadOwn::rest => some (.own (Whole.ownOptions scope).attach::rest,none,.loadOwn)
  | .own []::rest => some (rest,none,.close)
  | .own (own::tail)::rest => some (.ownTerms own (terms (paidPoint scope))::.own tail::rest,none,.openOwn)
  | .ownTerms _ []::rest => some (rest,none,.close)
  | .ownTerms own (term::tail)::rest => some (.ownTerms own tail::rest,some (.paid (.own own term)),.emit (.paid (.own own term)))
  | .loadInvoice::rest => some (.invoices (Whole.invoiceOptions scope).attach::rest,none,.loadInvoice)
  | .invoices []::rest => some (rest,none,.close)
  | .invoices (invoice::tail)::rest => some (.invoiceTerms invoice (terms (paidPoint scope))::.invoices tail::rest,none,.openInvoice)
  | .invoiceTerms _ []::rest => some (rest,none,.close)
  | .invoiceTerms invoice (term::tail)::rest => some (.invoiceTerms invoice tail::rest,some (.paid (.invoiced invoice term)),.emit (.paid (.invoiced invoice term)))

theorem one_step_conserves {before after : Cursor scope} {yielded : Option (Whole.Intent scope)} {event : Event scope}
    (observed : step scope before = some (after,yielded,event)) : denote scope before = yielded.toList++denote scope after := by
  cases before with
  | nil => cases observed
  | cons task rest =>
    cases task <;> first | (rename_i remaining;cases remaining) | skip
    all_goals dsimp only [step] at observed
    all_goals cases Option.some.inj observed
    all_goals simp [denote,Task.denote,List.append_assoc]

def Task.rank : Task scope → Nat
  | .keep => 1
  | .loadControl => 2+(terms (paidPoint scope)).length
  | .control remaining | .ownTerms _ remaining | .invoiceTerms _ remaining => 1+remaining.length
  | .loadOwn => 2+(Whole.ownOptions scope).length*((terms (paidPoint scope)).length+2)
  | .own remaining => 1+remaining.length*((terms (paidPoint scope)).length+2)
  | .loadInvoice => 2+(Whole.invoiceOptions scope).length*((terms (paidPoint scope)).length+2)
  | .invoices remaining => 1+remaining.length*((terms (paidPoint scope)).length+2)
def rank (cursor : Cursor scope) := (cursor.map (Task.rank scope)).sum

theorem step_decreases_rank {before after : Cursor scope} {yielded : Option (Whole.Intent scope)} {event : Event scope}
    (observed : step scope before = some (after,yielded,event)) : rank scope after+1 = rank scope before := by
  cases before with
  | nil => cases observed
  | cons task rest =>
    cases task <;> first | (rename_i remaining;cases remaining) | skip
    all_goals dsimp only [step] at observed
    all_goals cases Option.some.inj observed
    all_goals simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_cons,List.length_nil,List.length_attach,Nat.add_mul,Nat.one_mul,Nat.zero_mul,Nat.add_zero]
    all_goals omega

theorem stopped_iff_empty (before : Cursor scope) : step scope before = none ↔ before = [] := by
  cases before with
  | nil => simp [step]
  | cons task rest =>
    cases task <;> first | (rename_i remaining;cases remaining) | skip
    all_goals simp [step]
end IntentSource

namespace BranchSource
variable {pool index}
def entry (quota : catalogue.Quota) : Cached catalogue := ⟨quota,enter catalogue quota⟩
theorem entry_listed (pool : Pool catalogue) (quota : catalogue.Quota) : entry quota ∈ pool.cached := by
  rw [pool.generated]
  exact List.mem_map.mpr ⟨quota,List.mem_finRange _,rfl⟩

def block (pool : Pool catalogue) (index : Index prepared) (cached : Cached catalogue) (listed : cached ∈ pool.cached) :
    List (Branch pool index) := match ready : stageAt cached.2.attempt index with
  | .ready scope => (Whole.intents scope).map fun intent => ⟨cached,listed,scope,ready,intent⟩
  | .stopped _ | .blocked _ => []
def quotas (pool : Pool catalogue) (index : Index prepared) (remaining : List catalogue.Quota) :=
  remaining.flatMap fun quota => block pool index (entry quota) (entry_listed pool quota)

theorem all_quotas_are_exactly_the_original_branches (pool : Pool catalogue) (index : Index prepared) :
    quotas pool index catalogue.quotas = branches pool index := by
  let f := fun quota => block pool index (entry quota) (entry_listed pool quota)
  rcases pool with ⟨cached,generated,keys_exact⟩
  cases generated
  simp only [quotas,branches,entries,List.attach_map,List.flatMap_map]
  have erase := List.flatMap_map Subtype.val f catalogue.quotas.attach
  rw [List.attach_map_subtype_val] at erase
  exact erase.trans (by rfl)

inductive Cursor (pool : Pool catalogue) (index : Index prepared) where
  | quotas (remaining : List catalogue.Quota)
  | entered (quota : catalogue.Quota) (cached : Entry catalogue quota) (generated : cached = enter catalogue quota)
      (tail : List catalogue.Quota)
  | intents (cached : Cached catalogue) (listed : cached ∈ pool.cached)
      (scope : Whole.Scope (initial input prepared.saved[index].point) input.pricing input.future
        (reference input prepared.saved[index].point) input.actor input.position)
      (ready : stageAt cached.2.attempt index = .ready scope) (current : IntentSource.Cursor scope)
      (tail : List catalogue.Quota)
def start (pool : Pool catalogue) (index : Index prepared) : Cursor pool index := .quotas catalogue.quotas

def Cursor.denote : Cursor pool index → List (Branch pool index)
  | .quotas remaining => BranchSource.quotas pool index remaining
  | .entered quota cached generated tail => block pool index ⟨quota,cached⟩ (generated ▸ entry_listed pool quota)++BranchSource.quotas pool index tail
  | .intents cached listed scope ready current tail =>
      (IntentSource.denote scope current).map (fun intent => ⟨cached,listed,scope,ready,intent⟩)++BranchSource.quotas pool index tail

inductive Event (pool : Pool catalogue) (index : Index prepared) where
  | entered (quota : catalogue.Quota)
  | staged (quota : catalogue.Quota)
  | intent (cached : Cached catalogue) (listed : cached ∈ pool.cached)
      (scope : Whole.Scope (initial input prepared.saved[index].point) input.pricing input.future
        (reference input prepared.saved[index].point) input.actor input.position)
      (ready : stageAt cached.2.attempt index = .ready scope) (event : IntentSource.Event scope)
  | close

def step : Cursor pool index → Option (Cursor pool index × Option (Branch pool index) × Event pool index)
  | .quotas [] => none
  | .quotas (quota::tail) => some (.entered quota (enter catalogue quota) rfl tail,none,.entered quota)
  | .entered quota cached generated tail =>
      let listed : (⟨quota,cached⟩ : Cached catalogue) ∈ pool.cached := generated ▸ entry_listed pool quota
      match ready : stageAt cached.attempt index with
      | .ready scope => some (.intents ⟨quota,cached⟩ listed scope ready (IntentSource.start scope) tail,none,.staged quota)
      | .stopped _ | .blocked _ => some (.quotas tail,none,.staged quota)
  | .intents cached listed scope ready current tail => match IntentSource.step scope current with
      | none => some (.quotas tail,none,.close)
      | some (after,yielded,event) => some (.intents cached listed scope ready after tail,
          yielded.map (fun intent => ⟨cached,listed,scope,ready,intent⟩),.intent cached listed scope ready event)

theorem one_step_conserves {before after : Cursor pool index} {yielded : Option (Branch pool index)} {event : Event pool index}
    (observed : step before = some (after,yielded,event)) : before.denote = yielded.toList++after.denote := by
  cases before with
  | quotas remaining =>
    cases remaining with
    | nil => cases observed
    | cons quota tail =>
      cases Option.some.inj observed
      rfl
  | entered quota cached generated tail =>
    cases generated
    dsimp only [step] at observed
    split at observed
    · rename_i scope ready
      cases Option.some.inj observed
      dsimp only [Cursor.denote,block]
      split
      · rename_i actual same
        cases Stage.ready.inj (same.symm.trans ready)
        simp only [IntentSource.start_is_the_original_intent_order,Option.toList_none,List.nil_append]
      · rename_i header same;cases same.symm.trans ready
      · rename_i failure same;cases same.symm.trans ready
    · rename_i stopped ready
      cases Option.some.inj observed
      dsimp only [Cursor.denote,block]
      split
      · rename_i actual same;cases same.symm.trans ready
      · rfl
      · rfl
    · rename_i blocked ready
      cases Option.some.inj observed
      dsimp only [Cursor.denote,block]
      split
      · rename_i actual same;cases same.symm.trans ready
      · rfl
      · rfl
  | intents cached listed scope ready current tail =>
    dsimp only [step] at observed
    split at observed
    · rename_i stopped
      cases Option.some.inj observed
      have empty := (IntentSource.stopped_iff_empty scope current).mp stopped
      simp only [Cursor.denote,empty,IntentSource.denote,List.flatMap_nil,List.map_nil,Option.toList_none,List.nil_append]
    · rename_i next emitted event actual
      cases Option.some.inj observed
      have conserved := IntentSource.one_step_conserves scope actual
      simp only [Cursor.denote,conserved,List.map_append,List.append_assoc]
      cases emitted <;> rfl

def blockRank (index : Index prepared) (cached : Cached catalogue) : Nat := match stageAt cached.2.attempt index with
  | .ready scope => IntentSource.rank scope (IntentSource.start scope)+1
  | .stopped _ | .blocked _ => 0
def quotaRank (index : Index prepared) (remaining : List catalogue.Quota) : Nat :=
  (remaining.map fun quota => blockRank index (entry quota)+2).sum

def Cursor.rank : Cursor pool index → Nat
  | .quotas remaining => quotaRank index remaining
  | .entered quota cached _ tail => blockRank index ⟨quota,cached⟩+1+quotaRank index tail
  | .intents _ _ scope _ current tail => IntentSource.rank scope current+1+quotaRank index tail

theorem step_decreases_rank {before after : Cursor pool index} {yielded : Option (Branch pool index)} {event : Event pool index}
    (observed : step before = some (after,yielded,event)) : after.rank+1 = before.rank := by
  cases before with
  | quotas remaining =>
    cases remaining with
    | nil => cases observed
    | cons quota tail =>
      cases Option.some.inj observed
      simp only [Cursor.rank,quotaRank,List.map_cons,List.sum_cons,entry]
      omega
  | entered quota cached generated tail =>
    cases generated
    dsimp only [step] at observed
    split at observed
    all_goals cases Option.some.inj observed
    all_goals dsimp only [Cursor.rank,blockRank]
    all_goals simp only [*]
    all_goals omega
  | intents cached listed scope ready current tail =>
    dsimp only [step] at observed
    split at observed
    · rename_i stopped
      cases Option.some.inj observed
      have empty := (IntentSource.stopped_iff_empty scope current).mp stopped
      simp only [Cursor.rank,empty,IntentSource.rank,List.map_nil,List.sum_nil]
      omega
    · rename_i next emitted event actual
      cases Option.some.inj observed
      have reduced := IntentSource.step_decreases_rank scope actual
      simp only [Cursor.rank]
      omega

theorem stopped_has_no_residual (before : Cursor pool index) (stopped : step before = none) : before.denote = [] := by
  cases before with
  | quotas remaining => cases remaining <;> simp_all [step,Cursor.denote,quotas]
  | entered quota cached generated tail => dsimp only [step] at stopped;split at stopped <;> cases stopped
  | intents cached listed scope ready current tail => dsimp only [step] at stopped;split at stopped <;> cases stopped
end BranchSource

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.Comparison
