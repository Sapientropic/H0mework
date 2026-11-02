import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual.Joint
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Prefix
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code}
  (cursor : Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
  (n : Nat) (reference : Term cursor) (actor : Party) (position : Nat)

structure Scope where
  private mk ::
  fee : Future.Recovery.Action cursor.model
  registered : feeAt cursor actor position = some fee
  paid : (payment cursor pricing n fee).succeeded = true
  covered : required cursor pricing n fee ≤ units cursor pricing n
  header : Protocol cursor pricing n reference actor position
  header_exact : header = invoke cursor pricing n reference actor position
  paidWord : List (Future.Recovery.Action cursor.model)
  paidWord_exact : paidWord = (payment cursor pricing n fee).output
  continuation : Prefix.Journal (cursor.submit paidWord) actor position
  ownFamily : Bool
  invoiceQuotes : List (List (Future.Recovery.Action cursor.model) × Nat)

def prepare : Protocol cursor pricing n reference actor position ⊕ Scope cursor pricing n reference actor position :=
  let header := invoke cursor pricing n reference actor position
  match header.result with
  | .ready fee registered paid covered _ _ => .inr ⟨fee,registered,paid,covered,header,rfl,(payment cursor pricing n fee).output,rfl,Prefix.empty _ _ _,false,[]⟩
  | .unpriced _ | .refused .. | .shortfall .. => .inl header

variable {cursor pricing n reference actor position}
  (scope : Scope cursor pricing n reference actor position)
abbrev paidPoint := cursor.submit scope.paidWord

theorem the_paid_point_is_the_original_generated_payment : paidPoint scope = point cursor pricing n scope.fee := by
  dsimp only [paidPoint]
  rw [scope.paidWord_exact]

abbrev comparisonPoint := scope.continuation.point

def extend (bill : Prefix.Bill (paidPoint scope) actor position)
    (same : bill.before = scope.continuation.words) : Scope cursor pricing n reference actor position :=
  ⟨scope.fee,scope.registered,scope.paid,scope.covered,scope.header,scope.header_exact,
    scope.paidWord,scope.paidWord_exact,scope.continuation.append bill same,scope.ownFamily,scope.invoiceQuotes⟩

def extendOwn (own : Prefix.Own (paidPoint scope) actor)
    (same : own.before = scope.continuation.words) : Scope cursor pricing n reference actor position :=
  ⟨scope.fee,scope.registered,scope.paid,scope.covered,scope.header,scope.header_exact,
    scope.paidWord,scope.paidWord_exact,scope.continuation.appendOwn own same,scope.ownFamily,scope.invoiceQuotes⟩

theorem comparison_point_includes_every_actual_fee_word :
    (comparisonPoint scope).depth = cursor.depth+1+scope.continuation.words.length := by
  have later := Prefix.at_depth (paidPoint scope) scope.continuation.words
  have initial : (paidPoint scope).depth = cursor.depth+1 := by
    change cursor.source.val.history.length+1+(cursor.count+1) = cursor.depth+1
    dsimp only [Cursor.depth,Machine.Continuation.depth]
    omega
  exact later.trans (congrArg (·+scope.continuation.words.length) initial)

def comparisonTerm (term : Term (paidPoint scope)) : Term (comparisonPoint scope) :=
  Prefix.reindex (paidPoint scope) term scope.continuation.words

def originalTerm (term : Term (comparisonPoint scope)) : Term (paidPoint scope) :=
  ⟨term.val,by change term.val ∈ controls (paidPoint scope);exact term.property⟩

theorem every_current_control_is_represented (term : Term (comparisonPoint scope)) :
    comparisonTerm scope (originalTerm scope term) = term := by
  apply Subtype.ext
  rfl

/-- Opens the source grammar before reserving the enlarged comparison work. -/
def withOwnFamily : Scope cursor pricing n reference actor position :=
  ⟨scope.fee,scope.registered,scope.paid,scope.covered,scope.header,scope.header_exact,
    scope.paidWord,scope.paidWord_exact,scope.continuation,true,scope.invoiceQuotes⟩

/-- Raw quantity quotations are data; registration and payment are regenerated at each actual branch. -/
def withOwnInvoices (quotes : List (List (Future.Recovery.Action cursor.model) × Nat)) :
    Scope cursor pricing n reference actor position :=
  ⟨scope.fee,scope.registered,scope.paid,scope.covered,scope.header,scope.header_exact,
    scope.paidWord,scope.paidWord_exact,scope.continuation,true,quotes⟩

def ownOptions : List (Prefix.Own (paidPoint scope) actor) :=
  if scope.ownFamily then Prefix.ownCandidates (paidPoint scope) actor scope.continuation.words else []

abbrev OwnOption := {own // own ∈ ownOptions scope}

theorem own_option_has_the_actual_before (own : OwnOption scope) :
    own.val.before = scope.continuation.words := by
  have member := own.property
  unfold ownOptions at member
  split at member
  · obtain ⟨word,_,same⟩ := List.mem_map.mp member
    rw [←same]
  · cases member

def invoiceOptions : List (Prefix.Settlement (paidPoint scope) actor position) :=
  (ownOptions scope).flatMap fun own => scope.invoiceQuotes.filterMap fun quotation =>
    if quotation.1 = own.requested then some (Prefix.settle (paidPoint scope) actor position own quotation.2) else none

abbrev InvoiceOption := {invoice // invoice ∈ invoiceOptions scope}

theorem every_quoted_own_pair_is_generated (own : OwnOption scope)
    (quotation : List (Future.Recovery.Action cursor.model) × Nat)
    (listed : quotation ∈ scope.invoiceQuotes) (same : quotation.1 = own.val.requested) :
    ∃ invoice : InvoiceOption scope, invoice.val.own = own.val ∧ invoice.val.units = quotation.2 := by
  let invoice := Prefix.settle (paidPoint scope) actor position own.val quotation.2
  have member : invoice ∈ invoiceOptions scope := List.mem_flatMap.mpr
    ⟨own.val,own.property,List.mem_filterMap.mpr ⟨quotation,listed,by simp only [if_pos same];rfl⟩⟩
  exact ⟨⟨invoice,member⟩,rfl,rfl⟩

theorem invoice_has_the_actual_own_before (invoice : InvoiceOption scope) :
    invoice.val.own.before = scope.continuation.words := by
  obtain ⟨own,member,generated⟩ := List.mem_flatMap.mp invoice.property
  obtain ⟨quotation,_,same⟩ := List.mem_filterMap.mp generated
  split at same
  · have equal := Option.some.inj same
    rw [←equal]
    exact own_option_has_the_actual_before scope ⟨own,member⟩
  · contradiction

def invoiceJournal (invoice : InvoiceOption scope) : Prefix.Journal (paidPoint scope) actor position :=
  invoice.val.appendTo scope.continuation (invoice_has_the_actual_own_before scope invoice)

theorem invoice_journal_is_its_own_complete_actual_word (invoice : InvoiceOption scope) :
    (invoiceJournal scope invoice).words = invoice.val.words :=
  invoice.val.appendTo_words scope.continuation (invoice_has_the_actual_own_before scope invoice)

inductive Continuation where
  | control (term : Term (paidPoint scope))
  | own (attempt : OwnOption scope) (term : Term (paidPoint scope))
  | invoiced (attempt : InvoiceOption scope) (term : Term (paidPoint scope))

instance : Coe (Term (paidPoint scope)) (Continuation scope) := ⟨Continuation.control⟩

def continuations : List (Continuation scope) :=
  (terms (paidPoint scope)).map Continuation.control ++
    ((ownOptions scope).attach.flatMap fun own => (terms (paidPoint scope)).map (Continuation.own own)) ++
    (invoiceOptions scope).attach.flatMap fun invoice => (terms (paidPoint scope)).map (Continuation.invoiced invoice)

theorem every_continuation_is_generated (plan : Continuation scope) : plan ∈ continuations scope := by
  cases plan with
  | control term => exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨term,List.mem_attach _ _,rfl⟩))
  | own attempt term => exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨attempt,List.mem_attach _ _,List.mem_map.mpr ⟨term,List.mem_attach _ _,rfl⟩⟩))
  | invoiced attempt term => exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨attempt,List.mem_attach _ _,List.mem_map.mpr ⟨term,List.mem_attach _ _,rfl⟩⟩)

theorem every_registered_own_control_pair_is_generated
    (openFamily : scope.ownFamily = true)
    (word : List (Future.Recovery.Action cursor.model))
    (bounded : word ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit)
    (personal : Mandate.Replay.Personal actor word) (control : Term (paidPoint scope)) :
    ∃ attempt : OwnOption scope, attempt.val.requested = word ∧
      Continuation.own attempt control ∈ continuations scope := by
  obtain ⟨own,member,before,requested⟩ := Prefix.every_personal_registered_word_is_generated
    (paidPoint scope) actor scope.continuation.words word bounded personal
  have inside : own ∈ ownOptions scope := by simpa [ownOptions,openFamily] using member
  exact ⟨⟨own,inside⟩,requested,every_continuation_is_generated scope _⟩

namespace Continuation
variable {scope} (plan : Continuation scope)
def words : List (List (Future.Recovery.Action cursor.model)) := match plan with
  | .control _ => scope.continuation.words
  | .own attempt _ => scope.continuation.words ++ [attempt.val.execution.output]
  | .invoiced attempt _ => attempt.val.words
abbrev point := Prefix.pointFor (paidPoint scope) plan.words
def term : Term plan.point := match plan with
  | .control value => Prefix.reindex (paidPoint scope) value scope.continuation.words
  | .own attempt value => Prefix.reindex (paidPoint scope) value
      (scope.continuation.words ++ [attempt.val.execution.output])
  | .invoiced attempt value => Prefix.reindex (paidPoint scope) value attempt.val.words
end Continuation

inductive Intent where
  | keep
  | paid (term : Continuation scope)

def intents : List (Intent scope) := .keep :: (continuations scope).map Intent.paid

theorem every_intent_is_generated (intent : Intent scope) : intent ∈ intents scope := by
  cases intent with
  | keep => simp [intents]
  | paid term => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨term,every_continuation_is_generated scope _,rfl⟩)

/-- The unpaid reference cannot undo an already committed family reservation. -/
def Deployable (intent : Intent scope) : Prop :=
  if scope.ownFamily then match intent with
    | .keep => False
    | .paid (.invoiced invoice _) => invoice.val.paid = true
    | .paid _ => True
  else True
instance (intent : Intent scope) : Decidable (Deployable scope intent) := by
  unfold Deployable
  split
  · cases intent with
    | keep => infer_instance
    | paid plan => cases plan <;> infer_instance
  · infer_instance

def ownFrame (own : OwnOption scope) : Feedback.Residual.Joint.Frame cursor.source.val.code :=
  let point := Prefix.pointFor (paidPoint scope) (scope.continuation.words ++ [own.val.execution.output])
  ⟨point.state,programs point⟩

def invoiceFrame (invoice : InvoiceOption scope) : Feedback.Residual.Joint.Frame cursor.source.val.code :=
  let point := Prefix.pointFor (paidPoint scope) invoice.val.words
  ⟨point.state,programs point⟩

def frames : List (Feedback.Residual.Joint.Frame cursor.source.val.code) :=
  [⟨cursor.state,programs cursor⟩,⟨(comparisonPoint scope).state,programs (comparisonPoint scope)⟩] ++
    (ownOptions scope).attach.map (ownFrame scope) ++
    (invoiceOptions scope).attach.map (invoiceFrame scope)

theorem every_continuation_frame_is_generated (plan : Continuation scope) :
    ⟨plan.point.state,programs plan.point⟩ ∈ frames scope := by
  cases plan with
  | control _ => simp [frames,Continuation.point,Continuation.words,Prefix.pointFor]
  | own attempt _ => exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨attempt,List.mem_attach _ _,rfl⟩))
  | invoiced attempt _ => exact List.mem_append_right _ (List.mem_map.mpr ⟨attempt,List.mem_attach _ _,rfl⟩)

abbrev Table := Feedback.Residual.Joint.Table cursor.source.val.code (frames scope)
def tables := Feedback.Residual.Joint.tables cursor.source.val.code (frames scope)
abbrev opponent (table : Table scope) := Feedback.Residual.Joint.respond cursor.source.val.code (frames scope) table
abbrev restrict (rival : Opponent cursor.source.val.code) := Feedback.Residual.Joint.restrict cursor.source.val.code (frames scope) rival

theorem restriction_is_generated (rival : Opponent cursor.source.val.code) : restrict scope rival ∈ tables scope :=
  Feedback.Residual.Joint.restriction_is_generated _ _ _

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem forecast_suffix (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
    (schedule : Feedback.Residual.Schedule code) (input : Feedback.Input code) (state : Feedback.State code) (horizon : Nat) :
    forecastWords code schedule input state horizon =
      (Feedback.Residual.run code schedule input state horizon).history.drop state.history.length := by
  rw [forecast_is_the_generated_history_suffix,List.drop_append_of_le_length (Nat.le_refl _),List.drop_length,List.nil_append]

variable (span : Nat)
def target : Intent scope → Opponent cursor.source.val.code → Future.Recovery.SameCodeTarget cursor.model
  | .keep,rival => Planning.target cursor reference rival span
  | .paid term,rival => ⟨(Planning.target term.point term.term rival n).val,rfl⟩
def extent : Intent scope → Nat
  | .keep => span
  | .paid term => n+1+term.words.length
def count : Intent scope → Nat
  | .keep => cursor.count+span
  | .paid term => term.point.count+n

def restoration (source : Future.Recovery.SameCodeTarget cursor.model) (atCount : Nat)
    (word : List (Future.Recovery.Action cursor.model)) :
    Option (Future.Recovery.Assessment.Report cursor.model ×
      Option (Future.Recovery.Funding.Failure cursor.model cursor.depth word)) :=
  match Future.produce cursor.model cursor.depth source.indexed atCount word with
  | .inl _ => none
  | .inr receipt =>
      let made := Future.Recovery.produceWith pricing receipt
      some (Future.Recovery.Assessment.reportFrom made cursor.depth source.property,
        Future.Recovery.Funding.ofWalk made.walk)

def tensor (intent : Intent scope) (rival : Opponent cursor.source.val.code) : Planning.Tensor cursor :=
  let source := target scope span intent rival
  let bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument) :=
    ⟨seed.base,seed.scope,source.val,source.indexed.property.1,source.indexed.property.2⟩
  ⟨source.property ▸ Window.evaluate bound cursor.depth (extent scope span intent),
    restoration (pricing := pricing) source (count scope span intent)⟩

theorem keep_is_the_original_unpaid_tensor (rival : Opponent cursor.source.val.code) :
    tensor scope span .keep rival = Planning.tensor cursor pricing reference rival span := by
  unfold tensor target extent count Planning.tensor Planning.present Planning.restoration Planning.restorationWords restoration
  dsimp only [Planning.candidate,Planning.target,Planning.wordTarget,Cursor.forecast]
  congr 1
  funext word
  split <;> simp_all

private theorem initial_words (term : Term cursor) (rival : Opponent cursor.source.val.code)
    (bounded : span ≤ cursor.state.remaining) :
    forecastWords cursor.source.val.code (schedule cursor term) ⟨opponent scope (restrict scope rival),cursor.input.budget⟩ cursor.state span =
      forecastWords cursor.source.val.code (schedule cursor term) ⟨rival,cursor.input.budget⟩ cursor.state span := by
  have run := Feedback.Residual.Joint.one_table_preserves_each_full_run cursor.source.val.code (frames scope)
    ⟨cursor.state,programs cursor⟩ (by simp [frames]) (schedule cursor term) (schedule_is_generated cursor term)
    ⟨rival,cursor.input.budget⟩ span bounded
  rw [forecast_suffix,forecast_suffix,run]
private theorem paid_words (term : Continuation scope) (rival : Opponent cursor.source.val.code)
    (bounded : n ≤ (comparisonPoint scope).state.remaining) :
    forecastWords cursor.source.val.code (schedule term.point term.term)
        ⟨opponent scope (restrict scope rival),term.point.input.budget⟩ term.point.state n =
      forecastWords cursor.source.val.code (schedule term.point term.term)
        ⟨rival,term.point.input.budget⟩ term.point.state n := by
  have run := Feedback.Residual.Joint.one_table_preserves_each_full_run cursor.source.val.code (frames scope)
    ⟨term.point.state,programs term.point⟩ (every_continuation_frame_is_generated scope term) (schedule term.point term.term)
    (schedule_is_generated term.point term.term) ⟨rival,term.point.input.budget⟩ n bounded
  exact (forecast_suffix _ _ _ _ _).trans ((congrArg (fun state => state.history.drop term.point.state.history.length) run).trans (forecast_suffix _ _ _ _ _).symm)

theorem one_joint_table_preserves_each_own_source (intent : Intent scope)
    (rival : Opponent cursor.source.val.code) (oldBound : span ≤ cursor.state.remaining)
    (paidBound : n ≤ (comparisonPoint scope).state.remaining) :
    target scope span intent (opponent scope (restrict scope rival)) = target scope span intent rival := by
  apply Subtype.ext
  cases intent with
  | keep => exact congrArg cursor.install (initial_words scope span reference rival oldBound)
  | paid term => exact congrArg term.point.install (paid_words scope term rival paidBound)

theorem one_joint_table_preserves_the_whole_initial_cut_tensor (intent : Intent scope)
    (rival : Opponent cursor.source.val.code) (oldBound : span ≤ cursor.state.remaining)
    (paidBound : n ≤ (comparisonPoint scope).state.remaining) :
    tensor scope span intent (opponent scope (restrict scope rival)) = tensor scope span intent rival := by
  unfold tensor
  exact congrArg (fun (source : Future.Recovery.SameCodeTarget cursor.model) =>
    let bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
      ⟨seed.base,seed.scope,source.val,source.indexed.property.1,source.indexed.property.2⟩
    (⟨source.property ▸ Window.evaluate bound cursor.depth (extent scope span intent),
      restoration (pricing := pricing) source (count scope span intent)⟩ : Planning.Tensor cursor))
    (one_joint_table_preserves_each_own_source scope span intent rival oldBound paidBound)

theorem finite_relation_iff_every_same_adaptive_opponent
    (relation : Planning.Tensor cursor → Planning.Tensor cursor → Prop) (first second : Intent scope)
    (oldBound : span ≤ cursor.state.remaining) (paidBound : n ≤ (comparisonPoint scope).state.remaining) :
    (∀ table ∈ tables scope,relation (tensor scope span first (opponent scope table))
      (tensor scope span second (opponent scope table))) ↔
      ∀ rival : Opponent cursor.source.val.code,relation (tensor scope span first rival) (tensor scope span second rival) := by
  constructor
  · intro all rival
    have tested := all (restrict scope rival) (restriction_is_generated scope rival)
    rw [one_joint_table_preserves_the_whole_initial_cut_tensor scope span first rival oldBound paidBound,
      one_joint_table_preserves_the_whole_initial_cut_tensor scope span second rival oldBound paidBound] at tested
    exact tested
  · intro all table _;exact all _

def execute : Intent scope → Cursor seed driver
  | .keep => Planning.execute cursor reference span
  | .paid term => Planning.execute term.point term.term n

theorem execution_is_its_own_evaluated_source (intent : Intent scope) :
    (execute scope span intent).source.val = (target scope span intent cursor.input.opponent).val := by
  cases intent <;> rfl

theorem selected_whole_window_includes_its_actual_payment_prefix (intent : Intent scope) :
    (execute scope span intent).depth = cursor.depth+extent scope span intent := by
  cases intent with
  | keep => exact Cursor.realization_advances_the_actual_depth cursor _ span
  | paid term =>
      rw [execute,Planning.execute,Cursor.realization_advances_the_actual_depth]
      change cursor.source.val.history.length+1+(cursor.count+1+term.words.length)+n = cursor.depth+(n+1+term.words.length)
      dsimp only [Cursor.depth,Machine.Continuation.depth]
      omega
theorem actual_installation_is_the_compared_full_initial_cut_window (intent : Intent scope) :
    HEq (Window.evaluate (execute scope span intent).model cursor.depth
      ((execute scope span intent).depth-cursor.depth))
      (tensor scope span intent cursor.input.opponent).present := by
  have length : (execute scope span intent).depth-cursor.depth = extent scope span intent := by
    rw [selected_whole_window_includes_its_actual_payment_prefix]
    omega
  rw [length]
  cases intent <;> exact HEq.rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole
