import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

structure Input where
  actor : Party
  position : Nat
  units : List Nat
  horizon : Nat
  budget : Nat
  pricing : Future.Recovery.Pricing (Future.Recovery.Action seed)
  future : Nat
  span : Nat
  site : Fin seed.source.code.sites
  reading : Fin seed.source.code.signals

variable {seed} (input : Input seed)
abbrev NativePoint := Point seed input.actor input.units input.horizon input.budget
abbrev initial (point : NativePoint input) := point.native (position := input.position)
abbrev reference (point : NativePoint input) := Planning.baseline (initial input point)

inductive ReservationFailure (point : NativePoint input) where
  | unpriced (scope : Scope (initial input point) input.pricing input.future (reference input point) input.actor input.position)
      (units : Nat) (absent : Prefix.quote (paidPoint scope) input.actor input.position scope.continuation.words units = none)
  | refused (scope : Scope (initial input point) input.pricing input.future (reference input point) input.actor input.position)
      (bill : Prefix.Bill (paidPoint scope) input.actor input.position)
      (before : bill.before = scope.continuation.words) (unpaid : bill.payment.succeeded = false)

def ReservationFailure.retained {point : NativePoint input} : ReservationFailure input point →
    Scope (initial input point) input.pricing input.future (reference input point) input.actor input.position
  | .unpriced scope .. => scope
  | .refused scope bill before _ => Whole.extend scope bill before

inductive Recipe where
  | initial
  | reserved (prior : Recipe) (units : Nat)

inductive Stage (point : NativePoint input) where
  | stopped (header : Prepaid.Protocol (initial input point) input.pricing input.future (reference input point) input.actor input.position)
  | ready (scope : Scope (initial input point) input.pricing input.future (reference input point) input.actor input.position)
  | blocked (failure : ReservationFailure input point)

def prepareStage (point : NativePoint input) : Stage input point :=
  match Whole.prepare (initial input point) input.pricing input.future (reference input point) input.actor input.position with
  | .inl header => .stopped header
  | .inr scope => .ready (withOwnInvoices scope
      (Production.invoiceQuotations (initial input point) input.pricing input.future (reference input point)
        input.actor input.position scope input.span))

/-- Every reservation appends its actual Replay output before any new comparison. -/
def reserveStage (units : Nat) {point : NativePoint input} : Stage input point → Stage input point
  | .stopped header => .stopped header
  | .blocked failure => .blocked failure
  | .ready scope =>
    match quoted : Prefix.quote (paidPoint scope) input.actor input.position scope.continuation.words units with
    | none => .blocked (.unpriced scope units quoted)
    | some bill =>
      if paid : bill.val.payment.succeeded = true then
        let actual := Whole.extend scope bill.val bill.property.1
        .ready (withOwnInvoices actual
          (Production.invoiceQuotations (initial input point) input.pricing input.future (reference input point)
            input.actor input.position actual input.span))
      else .blocked (.refused scope bill.val bill.property.1 (Bool.eq_false_iff.mpr paid))

def stageFor : Recipe → (point : NativePoint input) → Stage input point
  | .initial,point => prepareStage input point
  | .reserved prior units,point => reserveStage input units (stageFor prior point)

structure Cell where
  private mk ::
  point : NativePoint input
  original : point ∈ fiber seed input.actor input.position input.units input.horizon input.budget input.site input.reading
  recipe : Recipe
  stage : Stage input point
  generated : stage = stageFor input recipe point

def reserveCell (units : Nat) (cell : Cell input) : Cell input :=
  ⟨cell.point,cell.original,.reserved cell.recipe units,reserveStage input units cell.stage,by
    dsimp only [stageFor];rw [cell.generated]⟩

def cellsFor : Recipe → List (Cell input)
  | .initial => (fiber seed input.actor input.position input.units input.horizon input.budget input.site input.reading).attach.map
      (fun point => ⟨point.val,point.property,.initial,prepareStage input point.val,rfl⟩)
  | .reserved prior units => (cellsFor prior).map (reserveCell input units)

abbrev cells := cellsFor input .initial

structure Prepared where
  private mk ::
  recipe : Recipe
  saved : List (Cell input)
  generated : saved = cellsFor input recipe

def prepare : Prepared input := ⟨.initial,cells input,rfl⟩

def reserve (prepared : Prepared input) (units : Nat) : Prepared input :=
  ⟨.reserved prepared.recipe units,prepared.saved.map (reserveCell input units),by rw [prepared.generated];rfl⟩

theorem cellsFor_preserves_every_original_point (recipe : Recipe) :
    (cellsFor input recipe).map Cell.point =
      (fiber seed input.actor input.position input.units input.horizon input.budget input.site input.reading).attach.map Subtype.val := by
  induction recipe with
  | initial => simp only [cellsFor,List.map_map,Function.comp_def]
  | reserved prior units ih =>
    simpa only [cellsFor,List.map_map,Function.comp_def,reserveCell] using ih


abbrev Raw := RawEvent Party Good Port (Mandate.State Party Technology) Instrument
inductive Signature (Action : Type) where
  | keep (header : List Action)
  | direct (header : List Action) (control : List (Option (List (List Action))))
  | own (header requested : List Action) (control : List (Option (List (List Action))))
  | invoiced (header requested : List Action) (invoice : Option (List Action)) (control : List (Option (List (List Action))))
  | stopped (requested : Option (List Action))
  | prefix (committed : List (List Action)) (next : Signature Action)
  deriving DecidableEq

abbrev Shape := Signature (Future.Recovery.Action seed)
private def encodeControl {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
    (term : List (Option code.Policy)) : List (Option (List (Raw (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))) :=
  term.map (Option.map (fun policy => code.keys.attach.map (fun key => policy key.val key.property)))

variable {input} {point : NativePoint input}
def Local : Stage input point → Type
  | .stopped _ | .blocked _ => Unit
  | .ready scope => Intent scope

def moves : (stage : Stage input point) → List (Local stage)
  | .stopped _ | .blocked _ => [()]
  | .ready scope => intents scope

theorem every_local_term_is_generated (stage : Stage input point) (term : Local stage) : term ∈ moves stage := by
  cases stage with
  | stopped header => cases term;exact List.mem_cons_self
  | blocked failure => cases term;exact List.mem_cons_self
  | ready scope => exact every_intent_is_generated scope term

private def stoppedRequest (point : NativePoint input)
    (header : Prepaid.Protocol (initial input point) input.pricing input.future (reference input point) input.actor input.position) :
    Option (List (Future.Recovery.Action seed)) :=
  match header.result with
  | .unpriced _ => none
  | .refused fee .. | .shortfall fee .. | .ready fee .. =>
    some (Prepaid.invoice (initial input point) input.pricing input.future fee)

private def unprefixedShape : (stage : Stage input point) → Local stage → Signature (Future.Recovery.Action seed)
  | .stopped header,_ => .stopped (stoppedRequest _ header)
  | .blocked failure,_ => .stopped (some failure.retained.paidWord)
  | .ready scope,.keep => .keep (Prepaid.invoice _ input.pricing input.future scope.fee)
  | .ready scope,.paid (.control term) =>
    .direct (Prepaid.invoice _ input.pricing input.future scope.fee) (encodeControl term.val)
  | .ready scope,.paid (.own own term) =>
    .own (Prepaid.invoice _ input.pricing input.future scope.fee) own.val.requested (encodeControl term.val)
  | .ready scope,.paid (.invoiced invoice term) =>
    .invoiced (Prepaid.invoice _ input.pricing input.future scope.fee) invoice.val.own.requested
      (invoice.val.quoted.map (fun bill => [Prepaid.scaled _ bill.val.fee bill.val.units])) (encodeControl term.val)

def attachPrefix (committed : List (List (Future.Recovery.Action seed)))
    (next : Shape (seed := seed)) : Shape (seed := seed) :=
  if committed = [] then next else .prefix committed next

def shape : (stage : Stage input point) → Local stage → Shape (seed := seed)
  | .ready scope,term => attachPrefix scope.continuation.words (unprefixedShape (.ready scope) term)
  | .stopped header,term => unprefixedShape (.stopped header) term
  | .blocked failure,term => attachPrefix failure.retained.continuation.words (unprefixedShape (.blocked failure) term)

def localNoWorse (stage : Stage input point) : Local stage → Local stage → Prop :=
  match stage with
  | .stopped _ | .blocked _ => fun _ _ => False
  | .ready scope => fun new previous => Decision.NoWorse scope input.span new previous
instance (stage : Stage input point) (new previous : Local stage) : Decidable (localNoWorse stage new previous) := by
  cases stage with
  | stopped header => exact isFalse (fun h => h)
  | blocked failure => exact isFalse (fun h => h)
  | ready scope =>
    change Decidable (Decision.NoWorse scope input.span new previous)
    unfold Decision.NoWorse
    refine @instDecidableAnd _ _ ?_ ?_
    · unfold Deployable
      split
      · cases new with
        | keep => infer_instance
        | paid plan => cases plan <;> infer_instance
      · infer_instance
    · infer_instance

def localBenefit (stage : Stage input point) : Local stage → Local stage → Prop :=
  match stage with
  | .stopped _ | .blocked _ => fun _ _ => True
  | .ready scope => fun new previous => Decision.Benefit scope input.span new previous
instance (stage : Stage input point) (new previous : Local stage) : Decidable (localBenefit stage new previous) := by
  cases stage with
  | stopped header => exact isTrue trivial
  | blocked failure => exact isTrue trivial
  | ready scope =>
    change Decidable (Decision.Benefit scope input.span new previous)
    unfold Decision.Benefit
    infer_instance

theorem localBenefit_refl (stage : Stage input point) (term : Local stage) : localBenefit stage term term := by
  cases stage with
  | stopped _ => trivial
  | blocked _ => trivial
  | ready scope => intro table inside;exact benefit_refl _ _
theorem localBenefit_trans (stage : Stage input point) {a b c : Local stage}
    (ab : localBenefit stage a b) (bc : localBenefit stage b c) : localBenefit stage a c := by
  cases stage with
  | stopped _ => trivial
  | blocked _ => trivial
  | ready scope => intro table inside;exact benefit_trans _ (ab table inside) (bc table inside)
theorem localNoWorse_trans (stage : Stage input point) {a b c : Local stage}
    (ab : localNoWorse stage a b) (bc : localNoWorse stage b c) : localNoWorse stage a c := by
  cases stage with
  | stopped _ => exact ab.elim
  | blocked _ => exact ab.elim
  | ready scope => exact Decision.noWorse_trans scope input.span ab bc

theorem localNoWorse_bounds_benefit (stage : Stage input point) {a b : Local stage}
    (accepted : localNoWorse stage a b) : localBenefit stage a b := by
  cases stage with
  | stopped _ => exact accepted.elim
  | blocked _ => exact accepted.elim
  | ready scope => exact Decision.no_worse_bounds_real_benefit scope input.span accepted

def localBaseline : (stage : Stage input point) → Local stage
  | .stopped _ | .blocked _ => ()
  | .ready _ => .keep

def LocalRow : Stage input point → Type
  | .stopped _ | .blocked _ => Unit
  | .ready scope => Decision.Row scope

def localRows : (stage : Stage input point) → List (LocalRow stage)
  | .stopped _ | .blocked _ => [()]
  | .ready scope => Decision.rows scope

def localHolds (stage : Stage input point) : Local stage → Local stage → LocalRow stage → Prop :=
  match stage with
  | .stopped _ | .blocked _ => fun _ _ _ => False
  | .ready scope => fun previous new row => Decision.Holds scope input.span previous new row
instance (stage : Stage input point) (previous new : Local stage) (row : LocalRow stage) :
    Decidable (localHolds stage previous new row) := by
  cases stage with
  | stopped _ => exact isFalse (fun h => h)
  | blocked _ => exact isFalse (fun h => h)
  | ready scope =>
    change Decidable (Decision.Holds scope input.span previous new row)
    cases row <;> dsimp only [Decision.Holds]
    · unfold Deployable
      split
      · cases new with
        | keep => infer_instance
        | paid plan => cases plan <;> infer_instance
      · infer_instance
    · infer_instance
    · infer_instance
    · infer_instance

theorem local_rows_iff (stage : Stage input point) (new previous : Local stage) :
    (∀ row ∈ localRows stage, localHolds stage previous new row) ↔ localNoWorse stage new previous := by
  cases stage with
  | stopped _ =>
    constructor
    · intro all;exact all () List.mem_cons_self
    · intro impossible;exact impossible.elim
  | blocked _ =>
    constructor
    · intro all;exact all () List.mem_cons_self
    · intro impossible;exact impossible.elim
  | ready scope => exact Decision.rows_iff scope input.span previous new

variable (prepared : Prepared input)
abbrev Index := Fin prepared.saved.length
abbrev keys := List.finRange prepared.saved.length
abbrev Section := ∀ index ∈ keys prepared, Local prepared.saved[index].stage
abbrev readTerm (policy : Section prepared) (index : Index prepared) := policy index (List.mem_finRange index)
def sections : List (Section prepared) := List.pi (keys prepared) (fun index => moves prepared.saved[index].stage)

theorem every_section_is_generated (policy : Section prepared) : policy ∈ sections prepared := by
  apply (List.mem_pi _ _).mpr
  intro index inside
  exact every_local_term_is_generated _ _

def Coherent (policy : Section prepared) : Prop :=
  ∀ first second : Index prepared, shape prepared.saved[first].stage (readTerm prepared policy first) =
    shape prepared.saved[second].stage (readTerm prepared policy second)
instance (policy : Section prepared) : Decidable (Coherent prepared policy) := by unfold Coherent;infer_instance

def NoWorse (new previous : Section prepared) : Prop :=
  prepared.saved ≠ [] ∧ Coherent prepared new ∧
    ∀ index : Index prepared, localNoWorse prepared.saved[index].stage (readTerm prepared new index) (readTerm prepared previous index)
instance (new previous : Section prepared) : Decidable (NoWorse prepared new previous) := by unfold NoWorse;infer_instance

def Benefit (new previous : Section prepared) : Prop :=
  ∀ index : Index prepared, localBenefit prepared.saved[index].stage (readTerm prepared new index) (readTerm prepared previous index)
instance (new previous : Section prepared) : Decidable (Benefit prepared new previous) := by unfold Benefit;infer_instance

theorem noWorse_trans {first middle last : Section prepared}
    (left : NoWorse prepared first middle) (right : NoWorse prepared middle last) : NoWorse prepared first last :=
  ⟨left.1,left.2.1,fun index => localNoWorse_trans _ (left.2.2 index) (right.2.2 index)⟩
theorem noWorse_bounds_benefit {new previous : Section prepared}
    (accepted : NoWorse prepared new previous) : Benefit prepared new previous :=
  fun index => localNoWorse_bounds_benefit _ (accepted.2.2 index)

abbrev Axis := Index prepared × Section prepared
def axes : List (Axis prepared) := (keys prepared).flatMap fun index => (sections prepared).map (index,·)
def cost (policy : Section prepared) (axis : Axis prepared) : ℚ :=
  if localBenefit prepared.saved[axis.1].stage (readTerm prepared policy axis.1) (readTerm prepared axis.2 axis.1) then 0 else 1

theorem vector_iff (new previous : Section prepared) :
    Distributed.NoWorse (axes prepared) (cost prepared) new previous ↔ Benefit prepared new previous := by
  constructor
  · intro vector index
    have tested := vector (index,previous) (List.mem_flatMap.mpr ⟨index,List.mem_finRange _,
      List.mem_map.mpr ⟨previous,every_section_is_generated prepared previous,rfl⟩⟩)
    have self := localBenefit_refl prepared.saved[index].stage (readTerm prepared previous index)
    by_contra failed
    simp only [cost,if_pos self,if_neg failed] at tested
    norm_num at tested
  · intro all axis inside
    obtain ⟨index,_,mapped⟩ := List.mem_flatMap.mp inside
    obtain ⟨probe,_,same⟩ := List.mem_map.mp mapped
    subst axis
    by_cases old : localBenefit prepared.saved[index].stage (readTerm prepared previous index) (readTerm prepared probe index)
    · have now := localBenefit_trans _ (all index) old
      simp only [cost,if_pos old,if_pos now,le_refl]
    · simp only [cost,if_neg old]
      split <;> norm_num

def baseline : Section prepared := fun index _ => localBaseline prepared.saved[index].stage

theorem every_original_local_branch_has_a_generated_section
    (index : Index prepared) (term : Local prepared.saved[index].stage) :
    ∃ policy ∈ sections prepared, readTerm prepared policy index = term := by
  let policy : Section prepared := fun other _ =>
    if same : other = index then same.symm ▸ term else localBaseline prepared.saved[other].stage
  refine ⟨policy,every_section_is_generated prepared policy,?_⟩
  simp only [readTerm,policy,dif_pos rfl]

inductive Row where
  | informed
  | coherence (first second : Index prepared)
  | native (index : Index prepared) (row : LocalRow prepared.saved[index].stage)

def rows : List (Row prepared) := [.informed] ++
  (keys prepared).flatMap (fun first => (keys prepared).map (.coherence first)) ++
  (keys prepared).flatMap (fun index => (localRows prepared.saved[index].stage).map (.native index))

def Holds (reference term : Section prepared) : Row prepared → Prop
  | .informed => prepared.saved ≠ []
  | .coherence first second => shape prepared.saved[first].stage (readTerm prepared term first) =
      shape prepared.saved[second].stage (readTerm prepared term second)
  | .native index row => localHolds prepared.saved[index].stage
      (readTerm prepared reference index) (readTerm prepared term index) row
instance (reference term : Section prepared) (row : Row prepared) : Decidable (Holds prepared reference term row) := by
  cases row <;> unfold Holds <;> infer_instance

theorem rows_iff (reference term : Section prepared) :
    (∀ row ∈ rows prepared, Holds prepared reference term row) ↔ NoWorse prepared term reference := by
  constructor
  · intro all
    refine ⟨all .informed (by simp [rows]),?_,?_⟩
    · intro first second
      exact all (.coherence first second) (by simp [rows])
    · intro index
      apply (local_rows_iff _ _ _).mp
      intro row inside
      exact all (.native index row) (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨index,List.mem_finRange _,List.mem_map.mpr ⟨row,inside,rfl⟩⟩))
  · rintro ⟨informed,coherent,accepted⟩ row inside
    cases row with
    | informed => exact informed
    | coherence first second => exact coherent first second
    | native index coordinate =>
      simp only [rows,List.mem_append,List.mem_singleton,List.mem_flatMap,List.mem_map] at inside
      rcases inside with (impossible | ⟨first,_,second,_,impossible⟩) | ⟨other,_,localRow,member,same⟩
      · cases impossible
      · cases impossible
      · have known : Holds prepared reference term (.native other localRow) :=
          (local_rows_iff _ _ _).mpr (accepted other) localRow member
        exact same ▸ known

def Better (previous new : Section prepared) : Prop := NoWorse prepared new previous ∧ ¬ Benefit prepared previous new
structure Candidate (reference : Section prepared) where
  term : Section prepared
  accepted : NoWorse prepared term reference

def check (reference term : Section prepared) : Option (Candidate prepared reference) :=
  if accepted : NoWorse prepared term reference then some ⟨term,accepted⟩ else none

def candidates (reference : Section prepared) := (sections prepared).filterMap (check prepared reference)
theorem every_accepted_section_is_generated (reference term : Section prepared) (valid : NoWorse prepared term reference) :
    ∃ candidate ∈ candidates prepared reference, candidate.term = term := by
  exact ⟨⟨term,valid⟩,List.mem_filterMap.mpr ⟨term,every_section_is_generated prepared term,by simp [check,valid]⟩,rfl⟩

abbrev Choice (reference : Section prepared) :=
  Selected (axes prepared) (fun candidate : Candidate prepared reference => cost prepared candidate.term)
    (candidates prepared reference)

def select (reference : Section prepared) : Option (Choice prepared reference) :=
  Distributed.choose (axes prepared) (fun candidate => cost prepared candidate.term) (candidates prepared reference)

theorem selected_has_no_full_domain_responsibility_dominator (reference : Section prepared)
    (choice : Choice prepared reference) (other : Section prepared) : ¬ Better prepared choice.policy.term other := by
  intro improves
  obtain ⟨candidate,member,same⟩ := every_accepted_section_is_generated prepared reference other
    (noWorse_trans prepared improves.1 choice.policy.accepted)
  apply choice.maximal candidate member
  change Improves (axes prepared) (cost prepared) choice.policy.term candidate.term
  rw [same]
  exact ⟨(vector_iff prepared _ _).mpr (noWorse_bounds_benefit prepared improves.1),
    fun reverse => improves.2 ((vector_iff prepared _ _).mp reverse)⟩

theorem every_available_uniform_real_improvement_is_selected (reference : Section prepared)
    (choice : Choice prepared reference) (available : ∃ other : Section prepared, Better prepared reference other) :
    Better prepared reference choice.policy.term := by
  refine ⟨choice.policy.accepted,?_⟩
  intro reverse
  obtain ⟨other,improves⟩ := available
  obtain ⟨candidate,member,same⟩ := every_accepted_section_is_generated prepared reference other improves.1
  apply choice.maximal candidate member
  change Improves (axes prepared) (cost prepared) choice.policy.term candidate.term
  rw [same]
  refine ⟨(vector_iff prepared _ _).mpr (fun index => localBenefit_trans _
    (noWorse_bounds_benefit prepared improves.1 index) (reverse index)),?_⟩
  intro backwards
  exact improves.2 (fun index => localBenefit_trans _ (reverse index) ((vector_iff prepared _ _).mp backwards index))

structure Rejection (reference term : Section prepared) where
  row : Row prepared
  original : row ∈ rows prepared
  broken : ¬ Holds prepared reference term row

inductive Outcome (reference : Section prepared) where
  | selected (choice : Choice prepared reference)
  | blocked (rejected : ∀ term : Section prepared, Rejection prepared reference term)

def compile (reference : Section prepared) : Outcome prepared reference :=
  match result : select prepared reference with
  | some choice => .selected choice
  | none => .blocked (fun term => match Distributed.inspect (Holds prepared reference term) (rows prepared) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted all => False.elim (by
        have empty := (Distributed.choose_none_iff_empty _ _ _).mp result
        obtain ⟨candidate,member,_⟩ := every_accepted_section_is_generated prepared reference term
          ((rows_iff prepared reference term).mp all)
        rw [empty] at member
        exact List.not_mem_nil member))

def verify (reference term : Section prepared) : Bool := decide (
  NoWorse prepared term reference ∧ ∀ other ∈ sections prepared,
    NoWorse prepared other reference → ¬ Improves (axes prepared) (cost prepared) term other)

theorem independent_replay_accepts_the_public_selection (reference : Section prepared)
    (choice : Choice prepared reference) : verify prepared reference choice.policy.term = true := by
  apply decide_eq_true
  refine ⟨choice.policy.accepted,?_⟩
  intro other _ accepted
  obtain ⟨candidate,member,same⟩ := every_accepted_section_is_generated prepared reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes prepared) (cost prepared) choice.policy.term candidate.term at maximal
  simpa only [same] using maximal

theorem independently_checked_planners_satisfy_the_same_contract
    (reference term : Section prepared) (checked : verify prepared reference term = true) :
    NoWorse prepared term reference ∧ ∀ other : Section prepared,
      NoWorse prepared other reference → ¬ Improves (axes prepared) (cost prepared) term other := by
  have all := of_decide_eq_true checked
  exact ⟨all.1,fun other accepted => all.2 other (every_section_is_generated prepared other) accepted⟩

theorem all_actual_native_representatives_of_the_selected_policy_have_the_same_request_signature
    (reference : Section prepared) (choice : Choice prepared reference) (first second : Index prepared) :
    shape prepared.saved[first].stage (readTerm prepared choice.policy.term first) =
      shape prepared.saved[second].stage (readTerm prepared choice.policy.term second) :=
  choice.policy.accepted.2.1 first second

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy


namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O]
  [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed}

private def canonicalCell (recipe : Recipe) (point : NativePoint input)
    (original : point ∈ fiber seed input.actor input.position input.units input.horizon input.budget input.site input.reading) :
    Cell input := ⟨point,original,recipe,stageFor input recipe point,rfl⟩

private theorem cellsFor_canonical (recipe : Recipe) : cellsFor input recipe =
    (fiber seed input.actor input.position input.units input.horizon input.budget input.site input.reading).attach.map
      (fun point => canonicalCell recipe point.val point.property) := by
  induction recipe with
  | initial => rfl
  | reserved prior units ih =>
      rw [cellsFor,ih,List.map_map]
      rfl

private def rebaseCell (recipe : Recipe) (cell : Cell input) : Cell input :=
  canonicalCell recipe cell.point cell.original

private theorem rebase_all_cells (recipe prior : Recipe) :
    (cellsFor input prior).map (rebaseCell recipe) = cellsFor input recipe := by
  rw [cellsFor_canonical,cellsFor_canonical,List.map_map]
  rfl

/-- Consume already generated stages. The equality is a transport obligation,
not an instruction to repeat preparation, quoting or payment. -/
def Prepared.installCached (prepared : Prepared input) (recipe : Recipe)
    (result : (index : Index prepared) → Stage input prepared.saved[index].point)
    (aligned : ∀ index,result index = stageFor input recipe prepared.saved[index].point) : Prepared input :=
  let saved : List (Cell input) := List.ofFn fun index : Index prepared =>
    ⟨prepared.saved[index].point,prepared.saved[index].original,recipe,result index,aligned index⟩
  ⟨recipe,saved,by
    have generated : saved = prepared.saved.map (rebaseCell recipe) := by
      calc
        saved = List.ofFn (fun index : Index prepared => rebaseCell recipe prepared.saved[index]) := by
          apply congrArg List.ofFn
          funext index
          dsimp only [rebaseCell,canonicalCell]
          simp only [aligned]
        _ = prepared.saved.map (rebaseCell recipe) := by
          simpa only [List.map_ofFn,Function.comp_def,Fin.getElem_fin] using
            congrArg (List.map (rebaseCell recipe)) (List.ofFn_getElem (xs := prepared.saved))
    rw [generated,prepared.generated]
    exact rebase_all_cells recipe prepared.recipe⟩

theorem Prepared.cached_installation_preserves_source_order (prepared : Prepared input) (recipe : Recipe)
    (result : (index : Index prepared) → Stage input prepared.saved[index].point)
    (aligned : ∀ index,result index = stageFor input recipe prepared.saved[index].point) :
    (prepared.installCached recipe result aligned).saved.map Cell.point = prepared.saved.map Cell.point := by
  change (List.ofFn _).map Cell.point = _
  simpa only [List.map_ofFn,Function.comp_def,Fin.getElem_fin] using
    congrArg (List.map Cell.point) (List.ofFn_getElem (xs := prepared.saved))

theorem Prepared.original_cell_stage (prepared : Prepared input) (index : Index prepared) :
    prepared.saved[index].stage = stageFor input prepared.recipe prepared.saved[index].point := by
  have all : ∀ cell ∈ cellsFor input prepared.recipe,cell.stage = stageFor input prepared.recipe cell.point := by
    intro cell inside
    rw [cellsFor_canonical] at inside
    obtain ⟨point,inside,same⟩ := List.mem_map.mp inside
    subst cell
    rfl
  apply all
  rw [←prepared.generated]
  exact List.getElem_mem _

theorem Prepared.cached_stage_is_installed (prepared : Prepared input) (recipe : Recipe)
    (result : (index : Index prepared) → Stage input prepared.saved[index].point)
    (aligned : ∀ index,result index = stageFor input recipe prepared.saved[index].point) (index : Index prepared) :
    ∃ cell ∈ (prepared.installCached recipe result aligned).saved,
      cell.point = prepared.saved[index].point ∧ HEq cell.stage (result index) := by
  refine ⟨⟨prepared.saved[index].point,prepared.saved[index].original,recipe,result index,aligned index⟩,?_,rfl,HEq.rfl⟩
  change _ ∈ List.ofFn _
  exact List.mem_ofFn.mpr ⟨index,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
