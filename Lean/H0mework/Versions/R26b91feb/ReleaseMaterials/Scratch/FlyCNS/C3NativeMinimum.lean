import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PublishedInvocation
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PublishedRoot
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ReachableAutonomous

set_option autoImplicit false
namespace FlyCNS.C3NativeMinimum
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open C3FiniteOccurrence
abbrev Letter : Type := C3ReachableAutonomous.Letter

structure Snapshot (boundary : Boundary) where
  private mk ::
  current : ContentReentryIO.Current boundary.source.material
  latest : Option C3Published.Result
  traces : Vector ByteArray 3

def initial (boundary : Boundary) : Snapshot boundary := ⟨boundary.source.initial,none,boundary.latestTraces⟩
def image {boundary : Boundary} (current : Snapshot boundary) : C3CompleteInventory.Image :=
  ⟨ContentReentryIO.capture current.current,current.traces,C3CompleteInventory.sourceMetadata boundary.source⟩

structure Anchor (boundary : Boundary) where
  private mk ::
  base : Snapshot boundary

def atBoundary (boundary : Boundary) : Anchor boundary := ⟨initial boundary⟩
def fromActual {boundary : Boundary} {before : ContentReentryIO.Current boundary.source.material}
    (event : ContentReentryRoot.GeneratedAt boundary.source before) : Anchor boundary :=
  ⟨⟨event.next,none,⟨#[event.reply.events,event.reply.learning,event.reply.physics],rfl⟩⟩⟩


/-- Same source-owned numerical generation, original private Current parser
and all three original clock guards. Failure is the original source error. -/
def advance {boundary : Boundary} (installed : Installed boundary) (current : Snapshot boundary) :
    Except String (Snapshot boundary) := do
  let generated ← C3PublishedInvocation.generate boundary.source installed.material current.current
  return ⟨generated.after,some generated.published,⟨#[generated.published.numerical.events,generated.published.learning,generated.published.numerical.physics.getD ByteArray.empty],rfl⟩⟩

def selected {boundary : Boundary} (input : Letter) (current : Snapshot boundary) : C3Native.Operation :=
  match input with
  | .inl _ => C3Native.operationAt current.current.visit
  | .inr operation => operation

def effect {boundary : Boundary} (installed : Installed boundary) (input : Letter)
    (state : Except String (Snapshot boundary)) : Except String (Snapshot boundary) := do
  let current ← state
  if C3Native.operationAt current.current.visit≠selected input current then
    .error "operation not admitted at this source incidence"
  else advance installed current

def generate {boundary : Boundary} (installed : Installed boundary) (anchor : Anchor boundary) : Nat → Except String (Snapshot boundary)
  | 0 => .ok anchor.base
  | n+1 => do
    let current ← generate installed anchor n
    advance installed current

def execute {boundary : Boundary} (installed : Installed boundary) : List Letter →
    Except String (Snapshot boundary) → Except String (Snapshot boundary)
  | [],current => current
  | input::rest,current => execute installed rest (effect installed input current)

theorem advance_visit {boundary : Boundary} {installed : Installed boundary} {before after : Snapshot boundary}
    (paid:advance installed before=.ok after) : after.current.visit=before.current.visit+1 := by
  unfold advance at paid
  simp only [bind,pure,Except.bind,Except.pure] at paid
  cases h:C3PublishedInvocation.generate boundary.source installed.material before.current with
  | error why => simp only [h] at paid;contradiction
  | ok generated => simp only [h] at paid;cases paid;exact generated.nextVisit

theorem generated_visit {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} {n : Nat} {current : Snapshot boundary}
    (paid:generate installed anchor n=.ok current) : current.current.visit=anchor.base.current.visit+n := by
  induction n generalizing current with
  | zero => cases paid;rfl
  | succ n previous =>
    simp only [generate,bind,Except.bind] at paid
    cases h:generate installed anchor n with
    | error why => simp only [h] at paid;contradiction
    | ok before =>
      simp only [h] at paid
      have step:=advance_visit paid
      have old:=previous h
      omega

theorem effect_error {boundary : Boundary} (installed : Installed boundary) (input : Letter) (why : String) :
    effect installed input (.error why)=.error why := rfl

theorem execute_error {boundary : Boundary} (installed : Installed boundary) (word : List Letter) (why : String) :
    execute installed word (.error why)=.error why := by
  induction word with
  | nil => rfl
  | cons _ _ previous => exact previous

theorem success_is_autonomous {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    {word : List Letter} {current : Snapshot boundary}
    (paid:execute installed word (.ok anchor.base)=.ok current) :
    generate installed anchor word.length=.ok current := by
  have shifted (word : List Letter) (n : Nat) (before after : Snapshot boundary)
      (old:generate installed anchor n=.ok before) (paid:execute installed word (.ok before)=.ok after) :
      generate installed anchor (n+word.length)=.ok after := by
    induction word generalizing n before with
    | nil => simpa using old.trans paid
    | cons input rest previous =>
      simp only [execute] at paid
      cases step:effect installed input (.ok before) with
      | error why => rw [step,execute_error] at paid;contradiction
      | ok later =>
        rw [step] at paid
        have generated:advance installed before=.ok later := by
          unfold effect at step
          simp only [bind,Except.bind] at step
          split at step
          · contradiction
          · exact step
        have occurred:generate installed anchor (n+1)=.ok later := by
          simp only [generate,old,bind,Except.bind]
          exact generated
        have next:=previous (n+1) later occurred paid
        simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
  simpa only [Nat.zero_add] using shifted word 0 anchor.base current rfl paid

abbrev Outcome (boundary : Boundary) := Except String (Snapshot boundary)
abbrev Carrier (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :=
  {state : Outcome boundary // ∃ word,execute installed word (.ok anchor.base)=state}

def fromWord (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) (word : List Letter) : Carrier boundary installed anchor :=
  ⟨execute installed word (.ok anchor.base),word,rfl⟩

abbrev Key : Type := Nat ⊕ String
def key {boundary : Boundary} : Outcome boundary → Key
  | .ok current => .inl current.current.visit
  | .error why => .inr why

def encode {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (current : Carrier boundary installed anchor) : Key := key current.val

def read {boundary : Boundary} (observer : Fin 69) (state : Outcome boundary) : C3ReachableModel.Output observer := do
  let current ← state
  return C3CompleteInventory.read (C3ReachableModel.reader observer) (image current)

theorem key_injective (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :
    Function.Injective (encode (boundary:=boundary) (installed:=installed) (anchor:=anchor)) := by
  intro left right same
  apply Subtype.ext
  rcases left.property with ⟨lw,lpaid⟩
  rcases right.property with ⟨rw,rpaid⟩
  cases hl:left.val with
  | error why =>
    cases hr:right.val with
    | error other =>
      have equal:why=other := by simpa only [encode,key,hl,hr,Sum.inr.injEq] using same
      exact congrArg (Except.error (α:=Snapshot boundary)) equal
    | ok other => simp only [encode,key,hl,hr,Sum.inr_ne_inl] at same
  | ok first =>
    cases hr:right.val with
    | error why => simp only [encode,key,hl,hr,Sum.inl_ne_inr] at same
    | ok second =>
      rw [hl] at lpaid
      rw [hr] at rpaid
      have a:=success_is_autonomous lpaid
      have b:=success_is_autonomous rpaid
      have va:=generated_visit a
      have vb:=generated_visit b
      have visits:first.current.visit=second.current.visit := by simpa only [encode,key,hl,hr,Sum.inl.injEq] using same
      have lengths:lw.length=rw.length := by omega
      rw [lengths] at a
      exact a.symm.trans b

def decode {boundary : Boundary} (installed : Installed boundary) (anchor : Anchor boundary) : Key → Outcome boundary
  | .inl visit => generate installed anchor (visit-anchor.base.current.visit)
  | .inr why => .error why

theorem decode_encode {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (current : Carrier boundary installed anchor) :
    decode installed anchor (encode current)=current.val := by
  rcases current.property with ⟨word,paid⟩
  cases h:current.val with
  | error why => simp only [decode,encode,key,h]
  | ok value =>
    rw [h] at paid
    have generated:=success_is_autonomous paid
    have visit:=generated_visit generated
    simpa only [decode,encode,key,h,visit,Nat.add_sub_cancel_left] using generated

theorem execute_append {boundary : Boundary} (installed : Installed boundary) (first second : List Letter)
    (current : Outcome boundary) : execute installed (first++second) current=
      execute installed second (execute installed first current) := by
  induction first generalizing current with
  | nil => rfl
  | cons input rest previous => simpa only [List.cons_append,execute] using previous (effect installed input current)

def action {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (input : Letter)
    (current : Carrier boundary installed anchor) : Carrier boundary installed anchor :=
  ⟨effect installed input current.val,by
    rcases current.property with ⟨word,paid⟩
    refine ⟨word++[input],?_⟩
    rw [execute_append,paid]
    rfl⟩

def run {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} :=
  WholeRepresentation.runMap (action (boundary:=boundary) (installed:=installed) (anchor:=anchor))

theorem run_actual {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (word : List Letter)
    (current : Carrier boundary installed anchor) : (run word current).val=execute installed word current.val := by
  induction word generalizing current with
  | nil => rfl
  | cons input rest previous =>
    simp only [run,WholeRepresentation.runMap]
    exact previous (action input current)

def visitKey : Except String Nat → Key
  | .ok visit => .inl visit
  | .error why => .inr why

theorem key_is_original_visit {boundary : Boundary} (current : Outcome boundary) :
    key current=visitKey (read 64 current) := by cases current <;> rfl

theorem minimum_future_kernel {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (left right : Carrier boundary installed anchor) : encode left=encode right ↔
      ∀ word : List Letter,∀ observer : Fin 69,read observer (run word left).val=read observer (run word right).val := by
  constructor
  · intro same
    have equal:=key_injective boundary installed anchor same
    subst right
    intro word observer
    rfl
  · intro same
    have visit:=congrArg visitKey (same [] 64)
    exact (key_is_original_visit left.val).trans (visit.trans (key_is_original_visit right.val).symm)

abbrev Encoded (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :=
  {address : Key // ∃ current : Carrier boundary installed anchor,encode current=address}

def pack {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (current : Carrier boundary installed anchor) : Encoded boundary installed anchor :=
  ⟨encode current,current,rfl⟩

def unpack {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (packed : Encoded boundary installed anchor) : Carrier boundary installed anchor :=
  ⟨decode installed anchor packed.val,by
    rcases packed.property with ⟨current,same⟩
    rw [← same,decode_encode]
    exact current.property⟩

theorem unpack_pack {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (current : Carrier boundary installed anchor) :
    unpack (pack current)=current := Subtype.ext (decode_encode current)

theorem pack_unpack {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (packed : Encoded boundary installed anchor) :
    pack (unpack packed)=packed := by
  rcases packed.property with ⟨current,same⟩
  have equal:pack current=packed := Subtype.ext same
  rw [← equal,unpack_pack]

def encodedAction {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (input : Letter)
    (packed : Encoded boundary installed anchor) : Encoded boundary installed anchor := pack (action input (unpack packed))
def encodedRead {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (observer : Fin 69)
    (packed : Encoded boundary installed anchor) : C3ReachableModel.Output observer := read observer (unpack packed).val

theorem action_commutes {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (input : Letter)
    (current : Carrier boundary installed anchor) : encodedAction input (pack current)=pack (action input current) := by
  rw [encodedAction,unpack_pack]

theorem read_commutes {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (observer : Fin 69)
    (current : Carrier boundary installed anchor) : encodedRead observer (pack current)=read observer current.val := by
  rw [encodedRead,unpack_pack]

theorem all_words_commute {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (word : List Letter)
    (current : Carrier boundary installed anchor) : WholeRepresentation.runMap encodedAction word (pack current)=pack (run word current) := by
  induction word generalizing current with
  | nil => rfl
  | cons input rest previous =>
    simp only [WholeRepresentation.runMap,run]
    rw [action_commutes]
    exact previous (action input current)

theorem all_readers_zero_error {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} (word : List Letter)
    (observer : Fin 69) (current : Carrier boundary installed anchor) :
    encodedRead observer (WholeRepresentation.runMap encodedAction word (pack current))=
      read observer (execute installed word current.val) := by
  rw [all_words_commute,read_commutes,run_actual]

theorem minimal_other_implementations {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} {Candidate : Type}
    (represent : Carrier boundary installed anchor → Candidate)
    (reads : (observer : Fin 69) → Candidate → C3ReachableModel.Output observer)
    (paid : ∀ observer current,reads observer (represent current)=read observer current.val) :
    Function.FactorsThrough (pack (boundary:=boundary) (installed:=installed) (anchor:=anchor)) represent := by
  intro left right equal
  apply congrArg pack
  apply key_injective boundary installed anchor
  change key left.val=key right.val
  rw [key_is_original_visit,key_is_original_visit]
  apply congrArg visitKey
  rw [← paid 64 left,← paid 64 right,equal]

open RepresentationIO
def fromPublished {boundary : Boundary} {installed : Installed boundary}
    {before : ContentReentryIO.Current boundary.source.material}
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before) : Snapshot boundary :=
  ⟨event.original.next,some event.sourceReply.published,
    ⟨#[event.sourceReply.published.numerical.events,event.sourceReply.published.learning,
      event.sourceReply.published.numerical.physics.getD ByteArray.empty],rfl⟩⟩

theorem published_complete {boundary : Boundary} {installed : Installed boundary}
    {before : ContentReentryIO.Current boundary.source.material}
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before) :
    image (fromPublished event)=C3CompleteInventory.fromActual event.original :=
  C3PublishedRoot.same_complete_occurrence event

theorem published_parsed {boundary : Boundary} {installed : Installed boundary}
    {before : ContentReentryIO.Current boundary.source.material}
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before) :
    C3RootSplice.current boundary.source event.sourceReply.published.numerical=.ok event.sourceReply.reply.after := by
  have paid:=event.sourceReply.decoded
  let written:=event.sourceReply.published.numerical.written
  change (do
    if count:written.words.size=59 then
      let rawWords : Vector ByteArray 59 := ⟨written.words,count⟩
      let parsed ← Vector.ofFnM fun i => BodyIO.parseWord (boundary.source.material.layout.get i) (rawWords.get i)
      if backends:written.archives.size=3 then
        let original : Vector ByteArray 3 := ⟨written.archives,backends⟩
        let complete : Vector ByteArray 4 := original++(⟨#[written.sourceDocument],rfl⟩ : Vector ByteArray 1)
        ContentReentryIO.parseCurrentImage boundary.source ⟨parsed.map captureWord,complete,written.header,written.visit⟩
      else .error "pure source writer omitted an original backend"
    else .error "pure source writer omitted an original coordinate")=.ok event.sourceReply.reply.after at paid
  change (do
    if count:written.words.size=59 then
      let rawWords : Vector ByteArray 59 := ⟨written.words,count⟩
      let parsed ← Vector.ofFnM fun i => BodyIO.parseWord (boundary.source.material.layout.get i) (rawWords.get i)
      if backends:written.archives.size=3 then
        let original : Vector ByteArray 3 := ⟨written.archives,backends⟩
        let complete : Vector ByteArray 4 := original++(⟨#[written.sourceDocument],rfl⟩ : Vector ByteArray 1)
        ContentReentryIO.parseCurrentImage boundary.source ⟨parsed.map captureWord,complete,written.header,written.visit⟩
      else .error "the pure source writer omitted an original backend"
    else .error "the pure source writer omitted an original word")=.ok event.sourceReply.reply.after
  by_cases count:written.words.size=59
  · simp only [dif_pos count,bind,Except.bind] at paid ⊢
    cases hp:Vector.ofFnM (fun i : Fin 59 => BodyIO.parseWord (boundary.source.material.layout.get i)
      ((⟨written.words,count⟩ : Vector ByteArray 59).get i)) with
    | error why => simp only [hp] at paid;contradiction
    | ok words =>
      simp only [hp] at paid ⊢
      by_cases backends:written.archives.size=3
      · simp only [dif_pos backends] at paid ⊢
        exact paid
      · simp only [dif_neg backends] at paid;contradiction
  · simp only [dif_neg count] at paid;contradiction

set_option maxHeartbeats 2000000 in
theorem advance_published {boundary : Boundary} {installed : Installed boundary} {before : Snapshot boundary}
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current) :
    advance installed before=.ok (fromPublished event) := by
  have generated:=event.sourceReply.generated
  have parsed:=published_parsed event
  change C3BoundPublication.generate installed.material (C3PublishedInvocation.raw boundary.source before.current)=
    .ok event.sourceReply.published at generated
  have identity : (installed.material.identity.instanceId != boundary.source.material.instanceId ||
      installed.material.identity.occurrenceId != boundary.source.material.occurrenceId ||
      installed.material.identity.installationId != boundary.source.material.installationId)=false := by
    simp [installed.instanceId,installed.occurrenceId,installed.installationId]
  have accepted:∃ result:C3PublishedInvocation.At boundary.source installed.material before.current,
      C3PublishedInvocation.generate boundary.source installed.material before.current=.ok result ∧
      result.published=event.sourceReply.published ∧ result.after=event.sourceReply.reply.after := by
    unfold C3PublishedInvocation.generate
    rw [if_neg (by rw [identity];decide)]
    simp only [pure,Except.pure]
    split
    next why failed =>
      have impossible:=failed.symm.trans generated
      contradiction
    next result generatedHere =>
      have same:result=event.sourceReply.published := Except.ok.inj (generatedHere.symm.trans generated)
      subst result
      split
      next why failed =>
        have impossible:=failed.symm.trans parsed
        contradiction
      next after parsedHere =>
        have same:after=event.sourceReply.reply.after := Except.ok.inj (parsedHere.symm.trans parsed)
        subst after
        simp only [dif_pos event.sourceReply.reply.next_visit,dif_pos event.sourceReply.reply.next_tick,
          dif_pos event.sourceReply.reply.next_physics]
        exact ⟨_,rfl,rfl,rfl⟩
  rcases accepted with ⟨result,paid,samePublished,sameCurrent⟩
  simp only [advance,paid,bind,pure,Except.bind,Except.pure,samePublished,sameCurrent]
  rfl

structure Ready (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) where
  private mk ::
  state : Carrier boundary installed anchor
  current : Snapshot boundary
  same : state.val=.ok current

def ready {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (state : Carrier boundary installed anchor) : Except String (Ready boundary installed anchor) :=
  match same:state.val with
  | .error why => .error why
  | .ok current => .ok ⟨state,current,same⟩

/-- Consume the original emitted occurrence itself. This constructor reads
its already-generated Current and traces; it performs no numerical step. -/
def consumePublished {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (before : Ready boundary installed anchor)
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current.current) :
    Carrier boundary installed anchor :=
  ⟨.ok (fromPublished event),by
    rcases before.state.property with ⟨word,paid⟩
    refine ⟨word++[.inl ()],?_⟩
    rw [execute_append,paid,before.same]
    simp only [execute,effect,selected,ne_eq,not_true_eq_false,if_false,bind,Except.bind]
    exact advance_published event⟩

theorem consumed_same_image {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (before : Ready boundary installed anchor)
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current.current)
    (observer : Fin 69) : read observer (consumePublished before event).val=
      Except.ok (C3CompleteInventory.read (C3ReachableModel.reader observer) (C3CompleteInventory.fromActual event.original)) := by
  simp only [read,consumePublished,bind,pure,Except.bind,Except.pure,published_complete]
  rfl

end FlyCNS.C3NativeMinimum
