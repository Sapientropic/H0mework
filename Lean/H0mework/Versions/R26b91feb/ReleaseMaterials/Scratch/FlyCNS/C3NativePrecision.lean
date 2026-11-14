import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeMinimum
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeByteBound

set_option autoImplicit false
namespace FlyCNS.C3NativePrecision
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open C3FiniteOccurrence C3NativeMinimum

private theorem bind_ok {α β : Type} {source : Except String α} {f : α → Except String β} {after : β}
    (paid : source.bind f=.ok after) : ∃ before,source=.ok before ∧ f before=.ok after := by
  cases source with
  | error why => contradiction
  | ok before => exact ⟨before,rfl,paid⟩

private theorem vector_ofFnM_ok {α : Type} {n : Nat} {source : Fin n → Except String α} {after : Vector α n}
    (paid : Vector.ofFnM source=.ok after) : ∀ index,source index=.ok (after.get index) := by
  induction n with
  | zero => intro index;exact Fin.elim0 index
  | succ n previous =>
    rw [Vector.ofFnM_succ] at paid
    rcases bind_ok paid with ⟨initial,hinitial,rest⟩
    rcases bind_ok rest with ⟨last,hlast,finished⟩
    have equal : initial.push last=after := Except.ok.inj finished
    rw [← equal]
    intro index
    by_cases small:index.val<n
    · have old:=previous hinitial ⟨index.val,small⟩
      have cast : (⟨index.val,small⟩ : Fin n).castSucc=index := Fin.ext rfl
      rw [cast] at old
      change source index=.ok ((initial.push last)[index.val])
      rw [Vector.getElem_push_lt small]
      exact old
    · have atLast:index=Fin.last n := by apply Fin.ext;dsimp only [Fin.val_last];omega
      subst index
      change source (Fin.last n)=.ok ((initial.push last)[n])
      rw [Vector.getElem_push_eq]
      exact hlast

private theorem current_parser_width {source : ContentReentryIO.Source}
    {input : ContentFullPackedIO.Image} {current : ContentReentryIO.Current source.material}
    (paid : ContentReentryIO.parseCurrentImage source input=.ok current) :
    ∀ field,(current.words.get field).vector.width=(source.material.layout.get field).width := by
  unfold ContentReentryIO.parseCurrentImage at paid
  cases encoding:String.fromUTF8? input.header with
  | none => simp only [encoding,bind,Except.bind] at paid;contradiction
  | some header =>
    rw [encoding] at paid
    rcases bind_ok paid with ⟨text,_,parsedText⟩
    rcases bind_ok parsedText with ⟨raw,_,parsedJson⟩
    rcases bind_ok parsedJson with ⟨document,_,checkedDocument⟩
    split at checkedDocument
    · simp only [bind,Except.bind,C3NativeByteBound.throw_error] at checkedDocument;contradiction
    · rcases bind_ok checkedDocument with ⟨words,parsedWords,checkedWords⟩
      rcases bind_ok checkedWords with ⟨_,_,finished⟩
      split at finished
      · split at finished
        · cases finished
          intro field
          exact C3NativeByteBound.word_parser_width (vector_ofFnM_ok parsedWords field)
        · contradiction
      · contradiction

private theorem root_parser_width {source : ContentReentryIO.Source} {result : C3Successful.Result}
    {current : ContentReentryIO.Current source.material}
    (paid : C3RootSplice.current source result=.ok current) :
    ∀ field,(current.words.get field).vector.width=(source.material.layout.get field).width := by
  unfold C3RootSplice.current at paid
  dsimp only at paid
  split at paid
  · rcases bind_ok paid with ⟨words,_,completed⟩
    split at completed
    · exact current_parser_width completed
    · contradiction
  · contradiction

theorem advance_width {boundary : Boundary} {installed : Installed boundary} {before after : Snapshot boundary}
    (paid : advance installed before=.ok after) :
    ∀ field,(after.current.words.get field).vector.width=(boundary.source.material.layout.get field).width := by
  unfold advance at paid
  rcases bind_ok paid with ⟨generated,_,finished⟩
  cases finished
  exact root_parser_width generated.parsed

theorem advance_physics {boundary : Boundary} {installed : Installed boundary} {before after : Snapshot boundary}
    (paid : advance installed before=.ok after) :
    ContentReentryIO.physicsTick boundary.source.material after.current.words=
      ContentReentryIO.physicsTick boundary.source.material before.current.words+
        10*(BodyFullIO.operationAt before.current.visit).microTicks := by
  unfold advance at paid
  rcases bind_ok paid with ⟨generated,_,finished⟩
  cases finished
  exact generated.nextPhysics

def physics {boundary : Boundary} (current : Snapshot boundary) : Nat :=
  ContentReentryIO.physicsTick boundary.source.material current.current.words

def width (boundary : Boundary) (anchor : Anchor boundary) : Nat :=
  let field:=boundary.source.material.addresses.get ⟨34,by decide⟩
  max (anchor.base.current.words.get field).vector.width (boundary.source.material.layout.get field).width

def stateBound (boundary : Boundary) (anchor : Anchor boundary) : Nat :=
  anchor.base.current.visit+256^(width boundary anchor)/1000+3

theorem generated_physics_bound {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    {n : Nat} {current : Snapshot boundary} (paid : generate installed anchor n=.ok current) :
    physics current<256^(width boundary anchor) := by
  cases n with
  | zero =>
    cases paid
    have bounded:=C3NativeByteBound.word_bound
      (ContentReentryIO.wordAt boundary.source.material anchor.base.current.words ⟨34,by decide⟩).vector 0
    apply lt_of_lt_of_le bounded
    dsimp only [width,ContentReentryIO.wordAt]
    gcongr <;> omega
  | succ n =>
    simp only [C3NativeMinimum.generate,bind,Except.bind] at paid
    cases old:generate installed anchor n with
    | error why => simp only [old] at paid;contradiction
    | ok before =>
      simp only [old] at paid
      have widths:=advance_width paid
      have bounded:=C3NativeByteBound.word_bound
        (ContentReentryIO.wordAt boundary.source.material current.current.words ⟨34,by decide⟩).vector 0
      apply lt_of_lt_of_le bounded
      dsimp only [ContentReentryIO.wordAt] at *
      rw [widths]
      dsimp only [width]
      gcongr <;> omega

private theorem clock_step (visit : Nat) :
    (C3Clock.generate (visit+1)).physics=(C3Clock.generate visit).physics+
      10*(BodyFullIO.operationAt visit).microTicks := by
  rw [C3Clock.generate]
  unfold C3Clock.next
  rw [C3Clock.generated_visit]
  by_cases first:visit=55
  · simp only [first,beq_self_eq_true,Bool.true_or,ite_true,BodyFullIO.operationAt,
      BodyFullIO.Operation.microTicks,Nat.mul_zero,Nat.add_zero]
  by_cases second:visit=58
  · simp [second,BodyFullIO.operationAt,BodyFullIO.Operation.microTicks]
  simp [first,second,BodyFullIO.operationAt,BodyFullIO.Operation.microTicks]

theorem generated_physics_conservation {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    {n : Nat} {current : Snapshot boundary} (paid : generate installed anchor n=.ok current) :
    physics current+(C3Clock.generate anchor.base.current.visit).physics=
      physics anchor.base+(C3Clock.generate current.current.visit).physics := by
  induction n generalizing current with
  | zero => cases paid;rfl
  | succ n previous =>
    simp only [C3NativeMinimum.generate,bind,Except.bind] at paid
    cases old:generate installed anchor n with
    | error why => simp only [old] at paid;contradiction
    | ok before =>
      simp only [old] at paid
      have conserved:=previous old
      have physical:=advance_physics paid
      have visit:=advance_visit paid
      have counter:=clock_step before.current.visit
      dsimp only [physics] at conserved ⊢
      rw [visit,counter]
      omega

theorem generated_visit_bound {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    {n : Nat} {current : Snapshot boundary} (paid : generate installed anchor n=.ok current) :
    current.current.visit<stateBound boundary anchor := by
  have bounded:=generated_physics_bound paid
  have conserved:=generated_physics_conservation paid
  have first:=C3Clock.closed_eq_generate anchor.base.current.visit
  have last:=C3Clock.closed_eq_generate current.current.visit
  have gates:C3Clock.gateCount current.current.visit≤2 := by
    unfold C3Clock.gateCount
    split <;> split <;> omega
  rw [← first,← last] at conserved
  dsimp only [C3Clock.closed] at conserved
  unfold stateBound
  omega

theorem carrier_success_bound {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (state : Carrier boundary installed anchor) {current : Snapshot boundary}
    (success : state.val=.ok current) : current.current.visit<stateBound boundary anchor := by
  rcases state.property with ⟨word,paid⟩
  rw [success] at paid
  exact generated_visit_bound (success_is_autonomous paid)

abbrev Key (boundary : Boundary) (anchor : Anchor boundary) := Fin (stateBound boundary anchor) ⊕ String

def forget {boundary : Boundary} {anchor : Anchor boundary} : Key boundary anchor → C3NativeMinimum.Key
  | .inl visit => .inl visit.val
  | .inr why => .inr why

/-- The physical word and original clock guards produce the finite success
address. Error strings are retained verbatim rather than assigned a success address. -/
def encode {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (state : Carrier boundary installed anchor) : Key boundary anchor :=
  match success:state.val with
  | .error why => .inr why
  | .ok current => .inl ⟨current.current.visit,carrier_success_bound state success⟩

theorem forget_encode {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (state : Carrier boundary installed anchor) : forget (encode state)=C3NativeMinimum.encode state := by
  unfold encode
  split <;> simp_all only [forget,C3NativeMinimum.encode,key]

theorem finite_key_injective {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} :
    Function.Injective (encode (boundary:=boundary) (installed:=installed) (anchor:=anchor)) := by
  intro left right equal
  apply key_injective boundary installed anchor
  have retained:=congrArg forget equal
  simpa only [forget_encode] using retained

abbrev Encoded (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :=
  {address : Key boundary anchor // ∃ current : Carrier boundary installed anchor,encode current=address}

def pack {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (state : Carrier boundary installed anchor) : Encoded boundary installed anchor := ⟨encode state,state,rfl⟩

def unpack {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (packed : Encoded boundary installed anchor) : Carrier boundary installed anchor :=
  ⟨decode installed anchor (forget packed.val),by
    rcases packed.property with ⟨state,same⟩
    rw [← same,forget_encode,decode_encode]
    exact state.property⟩

theorem unpack_pack {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (state : Carrier boundary installed anchor) : unpack (pack state)=state := by
  apply Subtype.ext
  exact (congrArg (decode installed anchor) (forget_encode state)).trans (decode_encode state)

theorem pack_unpack {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (packed : Encoded boundary installed anchor) : pack (unpack packed)=packed := by
  rcases packed.property with ⟨state,same⟩
  have equal:pack state=packed := Subtype.ext same
  rw [← equal,unpack_pack]

def action {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (input : Letter) (packed : Encoded boundary installed anchor) : Encoded boundary installed anchor :=
  pack (C3NativeMinimum.action input (unpack packed))

def read {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (observer : Fin 69) (packed : Encoded boundary installed anchor) : C3ReachableModel.Output observer :=
  C3NativeMinimum.read observer (unpack packed).val

theorem action_commutes {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (input : Letter) (state : Carrier boundary installed anchor) :
    action input (pack state)=pack (C3NativeMinimum.action input state) := by
  rw [action,unpack_pack]

theorem read_commutes {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (observer : Fin 69) (state : Carrier boundary installed anchor) :
    read observer (pack state)=C3NativeMinimum.read observer state.val := by
  rw [read,unpack_pack]

theorem all_words_commute {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (word : List Letter) (state : Carrier boundary installed anchor) :
    WholeRepresentation.runMap action word (pack state)=pack (run word state) := by
  induction word generalizing state with
  | nil => rfl
  | cons input rest previous =>
    simp only [WholeRepresentation.runMap,run]
    rw [action_commutes]
    exact previous (C3NativeMinimum.action input state)

theorem all_readers_zero_error {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (word : List Letter) (observer : Fin 69) (state : Carrier boundary installed anchor) :
    read observer (WholeRepresentation.runMap action word (pack state))=
      C3NativeMinimum.read observer (execute installed word state.val) := by
  rw [all_words_commute,read_commutes,run_actual]

theorem minimum_future_kernel {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (left right : Carrier boundary installed anchor) : encode left=encode right ↔
    ∀ word : List Letter,∀ observer : Fin 69,
      C3NativeMinimum.read observer (run word left).val=C3NativeMinimum.read observer (run word right).val := by
  constructor
  · intro same
    have equal:=finite_key_injective same
    subst right
    intro word observer
    rfl
  · intro same
    have equal:=key_injective boundary installed anchor (C3NativeMinimum.minimum_future_kernel left right |>.mpr same)
    subst right
    rfl

theorem minimal_other_implementations {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    {Candidate : Type} (represent : Carrier boundary installed anchor → Candidate)
    (reads : (observer : Fin 69) → Candidate → C3ReachableModel.Output observer)
    (paid : ∀ observer current,reads observer (represent current)=C3NativeMinimum.read observer current.val) :
    Function.FactorsThrough (pack (boundary:=boundary) (installed:=installed) (anchor:=anchor)) represent := by
  intro left right equal
  apply congrArg pack
  apply key_injective boundary installed anchor
  change key left.val=key right.val
  rw [key_is_original_visit,key_is_original_visit]
  apply congrArg visitKey
  rw [← paid 64 left,← paid 64 right,equal]

/-- Pack the same emitted original event; the finite address consumer performs
no second numerical step or source recovery. -/
def consumePublished {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (before : Ready boundary installed anchor)
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current.current) :
    Encoded boundary installed anchor := pack (C3NativeMinimum.consumePublished before event)

theorem consumed_same_image {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (before : Ready boundary installed anchor)
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current.current)
    (observer : Fin 69) : read observer (consumePublished before event)=
    Except.ok (C3CompleteInventory.read (C3ReachableModel.reader observer)
      (C3CompleteInventory.fromActual event.original)) := by
  rw [consumePublished,read_commutes]
  exact C3NativeMinimum.consumed_same_image before event observer

end FlyCNS.C3NativePrecision
