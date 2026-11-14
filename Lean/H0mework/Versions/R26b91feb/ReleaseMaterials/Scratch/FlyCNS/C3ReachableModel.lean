import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3FiniteOccurrence

set_option autoImplicit false
namespace FlyCNS.C3ReachableModel
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open C3FiniteOccurrence

def letter (index : Fin 3) : C3Native.Operation :=
  match index.val with | 0 => .neural | 1 => .damage | _ => .repair

def letterIndex : C3Native.Operation → Fin 3
  | .neural => 0 | .damage => 1 | .repair => 2

theorem letter_index (operation : C3Native.Operation) : letter (letterIndex operation)=operation := by
  cases operation <;> rfl

/-- Exactly the original whole-image inventory: 59 words, four archives,
literal header, Nat visit, three latest traces and complete source material. -/
def reader (index : Fin 69) : C3CompleteInventory.Reader :=
  if first : index.val<59 then .word ⟨index.val,first⟩
  else if second : index.val<63 then .backend ⟨index.val-59,by omega⟩
  else if index.val=63 then .header
  else if index.val=64 then .visit
  else if third : index.val<68 then .trace ⟨index.val-65,by omega⟩
  else .metadata

def readerIndex : C3CompleteInventory.Reader → Fin 69
  | .word field => ⟨field.val,by omega⟩
  | .backend field => ⟨59+field.val,by omega⟩
  | .header => 63 | .visit => 64
  | .trace field => ⟨65+field.val,by omega⟩
  | .metadata => 68

theorem reader_index (original : C3CompleteInventory.Reader) : reader (readerIndex original)=original := by
  cases original with
  | word field => simp [reader,readerIndex,field.isLt]
  | backend field =>
    change reader ⟨59+field.val,by omega⟩=_
    unfold reader
    have first:¬59+field.val<59 := by omega
    have second:59+field.val<63 := by omega
    simp only [dif_neg first,dif_pos second]
    congr 1
    apply Fin.ext
    simp
  | header => rfl
  | visit => rfl
  | trace field =>
    change reader ⟨65+field.val,by omega⟩=_
    unfold reader
    have first:¬65+field.val<59 := by omega
    have second:¬65+field.val<63 := by omega
    have third:65+field.val<68 := by omega
    have h:65+field.val≠63 := by omega
    have v:65+field.val≠64 := by omega
    simp only [dif_neg first,dif_neg second,if_neg h,if_neg v,dif_pos third]
    congr 1
    apply Fin.ext
    simp
  | metadata => rfl

local instance : DecidableEq RepresentationIO.WordImage := fun left right =>
  decidable_of_iff (PackedRuntimeIO.WordEqual left right) (PackedRuntimeIO.wordEqual_iff left right)

def Output (index : Fin 69) := Except String (C3CompleteInventory.Output (reader index))

def outputEq (index : Fin 69) : DecidableEq (Output index) := by
  unfold Output C3CompleteInventory.Output
  cases reader index <;> infer_instance

def read (boundary : Boundary) (index : Fin 69)
    (current : Except String (Option C3Published.Result)) : Output index := do
  let whole ← image boundary current
  return C3CompleteInventory.read (reader index) whole

/-- The finite source calculates every state from the fixed admitted seed.
No raw-state table, partition, normalizer or future readout is an argument. -/
abbrev source (boundary : Boundary) (installed : Installed boundary) : FiniteMinimalModel.Source where
  stateCount := C3Reachable.stateBound+2
  letterCount := 3
  readerCount := 69
  Output := Output
  outputEq := outputEq
  initial := 0
  autonomous := 0
  reader := 64
  action := fun operation => C3FiniteOccurrence.action installed.material.kernel boundary.seed (letter operation)
  read := fun observer index => read boundary observer (indexed installed.material.kernel boundary.seed index)

def originalRead (boundary : Boundary) (original : C3CompleteInventory.Reader)
    (current : Except String (Option C3Published.Result)) : Except String (C3CompleteInventory.Output original) := do
  let whole ← image boundary current
  return C3CompleteInventory.read original whole

theorem every_original_reader (boundary : Boundary) (original : C3CompleteInventory.Reader)
    (current : Except String (Option C3Published.Result)) :
    (reader_index original) ▸ read boundary (readerIndex original) current=originalRead boundary original current := by
  unfold read originalRead
  generalize h:image boundary current=whole
  cases whole with
  | error why =>
    have transport (a b : C3CompleteInventory.Reader) (equal : a=b) :
        equal ▸ (Except.error (α:=C3CompleteInventory.Output a) why)=
          Except.error (α:=C3CompleteInventory.Output b) why := by cases equal;rfl
    exact transport _ _ (reader_index original)
  | ok whole =>
    have transport (a b : C3CompleteInventory.Reader) (equal : a=b) :
        equal ▸ (Except.ok (ε:=String) (C3CompleteInventory.read a whole))=
          Except.ok (ε:=String) (C3CompleteInventory.read b whole) := by cases equal;rfl
    exact transport _ _ (reader_index original)

theorem all_words_zero_error (boundary : Boundary) (installed : Installed boundary)
    (word : List (Fin 3)) (observer : Fin 69)
    (index : Fin (C3Reachable.stateBound+2)) :
    (source boundary installed).read observer (FiniteMinimalModel.execute (source boundary installed) word index)=
      read boundary observer (C3FiniteOccurrence.execute installed.material.kernel boundary.seed (word.map letter)
        (indexed installed.material.kernel boundary.seed index)) := by
  have mapped:WholeRepresentation.runMap ((source boundary installed).action) word index=
      WholeRepresentation.runMap (C3FiniteOccurrence.action installed.material.kernel boundary.seed) (word.map letter) index := by
    induction word generalizing index with
    | nil => rfl
    | cons operation rest previous => simpa only [WholeRepresentation.runMap,List.map,source] using previous ((source boundary installed).action operation index)
  change read boundary observer (indexed installed.material.kernel boundary.seed (WholeRepresentation.runMap ((source boundary installed).action) word index))=_
  rw [mapped,C3FiniteOccurrence.all_words]

theorem minimum_future_kernel (boundary : Boundary) (installed : Installed boundary)
    (left right : Fin (C3Reachable.stateBound+2)) :
    FiniteMinimalModel.encode (source boundary installed) left=FiniteMinimalModel.encode (source boundary installed) right ↔
      ∀ word : List (Fin 3),∀ observer : Fin 69,
        read boundary observer (C3FiniteOccurrence.execute installed.material.kernel boundary.seed (word.map letter)
          (indexed installed.material.kernel boundary.seed left))=
        read boundary observer (C3FiniteOccurrence.execute installed.material.kernel boundary.seed (word.map letter)
          (indexed installed.material.kernel boundary.seed right)) := by
  rw [FiniteMinimalModel.encode_kernel]
  constructor
  · intro equal word observer
    rw [← all_words_zero_error,← all_words_zero_error]
    exact equal word observer
  · intro equal word observer
    rw [all_words_zero_error,all_words_zero_error]
    exact equal word observer

theorem minimum_every_future_reader (boundary : Boundary) (installed : Installed boundary)
    (word : List (Fin 3)) (observer : Fin 69) (index : Fin (C3Reachable.stateBound+2)) :
    FiniteMinimalModel.read (source boundary installed) observer
      (FiniteMinimalModel.run (source boundary installed) word (FiniteMinimalModel.encode (source boundary installed) index))=
      read boundary observer (C3FiniteOccurrence.execute installed.material.kernel boundary.seed (word.map letter)
        (indexed installed.material.kernel boundary.seed index)) := by
  rw [FiniteMinimalModel.every_future_reader_commutes,all_words_zero_error]

theorem original_initial_all_words (boundary : Boundary) (installed : Installed boundary)
    (word : List C3Native.Operation) :
    (indexed installed.material.kernel boundary.seed
      (FiniteMinimalModel.execute (source boundary installed) (word.map letterIndex) 0)).map
      (occurrenceCurrent boundary.seed)=C3Published.word installed.material.kernel word boundary.seed.initial := by
  have same:(word.map letterIndex).map letter=word := by
    simp only [List.map_map]
    have identity:letter ∘ letterIndex=id := funext letter_index
    simp only [identity,List.map_id]
  have mapped (letters : List (Fin 3)) (index : Fin (C3Reachable.stateBound+2)) :
      WholeRepresentation.runMap ((source boundary installed).action) letters index=
        WholeRepresentation.runMap (C3FiniteOccurrence.action installed.material.kernel boundary.seed) (letters.map letter) index := by
    induction letters generalizing index with
    | nil => rfl
    | cons operation rest previous => simpa only [WholeRepresentation.runMap,List.map,source] using previous ((source boundary installed).action operation index)
  change (indexed installed.material.kernel boundary.seed
    (WholeRepresentation.runMap ((source boundary installed).action) (word.map letterIndex) 0)).map _=_
  rw [mapped,same,C3FiniteOccurrence.all_words]
  exact C3FiniteOccurrence.execute_original installed.material.kernel boundary.seed word none

theorem minimal_other_implementations (boundary : Boundary) (installed : Installed boundary)
    {Candidate : Type} (represent : Fin (C3Reachable.stateBound+2) → Candidate)
    (actions : Fin 3 → Candidate → Candidate)
    (reads : (observer : Fin 69) → Candidate → Output observer)
    (action_commutes : ∀ operation index,actions operation (represent index)=
      represent ((source boundary installed).action operation index))
    (read_commutes : ∀ observer index,reads observer (represent index)=
      (source boundary installed).read observer index) :
    Function.FactorsThrough (FiniteMinimalModel.encode (source boundary installed)) represent :=
by
  exact FiniteMinimalModel.minimal (source boundary installed) represent actions (reads:=reads) action_commutes read_commutes

theorem every_future_reader_unique (boundary : Boundary) (installed : Installed boundary)
    (word : List (Fin 3)) (observer : Fin 69) :
    ∃! factor : FiniteMinimalModel.Model (source boundary installed) → Output observer,
      ∀ index,factor (FiniteMinimalModel.encode (source boundary installed) index)=
        read boundary observer (C3FiniteOccurrence.execute installed.material.kernel boundary.seed (word.map letter)
          (indexed installed.material.kernel boundary.seed index)) := by
  have unique:=FiniteMinimalModel.every_future_reader_unique_factorization (source boundary installed) word observer
  rcases unique with ⟨factor,paid,only⟩
  refine ⟨factor,?_,?_⟩
  · intro index
    rw [← all_words_zero_error]
    exact paid index
  · intro other commutes
    apply only
    intro index
    rw [all_words_zero_error]
    exact commutes index

end FlyCNS.C3ReachableModel
