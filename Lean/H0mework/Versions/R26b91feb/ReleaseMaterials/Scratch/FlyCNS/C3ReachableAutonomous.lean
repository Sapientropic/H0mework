import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ReachableModel

set_option autoImplicit false
namespace FlyCNS.C3ReachableAutonomous
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open C3FiniteOccurrence

abbrev Letter := PUnit ⊕ C3Native.Operation
def letter (index : Fin 4) : Letter :=
  if index.val=0 then .inl () else .inr (C3ReachableModel.letter ⟨index.val-1,by omega⟩)
def letterIndex : Letter → Fin 4
  | .inl _ => 0
  | .inr operation => ⟨1+(C3ReachableModel.letterIndex operation).val,by omega⟩

theorem letter_index (original : Letter) : letter (letterIndex original)=original := by
  cases original with
  | inl token => cases token;rfl
  | inr operation => cases operation <;> rfl

def selected (seed : C3Reachable.Seed) (input : Letter) (before : Option C3Published.Result) : C3Native.Operation :=
  match input with
  | .inl _ => C3Native.operationAt (occurrenceCurrent seed before).original.visit
  | .inr operation => operation

def effect (material : C3Macro.Material) (seed : C3Reachable.Seed) (input : Letter)
    (current : Except String (Option C3Published.Result)) : Except String (Option C3Published.Result) := do
  let before ← current
  occurrenceAction material seed (selected seed input before) (.ok before)

def action (material : C3Macro.Material) (seed : C3Reachable.Seed) (input : Letter)
    (index : Fin (C3Reachable.stateBound+2)) : Fin (C3Reachable.stateBound+2) :=
  match indexed material seed index with
  | .error _ => index
  | .ok current => C3FiniteOccurrence.action material seed (selected seed input current) index

theorem action_commutes (material : C3Macro.Material) (seed : C3Reachable.Seed)
    (input : Letter) (index : Fin (C3Reachable.stateBound+2)) :
    indexed material seed (action material seed input index)=effect material seed input (indexed material seed index) := by
  unfold action effect
  cases h:indexed material seed index with
  | error why => simp only [h,bind,Except.bind]
  | ok before =>
    simp only [bind,Except.bind]
    simpa only [h] using C3FiniteOccurrence.action_commutes material seed (selected seed input before) index

def execute (material : C3Macro.Material) (seed : C3Reachable.Seed) : List Letter →
    Except String (Option C3Published.Result) → Except String (Option C3Published.Result)
  | [],current => current
  | input::rest,current => execute material seed rest (effect material seed input current)

theorem all_words (material : C3Macro.Material) (seed : C3Reachable.Seed)
    (word : List Letter) (index : Fin (C3Reachable.stateBound+2)) :
    indexed material seed (WholeRepresentation.runMap (action material seed) word index)=
      execute material seed word (indexed material seed index) := by
  induction word generalizing index with
  | nil => rfl
  | cons input rest previous =>
    simp only [WholeRepresentation.runMap,execute]
    rw [previous,action_commutes]

/-- The autonomous letter is the original current-dependent successor.
The three explicit registered operations remain distinct input letters. -/
abbrev source (boundary : Boundary) (installed : Installed boundary) : FiniteMinimalModel.Source where
  stateCount := C3Reachable.stateBound+2
  letterCount := 4
  readerCount := 69
  Output := C3ReachableModel.Output
  outputEq := C3ReachableModel.outputEq
  initial := 0
  autonomous := 0
  reader := 64
  action := fun input => action installed.material.kernel boundary.seed (letter input)
  read := fun observer index => C3ReachableModel.read boundary observer (indexed installed.material.kernel boundary.seed index)

theorem autonomous_actual (material : C3Macro.Material) (seed : C3Reachable.Seed)
    (before : Option C3Published.Result) :
    effect material seed (.inl ()) (.ok before)=do
      let generated ← C3Published.successor material (occurrenceCurrent seed before)
      return some generated := rfl

theorem input_actual (material : C3Macro.Material) (seed : C3Reachable.Seed)
    (operation : C3Native.Operation) (current : Except String (Option C3Published.Result)) :
    effect material seed (.inr operation) current=occurrenceAction material seed operation current := by
  cases current <;> rfl

theorem autonomous_prefix (material : C3Macro.Material) (seed : C3Reachable.Seed) (n : Nat) :
    execute material seed (List.replicate n (.inl ())) (.ok none)=generate material seed n := by
  have commute (n : Nat) (before : Except String (Option C3Published.Result)) :
      execute material seed (List.replicate (n+1) (.inl ())) before=
        effect material seed (.inl ()) (execute material seed (List.replicate n (.inl ())) before) := by
    induction n generalizing before with
    | zero => rfl
    | succ n previous => simpa only [List.replicate_succ,execute] using previous (effect material seed (.inl ()) before)
  induction n with
  | zero => rfl
  | succ n previous =>
    rw [commute,previous]
    change effect material seed (.inl ()) (generate material seed n)=(do
      let before ← generate material seed n
      let generated ← C3Published.successor material (occurrenceCurrent seed before)
      pure (some generated))
    cases h:generate material seed n <;> rfl

theorem all_original_reads (boundary : Boundary) (installed : Installed boundary)
    (word : List (Fin 4)) (observer : Fin 69) (index : Fin (C3Reachable.stateBound+2)) :
    (source boundary installed).read observer (FiniteMinimalModel.execute (source boundary installed) word index)=
      C3ReachableModel.read boundary observer (execute installed.material.kernel boundary.seed (word.map letter)
        (indexed installed.material.kernel boundary.seed index)) := by
  have mapped:WholeRepresentation.runMap ((source boundary installed).action) word index=
      WholeRepresentation.runMap (action installed.material.kernel boundary.seed) (word.map letter) index := by
    induction word generalizing index with
    | nil => rfl
    | cons input rest previous => simpa only [WholeRepresentation.runMap,List.map,source] using previous ((source boundary installed).action input index)
  change C3ReachableModel.read boundary observer (indexed installed.material.kernel boundary.seed
    (WholeRepresentation.runMap ((source boundary installed).action) word index))=_
  rw [mapped,all_words]

theorem minimum_all_words (boundary : Boundary) (installed : Installed boundary)
    (word : List (Fin 4)) (observer : Fin 69) (index : Fin (C3Reachable.stateBound+2)) :
    FiniteMinimalModel.read (source boundary installed) observer
      (FiniteMinimalModel.run (source boundary installed) word (FiniteMinimalModel.encode (source boundary installed) index))=
      C3ReachableModel.read boundary observer (execute installed.material.kernel boundary.seed (word.map letter)
        (indexed installed.material.kernel boundary.seed index)) := by
  rw [FiniteMinimalModel.every_future_reader_commutes,all_original_reads]

theorem minimum_future_kernel (boundary : Boundary) (installed : Installed boundary)
    (left right : Fin (C3Reachable.stateBound+2)) :
    FiniteMinimalModel.encode (source boundary installed) left=FiniteMinimalModel.encode (source boundary installed) right ↔
      ∀ word : List (Fin 4),∀ observer : Fin 69,
        C3ReachableModel.read boundary observer (execute installed.material.kernel boundary.seed (word.map letter)
          (indexed installed.material.kernel boundary.seed left))=
        C3ReachableModel.read boundary observer (execute installed.material.kernel boundary.seed (word.map letter)
          (indexed installed.material.kernel boundary.seed right)) := by
  rw [FiniteMinimalModel.encode_kernel]
  constructor
  · intro equal word observer
    rw [← all_original_reads,← all_original_reads]
    exact equal word observer
  · intro equal word observer
    rw [all_original_reads,all_original_reads]
    exact equal word observer

theorem minimal_other_implementations (boundary : Boundary) (installed : Installed boundary)
    {Candidate : Type} (represent : Fin (C3Reachable.stateBound+2) → Candidate)
    (actions : Fin 4 → Candidate → Candidate)
    (reads : (observer : Fin 69) → Candidate → C3ReachableModel.Output observer)
    (action_commutes : ∀ input index,actions input (represent index)=
      represent ((source boundary installed).action input index))
    (read_commutes : ∀ observer index,reads observer (represent index)=
      (source boundary installed).read observer index) :
    Function.FactorsThrough (FiniteMinimalModel.encode (source boundary installed)) represent :=
  FiniteMinimalModel.minimal (source boundary installed) represent actions (reads:=reads) action_commutes read_commutes

end FlyCNS.C3ReachableAutonomous
