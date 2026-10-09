import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Live

set_option autoImplicit false
namespace CPS1LiveEditing
noncomputable section
open CPS1ResourceExecution CPS1Deamination CPS1Deamination.ExecutionReadout
variable {frame : CPS1Recycling.Frame}

private def reactionStep? : Reaction → Option Source.Step
  | .deaminate left right => some ⟨left.length,left,right⟩
  | _ => none

private theorem reaction_step_exact (reaction : Reaction) (step : Source.Step)
    (actual : reactionStep? reaction = some step) : step.reaction = reaction := by
  cases reaction <;> simp only [reactionStep?] at actual <;> try cases actual
  rfl

inductive SuffixFailure
  | missingLiveDNA
  | notDeamination (reaction : Reaction)
  | inconsistentWord (live required : List Base)

private structure DecodedSuffix (initial : List Base) (saved : List Reaction) where
  final : List Base
  steps : List Source.Step
  reactions : steps.map Source.Step.reaction = saved
  follows : Source.follows initial steps final

-- Checks the stored reaction data; it does not predict resource success or supply a target word.
private def decodeSuffix (initial : List Base) :
    (saved : List Reaction) → Except SuffixFailure (DecodedSuffix initial saved)
  | [] => .ok ⟨initial,[],rfl,rfl⟩
  | reaction :: rest =>
    match parsed : reactionStep? reaction with
    | none => .error (.notDeamination reaction)
    | some step =>
      if input : step.input = initial then
        match decodeSuffix step.output rest with
        | .error failure => .error failure
        | .ok tail => .ok ⟨tail.final,step :: tail.steps,
            by simp only [List.map_cons,reaction_step_exact reaction step parsed,tail.reactions],
            ⟨input,tail.follows⟩⟩
      else .error (.inconsistentWord initial step.input)

structure SavedSuffix (current : CPS1ReactiveField.Occurrence frame) where
  initial : List Base
  actualDNA : readDNA (liveResources current) = some initial
  final : List Base
  steps : List Source.Step
  reactions : steps.map Source.Step.reaction = (CPS1ReactiveField.editingSource current.old).editing.remaining
  follows : Source.follows initial steps final

def savedSuffix (current : CPS1ReactiveField.Occurrence frame) : Except SuffixFailure (SavedSuffix current) :=
  match actual : readDNA (liveResources current) with
  | none => .error .missingLiveDNA
  | some initial =>
    match decodeSuffix initial (CPS1ReactiveField.editingSource current.old).editing.remaining with
    | .error failure => .error failure
    | .ok generated => .ok ⟨initial,actual,generated.final,generated.steps,generated.reactions,generated.follows⟩

inductive SuffixEvent (current : CPS1ReactiveField.Occurrence frame) (water : Nat)
  | rejected (slice : LiveSlice current) (available : Stock)
      (rawSource : available = Continuation.refillWater slice.resources water)
      (saved : List Reaction)
      (savedSource : saved = (CPS1ReactiveField.editingSource current.old).editing.remaining)
      (failure : SuffixFailure)
  | resumed (source : SavedSuffix current) (event : ResumeEvent current water)

def suffixEvent (current : CPS1ReactiveField.Occurrence frame) (water : Nat) : SuffixEvent current water :=
  match savedSuffix current with
  | .error failure =>
    let slice := liveSlice current
    .rejected slice (Continuation.refillWater slice.resources water) rfl
      (CPS1ReactiveField.editingSource current.old).editing.remaining rfl failure
  | .ok source => .resumed source (resumeEvent current water)

-- Native primitive success generates its exact remainder, including arbitrary old NH3/resources.
theorem actual_deamination_remainder (left right : List Base) (stock next : Stock)
    (actual : fire (.deaminate left right) stock = .ok next) :
    ∃ remainder : Stock,
      consume [.dna (left ++ Base.A :: right), .water] stock = .ok remainder ∧
      next = .dna (left ++ Base.I :: right) :: .ammonia :: remainder ∧
      stock.Perm (.dna (left ++ Base.A :: right) :: .water :: remainder) ∧
      readDNA next = some (left ++ Base.I :: right) := by
  unfold fire Inventory.fire at actual
  cases consumed : Inventory.consume (Reaction.reactants (.deaminate left right)) stock with
  | error missing => simp only [consumed] at actual; cases actual
  | ok remainder =>
    simp only [consumed, Except.ok.injEq] at actual
    have nextSame : next = .dna (left ++ Base.I :: right) :: .ammonia :: remainder := by
      simpa only [Reaction.products, List.cons_append, List.nil_append] using actual.symm
    refine ⟨remainder, ?_, nextSame, ?_, ?_⟩
    · simpa only [consume, Reaction.reactants] using consumed
    · simpa only [Reaction.reactants, List.cons_append, List.nil_append] using
        Inventory.consume_perm _ _ _ consumed
    · rw [nextSame]
      rfl

end
end CPS1LiveEditing
