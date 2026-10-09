import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.Consumer

/-!
The existing inventory executor determines the actual DNA after every water-paid prefix.
Source endpoint recognition is consumed only after enough raw water pays the complete trace.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Deamination.ExecutionReadout

open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

/-- A normal form for one DNA molecule and the accumulated products/residual supply. -/
def workingStock (word : List Base) (paid water : Nat) : Stock :=
  .dna word :: (List.replicate paid Species.ammonia ++ List.replicate water Species.water)

/-- A coordinate of the already generated source trace, not another inventory executor. -/
def prefixWord (initial : List Base) (steps : List Source.Step) : List Base :=
  steps.foldl (fun _ step => step.output) initial

/-- Read DNA from the actual stock; the source's proposed endpoint is not an argument. -/
def readDNA (stock : Stock) : Option (List Base) :=
  (stock.filterMap (fun species => match species with
    | .dna word => some word
    | _ => none)).head?

theorem erase_water_after_ammonia (paid water : Nat) :
    (List.replicate paid Species.ammonia ++ Species.water :: List.replicate water Species.water).erase
      Species.water = List.replicate paid Species.ammonia ++ List.replicate water Species.water := by
  induction paid with
  | zero => simp
  | succ paid inductionHypothesis =>
      simp [List.replicate_succ, inductionHypothesis]

theorem fire_paid_step (step : Source.Step) (paid water : Nat) :
    fire step.reaction (workingStock step.input paid (water+1)) =
      .ok (workingStock step.output (paid+1) water) := by
  simp [fire, Inventory.fire, Inventory.consume, Source.Step.reaction, Reaction.reactants, Reaction.products,
    workingStock, Source.Step.input, Source.Step.output, erase_water_after_ammonia,
    List.replicate_succ]

theorem fire_dry_step (step : Source.Step) (paid : Nat) :
    fire step.reaction (workingStock step.input paid 0) = .error .water := by
  simp [fire, Inventory.fire, Inventory.consume, Source.Step.reaction, Reaction.reactants, workingStock,
    Source.Step.input]

theorem execute_cons (reaction : Reaction) (rest : List Reaction) (stock : Stock) :
    execute (reaction :: rest) stock =
      match fire reaction stock with
      | .error missing => ⟨[], reaction :: rest, stock, some missing⟩
      | .ok next =>
          let after := execute rest next
          ⟨reaction :: after.fired, after.remaining, after.stock, after.missing⟩ :=
  by
    unfold execute fire
    rw [Inventory.execute_cons]
    cases Inventory.fire Reaction.reactants Reaction.products reaction stock <;> rfl

theorem prefix_word_of_follows (initial final : List Base) (steps : List Source.Step)
    (trace : Source.follows initial steps final) : prefixWord initial steps = final := by
  induction steps generalizing initial with
  | nil => exact trace
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis step.output trace.2

/-- All capacities, including a cut: the stock holds the exact water-paid source prefix. -/
theorem execute_prefix_of_follows (initial final : List Base) (steps : List Source.Step)
    (trace : Source.follows initial steps final) (paid water : Nat) :
    execute (steps.map Source.Step.reaction) (workingStock initial paid water) =
      ⟨(steps.take water).map Source.Step.reaction,
       (steps.drop water).map Source.Step.reaction,
       workingStock (prefixWord initial (steps.take water))
         (paid + min water steps.length) (water - steps.length),
       if water < steps.length then some .water else none⟩ := by
  induction steps generalizing initial paid water with
  | nil => simp [execute, workingStock, prefixWord]
  | cons step rest inductionHypothesis =>
      have first := trace.1
      have later := trace.2
      subst initial
      cases water with
      | zero =>
          rw [List.map_cons, execute_cons, fire_dry_step]
          simp [prefixWord, workingStock]
      | succ water =>
          rw [List.map_cons, execute_cons, fire_paid_step]
          dsimp only
          rw [inductionHypothesis step.output later (paid+1) water]
          simp [prefixWord, List.take_succ_cons, List.drop_succ_cons, Nat.succ_min_succ,
            Nat.succ_sub_succ_eq_sub, Nat.add_comm, Nat.add_left_comm]

/-- Here the trace premise is discharged by the fixed source compiler. -/
theorem source_execute_prefix (edits : Target.Edits) (water : Nat) :
    execute (Source.sourceProgram edits).reactions (modelStock water) =
      ⟨((Source.sourceProgram edits).steps.take water).map Source.Step.reaction,
       ((Source.sourceProgram edits).steps.drop water).map Source.Step.reaction,
       workingStock
         (prefixWord Source.originalMinusAligned ((Source.sourceProgram edits).steps.take water))
         (min water (Source.sourceProgram edits).steps.length)
         (water - (Source.sourceProgram edits).steps.length),
       if water < (Source.sourceProgram edits).steps.length then some .water else none⟩ := by
  simpa only [Source.Compilation.reactions, workingStock, List.replicate_zero, List.nil_append,
    Nat.zero_add, modelStock] using
    execute_prefix_of_follows Source.originalMinusAligned (Source.sourceProgram edits).word
      (Source.sourceProgram edits).steps (Source.compile_follows _ _) 0 water

theorem source_execute_complete (edits : Target.Edits) (water : Nat)
    (enough : (Source.sourceProgram edits).steps.length ≤ water) :
    execute (Source.sourceProgram edits).reactions (modelStock water) =
      ⟨(Source.sourceProgram edits).reactions, [],
       workingStock (Source.sourceProgram edits).word (Source.sourceProgram edits).steps.length
         (water - (Source.sourceProgram edits).steps.length), none⟩ := by
  have execution := source_execute_prefix edits water
  have endpoint := prefix_word_of_follows Source.originalMinusAligned
    (Source.sourceProgram edits).word (Source.sourceProgram edits).steps (Source.compile_follows _ _)
  simpa only [List.take_of_length_le enough, List.drop_eq_nil_of_le enough, List.map_nil,
    Nat.min_eq_right enough, if_neg (Nat.not_lt.mpr enough), endpoint,
    Source.Compilation.reactions] using execution

theorem working_stock_counts (word : List Base) (paid water : Nat) :
    (workingStock word paid water).count (.dna word) = 1 ∧
    (workingStock word paid water).count .ammonia = paid ∧
    (workingStock word paid water).count .water = water := by
  simp [workingStock, List.count_append, List.count_replicate]

theorem working_stock_read_dna (word : List Base) (paid water : Nat) :
    readDNA (workingStock word paid water) = some word := by
  simp [readDNA, workingStock]

/-- The completed-source endpoint is now an actual inventory readout with its finite balances. -/
theorem source_complete_actual_readout (third eighth ninth : Bool) (water : Nat)
    (enough : (Source.sourceProgram ⟨third,eighth,ninth⟩).steps.length ≤ water) :
    let program := Source.sourceProgram ⟨third,eighth,ninth⟩
    let actual := execute program.reactions (modelStock water)
    actual.missing = none ∧
    actual.stock.count (.dna program.word) = 1 ∧
    actual.stock.count .water = water - program.steps.length ∧
    actual.stock.count .ammonia = program.steps.length ∧
    readDNA actual.stock = some program.word ∧
    (readDNA actual.stock).map Source.plusReadout = some (Target.genomic ⟨third,eighth,ninth⟩) := by
  dsimp only
  rw [source_execute_complete _ _ enough]
  have counts := working_stock_counts (Source.sourceProgram ⟨third,eighth,ninth⟩).word
    (Source.sourceProgram ⟨third,eighth,ninth⟩).steps.length
    (water - (Source.sourceProgram ⟨third,eighth,ninth⟩).steps.length)
  refine ⟨rfl, counts.1, counts.2.2, counts.2.1,
    working_stock_read_dna _ _ _, ?_⟩
  rw [working_stock_read_dna, Option.map_some, Source.source_readout_commutes]

/-- At insufficient capacity, actual DNA is the paid prefix, with the unexecuted suffix retained. -/
theorem source_prefix_actual_readout (edits : Target.Edits) (water : Nat) :
    let program := Source.sourceProgram edits
    let actual := execute program.reactions (modelStock water)
    readDNA actual.stock =
      some (prefixWord Source.originalMinusAligned (program.steps.take water)) ∧
    actual.stock.count .ammonia = min water program.steps.length ∧
    actual.stock.count .water = water - program.steps.length ∧
    actual.fired = (program.steps.take water).map Source.Step.reaction ∧
    actual.remaining = (program.steps.drop water).map Source.Step.reaction ∧
    actual.missing = if water < program.steps.length then some .water else none := by
  dsimp only
  rw [source_execute_prefix]
  have counts := working_stock_counts
    (prefixWord Source.originalMinusAligned ((Source.sourceProgram edits).steps.take water))
    (min water (Source.sourceProgram edits).steps.length)
    (water - (Source.sourceProgram edits).steps.length)
  exact ⟨working_stock_read_dna _ _ _, counts.2.1, counts.2.2, rfl, rfl, rfl⟩

def sourceExecution (edits : Target.Edits) (water : Nat) : Execution :=
  execute (Source.sourceProgram edits).reactions (modelStock water)

structure NativeExecutionContract : Prop where
  prefixExecution : type_of% source_execute_prefix
  completeExecution : type_of% source_execute_complete
  prefixReadout : type_of% source_prefix_actual_readout
  completeReadout : type_of% source_complete_actual_readout

theorem sourceGeneratedNativeExecution : NativeExecutionContract :=
  ⟨source_execute_prefix,source_execute_complete,source_prefix_actual_readout,
   source_complete_actual_readout⟩

end CPS1Deamination.ExecutionReadout
