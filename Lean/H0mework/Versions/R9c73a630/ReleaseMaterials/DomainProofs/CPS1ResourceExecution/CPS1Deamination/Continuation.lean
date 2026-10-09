import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.ExecutionReadout

/-!
A second native execution consumes the first execution's actual suffix and stock plus raw water.
Stitching the two paid traces preserves every earlier reaction and computes the cumulative update.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Deamination.Continuation

open CPS1ResourceExecution ExecutionReadout
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def refillWater (stock : Stock) (water : Nat) : Stock :=
  stock ++ List.replicate water Species.water

/-- Preserve the first actual receipt while retaining the second event's current disposition. -/
def stitch (first second : Execution) : Execution :=
  ⟨first.fired ++ second.fired, second.remaining, second.stock, second.missing⟩

/-- The source fixes the first event; callers supply only the two raw water amounts. -/
def sourceContinuation (edits : Target.Edits) (initialWater additionalWater : Nat) : Execution :=
  let first := sourceExecution edits initialWater
  execute first.remaining (refillWater first.stock additionalWater)

theorem refill_working_stock (word : List Base) (paid water additional : Nat) :
    refillWater (workingStock word paid water) additional =
      workingStock word paid (water + additional) := by
  simp only [refillWater, workingStock, List.cons_append, List.append_assoc]
  rw [List.replicate_add water additional Species.water]

/-- Two actual invocations compose through the paid cut, without replaying its prefix. -/
theorem native_continuation_of_follows (initial final : List Base) (steps : List Source.Step)
    (trace : Source.follows initial steps final) (paid water additional : Nat) :
    let first := execute (steps.map Source.Step.reaction) (workingStock initial paid water)
    let second := execute first.remaining (refillWater first.stock additional)
    stitch first second =
      execute (steps.map Source.Step.reaction) (workingStock initial paid (water + additional)) := by
  induction steps generalizing initial paid water with
  | nil =>
      simp only [List.map_nil]
      dsimp only [execute,Inventory.execute,stitch,Execution.fired,Execution.remaining,Execution.stock,Execution.missing]
      simp only [refill_working_stock,List.nil_append]
  | cons step rest inductionHypothesis =>
      have firstInput := trace.1
      have later := trace.2
      subst initial
      cases water with
      | zero =>
          rw [List.map_cons, execute_cons, fire_dry_step]
          dsimp only [stitch,Execution.fired,Execution.remaining,Execution.stock,Execution.missing]
          simp only [refill_working_stock, Nat.zero_add, List.nil_append]
      | succ water =>
          simp only [List.map_cons, execute_cons, fire_paid_step, Nat.succ_add]
          have continued := inductionHypothesis step.output later (paid+1) water
          exact congrArg (fun result : Execution =>
            (⟨step.reaction :: result.fired, result.remaining, result.stock,
              result.missing⟩ : Execution)) continued

/-- No execution certificate or proposed endpoint enters this source-fixed continuation mouth. -/
theorem source_continuation_composes (edits : Target.Edits) (water additional : Nat) :
    stitch (sourceExecution edits water) (sourceContinuation edits water additional) =
      sourceExecution edits (water + additional) := by
  simpa only [sourceExecution, sourceContinuation, modelStock, workingStock,
    List.replicate_zero, List.nil_append, Nat.zero_add, Source.Compilation.reactions] using
    native_continuation_of_follows Source.originalMinusAligned (Source.sourceProgram edits).word
      (Source.sourceProgram edits).steps (Source.compile_follows _ _) 0 water additional

/-- Every refill size generates the exact new DNA, balances, paid trace and remaining suffix. -/
theorem source_continuation_update (edits : Target.Edits) (water additional : Nat) :
    let program := Source.sourceProgram edits
    let first := sourceExecution edits water
    let second := sourceContinuation edits water additional
    first.fired ++ second.fired = (program.steps.take (water + additional)).map Source.Step.reaction ∧
    second.remaining = (program.steps.drop (water + additional)).map Source.Step.reaction ∧
    second.stock = workingStock
      (prefixWord Source.originalMinusAligned (program.steps.take (water + additional)))
      (min (water + additional) program.steps.length) (water + additional - program.steps.length) ∧
    second.missing = if water + additional < program.steps.length then some .water else none := by
  have generated := source_continuation_composes edits water additional
  have cumulative := source_execute_prefix edits (water + additional)
  change sourceExecution edits (water + additional) = _ at cumulative
  have updated := generated.trans cumulative
  exact ⟨congrArg Execution.fired updated, congrArg Execution.remaining updated,
    congrArg Execution.stock updated, congrArg Execution.missing updated⟩

theorem source_continuation_actual_readout (edits : Target.Edits) (water additional : Nat) :
    let program := Source.sourceProgram edits
    let second := sourceContinuation edits water additional
    readDNA second.stock =
      some (prefixWord Source.originalMinusAligned (program.steps.take (water + additional))) ∧
    second.stock.count .ammonia = min (water + additional) program.steps.length ∧
    second.stock.count .water = water + additional - program.steps.length := by
  dsimp only
  rw [(source_continuation_update edits water additional).2.2.1]
  have counts := working_stock_counts
    (prefixWord Source.originalMinusAligned ((Source.sourceProgram edits).steps.take (water + additional)))
    (min (water + additional) (Source.sourceProgram edits).steps.length)
    (water + additional - (Source.sourceProgram edits).steps.length)
  exact ⟨working_stock_read_dna _ _ _, counts.2.1, counts.2.2⟩

/-- Only the source-generated suffix is offered to the second invocation. -/
theorem source_continuation_only_remaining (edits : Target.Edits) (water additional : Nat) :
    sourceContinuation edits water additional =
      execute ((Source.sourceProgram edits).steps.drop water |>.map Source.Step.reaction)
        (refillWater (sourceExecution edits water).stock additional) := by
  dsimp only [sourceContinuation]
  have residual := (source_prefix_actual_readout edits water).2.2.2.2.1
  change (sourceExecution edits water).remaining = _ at residual
  rw [residual]

theorem source_refill_settles (edits : Target.Edits) (water additional : Nat)
    (enough : (Source.sourceProgram edits).steps.length ≤ water + additional) :
    (sourceContinuation edits water additional).missing = none ∧
    (sourceContinuation edits water additional).remaining = [] ∧
    readDNA (sourceContinuation edits water additional).stock =
      some (Source.sourceProgram edits).word := by
  have generated := source_continuation_composes edits water additional
  have complete := source_execute_complete edits (water + additional) enough
  change sourceExecution edits (water + additional) = _ at complete
  have updated := generated.trans complete
  have stock := congrArg Execution.stock updated
  have remaining := congrArg Execution.remaining updated
  have missing := congrArg Execution.missing updated
  dsimp only [stitch] at stock remaining missing
  exact ⟨missing, remaining, by rw [stock]; exact working_stock_read_dna _ _ _⟩

/-- A complete first pass retains its stock and accepts extra water through the empty suffix. -/
theorem source_complete_then_refill (edits : Target.Edits) (water additional : Nat)
    (alreadyPaid : (Source.sourceProgram edits).steps.length ≤ water) :
    sourceContinuation edits water additional =
      ⟨[], [], refillWater (sourceExecution edits water).stock additional, none⟩ := by
  dsimp only [sourceContinuation]
  have complete := source_execute_complete edits water alreadyPaid
  change sourceExecution edits water = _ at complete
  simp only [complete]
  rfl

end CPS1Deamination.Continuation
