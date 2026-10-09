import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Suffix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1LiveEditing
noncomputable section
open CPS1ResourceExecution CPS1Deamination CPS1Deamination.ExecutionReadout
variable {frame : CPS1Recycling.Frame}

theorem read_dna_member (stock : Stock) (word : List Base) (actual : readDNA stock = some word) :
    Species.dna word ∈ stock := by
  induction stock with
  | nil => cases actual
  | cons item rest ih =>
    cases item <;> first
    | exact List.mem_cons_of_mem _ (ih actual)
    | simp only [readDNA,List.filterMap_cons,List.head?_cons,Option.some.injEq] at actual
      cases actual
      exact List.mem_cons_self

theorem deamination_failure_water (step : Source.Step) (stock : Stock) (missing : Species)
    (dna : readDNA stock = some step.input)
    (failed : fire step.reaction stock = .error missing) : missing = .water := by
  have present := read_dna_member stock step.input dna
  dsimp only [Source.Step.input] at present
  unfold fire Inventory.fire at failed
  simp only [Source.Step.reaction,Reaction.reactants,Inventory.consume,if_pos present] at failed
  by_cases wet : Species.water ∈ stock.erase (.dna (step.left ++ Base.A :: step.right))
  · simp only [if_pos wet] at failed
    cases failed
  · simp only [if_neg wet,Except.error.injEq] at failed
    exact failed.symm

theorem native_suffix_update (initial final : List Base) (steps : List Source.Step)
    (stock : Stock) (trace : Source.follows initial steps final) (dna : readDNA stock = some initial) :
    let result := execute (steps.map Source.Step.reaction) stock
    result.fired = (steps.take result.fired.length).map Source.Step.reaction ∧
    result.remaining = (steps.drop result.fired.length).map Source.Step.reaction ∧
    readDNA result.stock = some (prefixWord initial (steps.take result.fired.length)) ∧
    result.stock.count .ammonia = stock.count .ammonia + result.fired.length ∧
    result.stock.count .water + result.fired.length = stock.count .water ∧
    result.missing = if result.fired.length < steps.length then some .water else none := by
  induction steps generalizing initial stock with
  | nil =>
    dsimp only [List.map_nil,execute,Inventory.execute,Execution.fired,Execution.remaining,Execution.stock,Execution.missing]
    exact ⟨rfl,rfl,dna,rfl,rfl,rfl⟩
  | cons step rest ih =>
    have input := trace.1
    have later := trace.2
    subst initial
    cases fired : fire step.reaction stock with
    | error missing =>
      have cut := deamination_failure_water step stock missing dna fired
      simp only [List.map_cons,execute_cons,fired]
      dsimp only [Execution.fired,Execution.remaining,Execution.stock,Execution.missing]
      refine ⟨rfl,rfl,dna,rfl,rfl,?_⟩
      simpa using congrArg Option.some cut
    | ok next =>
      obtain ⟨remainder,consumed,nextSource,partition,nextDNA⟩ :=
        actual_deamination_remainder step.left step.right stock next fired
      have generated := ih step.output next later nextDNA
      have ammonia := fire_balance step.reaction stock next fired .ammonia
      have water := fire_balance step.reaction stock next fired .water
      simp only [Source.Step.reaction,Reaction.reactants,Reaction.products] at ammonia water
      simp at ammonia water
      simp only [List.map_cons,execute_cons,fired]
      dsimp only [Execution.fired,Execution.remaining,Execution.stock,Execution.missing]
      simp only [List.length_cons,List.take_succ_cons,List.drop_succ_cons,List.map_cons,prefixWord,List.foldl_cons]
      refine ⟨congrArg (List.cons step.reaction) generated.1,generated.2.1,generated.2.2.1,?_,?_,?_⟩
      · have stepAmmonia : next.count .ammonia = stock.count .ammonia + 1 := ammonia.symm
        calc
          (execute (rest.map Source.Step.reaction) next).stock.count .ammonia =
              next.count .ammonia + (execute (rest.map Source.Step.reaction) next).fired.length :=
            generated.2.2.2.1
          _ = (stock.count .ammonia + 1) + (execute (rest.map Source.Step.reaction) next).fired.length := by
            rw [stepAmmonia]
          _ = stock.count .ammonia + ((execute (rest.map Source.Step.reaction) next).fired.length + 1) :=
            Nat.add_right_comm _ _ _
      · have laterWater := generated.2.2.2.2.1
        calc
          (execute (rest.map Source.Step.reaction) next).stock.count .water +
              ((execute (rest.map Source.Step.reaction) next).fired.length + 1) =
              ((execute (rest.map Source.Step.reaction) next).stock.count .water +
                (execute (rest.map Source.Step.reaction) next).fired.length) + 1 := by omega
          _ = next.count .water + 1 := by rw [laterWater]
          _ = stock.count .water := water.symm
      · simpa using generated.2.2.2.2.2

theorem native_execution_whole (program : List Reaction) (stock : Stock) :
    (stock ++ credit (execute program stock).fired).Perm
      ((execute program stock).stock ++ debit (execute program stock).fired) := by
  apply List.perm_iff_count.mpr
  intro species
  simpa only [List.count_append] using execution_balance program stock species

end
end CPS1LiveEditing
