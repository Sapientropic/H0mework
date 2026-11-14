import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Arena.Total

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ArenaTotal.Cost
open InterferenceProgram
abbrev Counted := ArenaCost.Counted

/-- The bound is read from the already loaded arena. Every successful choice
    removes one of its original input addresses. -/
def run (state : ArenaSource.State) : Counted ArenaSource.Run :=
  let output := ArenaCost.drive state.arena.code.size state
  ⟨output.value,output.cells+8*(state.arena.code.size+state.relations.length+
    ArenaCost.historySize output.value.instructions+1)+8⟩

theorem run_value (state : ArenaSource.State) :
    (run state).value=ArenaSource.drive state.arena.code.size state := by
  simp only [run,ArenaCost.drive_value]

theorem run_settled (state : ArenaSource.State) : ArenaSource.choose (run state).value.state=none := by
  rw [run_value]
  exact drive_nodes_settled state

theorem run_size (state : ArenaSource.State) : (run state).value.state.arena.code.size=state.arena.code.size := by
  rw [run_value,ArenaSource.drive_size]

theorem run_count (state : ArenaSource.State) : (run state).value.state.relations.length=state.relations.length := by
  rw [run_value,ArenaSource.drive_count]

theorem run_history (state : ArenaSource.State) :
    ArenaCost.historySize (run state).value.instructions ≤ state.arena.code.size*(state.arena.code.size+8)+1 :=
  ArenaCost.drive_history state.arena.code.size state

def runBudget (nodes count : Nat) : Nat :=
  ArenaCost.driveBudget nodes count nodes+8*(nodes+count+nodes*(nodes+8)+2)+8

theorem run_cells (state : ArenaSource.State) :
    (run state).cells ≤ runBudget state.arena.code.size state.relations.length := by
  have execution := ArenaCost.drive_cells state.arena.code.size state
  have history := ArenaCost.drive_history state.arena.code.size state
  simp only [run,runBudget]
  omega

theorem driveBudget_fuel_mono (nodes count a b : Nat) (bounded : a ≤ b) :
    ArenaCost.driveBudget nodes count a ≤ ArenaCost.driveBudget nodes count b := by
  unfold ArenaCost.driveBudget ArenaCost.roundBudget
  gcongr

theorem runBudget_mono (a b c d : Nat) (nodes : a ≤ b) (count : c ≤ d) : runBudget a c ≤ runBudget b d := by
  have execution := (driveBudget_fuel_mono a c a b nodes).trans (ArenaCost.driveBudget_mono a b c d b nodes count)
  have copies : a+c+a*(a+8)+2 ≤ b+d+b*(b+8)+2 := by gcongr
  unfold runBudget
  omega

theorem run_read (state : ArenaSource.State) (valid : ArenaSource.Valid state) (environment : Nat → Bool) :
    (FunctionalAffine.legal (run state).value.instructions environment &&
      truth ((run state).value.state.program.program.eval environment))=truth (state.program.program.eval environment) := by
  rw [run_value]
  exact ArenaSource.drive_read _ state valid environment

theorem run_correct (state : ArenaSource.State) (valid : ArenaSource.Valid state) :
    FunctionalSubstitution.decideProgram (run state).value.state.program.program=true ↔
      ∃ environment, truth (state.program.program.eval environment)=true := by
  rw [run_value]
  exact ArenaSource.drive_correct _ state valid

def compile {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) : Counted ArenaSource.Run :=
  let source := ArenaSource.front formula basis
  let initial := ArenaCost.build source.initial source.candidates
  let output := run initial.value
  ⟨output.value,source.cells+initial.cells+output.cells+
    16*(AffineCollect.tableSize source.table+FunctionalSchedule.Cost.inputSize source.candidates+
      source.initial.code.size+output.value.state.arena.code.size+output.value.state.relations.length+
      ArenaCost.historySize output.value.instructions+1)+24⟩

theorem compile_value {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) :
    (compile formula basis).value=ArenaSource.compile formula basis
      (ArenaSource.build (ArenaSource.front formula basis).initial (ArenaSource.front formula basis).candidates).arena.code.size := by
  simp only [compile,run_value,ArenaCost.build_value,ArenaSource.compile]

theorem compile_settled {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) :
    ArenaSource.choose (compile formula basis).value.state=none :=
  run_settled _

theorem compile_stable {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) :
    ArenaSource.step (compile formula basis).value.state=(compile formula basis).value.state := by
  simp only [ArenaSource.step,compile_settled]

theorem compile_size {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) :
    (compile formula basis).value.state.arena.code.size ≤
      ArenaSource.sourceBound n formula.length (Affine.Extract.literalCount formula) := by
  rw [compile_value]
  exact ArenaSource.compile_size formula basis valid _

theorem compile_count {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) :
    (compile formula basis).value.state.relations.length=(ForcedBranches.generate formula basis).value.length := by
  rw [compile_value,ArenaSource.compile_count]

def compileBudget (n clauses literals basisSize : Nat) : Nat :=
  let nodes := ArenaSource.sourceBound n clauses literals
  let count := 3*clauses+n*n
  ArenaSource.frontBudget n clauses literals basisSize+ArenaCost.buildBudget count nodes+runBudget nodes count+
    16*(AffineCarrier.Cost.cellBound n+ForcedBranches.Cost.outputStorage n clauses+
      2*nodes+count+nodes*(nodes+8)+2)+24

theorem compile_cells {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) :
    (compile formula basis).cells ≤
      compileBudget n formula.length (Affine.Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  let source := ArenaSource.front formula basis
  let initial := ArenaCost.build source.initial source.candidates
  let output := run initial.value
  let size := ArenaSource.sourceBound n formula.length (Affine.Extract.literalCount formula)
  let count := 3*formula.length+n*n
  have frontWork := ArenaSource.front_cells formula basis valid
  have inventorySize := ArenaCost.source_inventory formula basis valid
  have candidates := ForcedBranches.Cost.generate_length formula basis
  change source.candidates.length ≤ count at candidates
  have initialWork := (ArenaCost.build_cells source.initial source.candidates).trans
    (ArenaCost.buildBudget_mono _ count _ size candidates inventorySize)
  have nodes := (ArenaCost.build_nodes source.initial source.candidates).trans inventorySize
  change initial.value.arena.code.size ≤ size at nodes
  have relationCount : initial.value.relations.length=source.candidates.length := ArenaSource.build_count _ _
  have execution := (run_cells initial.value).trans (runBudget_mono _ size _ count nodes (relationCount ▸ candidates))
  have outputNodes : output.value.state.arena.code.size=initial.value.arena.code.size := run_size initial.value
  have outputCount : output.value.state.relations.length=source.candidates.length := (run_count initial.value).trans relationCount
  have history := run_history initial.value
  have stored : ArenaCost.historySize output.value.instructions ≤ size*(size+8)+1 := history.trans (by gcongr)
  have table := AffineCollect.Cost.coordinate_size n basis
  have storage := ForcedBranches.Cost.generate_storage formula basis valid
  have original : source.initial.code.size ≤ size :=
    (ArenaCost.inventory_code source.initial.code source.candidates).trans inventorySize
  change AffineCollect.tableSize source.table ≤ _ at table
  change FunctionalSchedule.Cost.inputSize source.candidates ≤ _ at storage
  change source.cells ≤ _ at frontWork
  change initial.cells ≤ _ at initialWork
  change output.cells ≤ _ at execution
  change source.cells+initial.cells+output.cells+
    16*(AffineCollect.tableSize source.table+FunctionalSchedule.Cost.inputSize source.candidates+
      source.initial.code.size+output.value.state.arena.code.size+output.value.state.relations.length+
      ArenaCost.historySize output.value.instructions+1)+24 ≤ _
  rw [outputNodes,outputCount]
  change _ ≤ ArenaSource.frontBudget n formula.length (Affine.Extract.literalCount formula) (AffineCarrier.cellSize basis)+
    ArenaCost.buildBudget count size+runBudget size count+
    16*(AffineCarrier.Cost.cellBound n+ForcedBranches.Cost.outputStorage n formula.length+
      2*size+count+size*(size+8)+2)+24
  omega

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) (environment : Nat → Bool) :
    (FunctionalAffine.legal (compile formula basis).value.instructions environment &&
      truth ((compile formula basis).value.state.program.program.eval environment))=
      CNFFormula.eval formula (Affine.Gates.coordinate (Affine.Table.coordinates n basis) environment) := by
  rw [compile_value]
  exact ArenaSource.compile_read formula basis valid _ environment

theorem compile_correct {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) :
    FunctionalSubstitution.decideProgram (compile formula basis).value.state.program.program=true ↔
      ∃ environment, CNFFormula.eval formula (Affine.Gates.coordinate (Affine.Table.coordinates n basis) environment)=true := by
  rw [compile_value]
  exact ArenaSource.compile_correct formula basis valid _

end SaturationMonoid.ComplexityProjection.SATSource.ArenaTotal.Cost
