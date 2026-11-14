import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.BinaryRelations
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCarrier.Cost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCollect.Cost

/-!
Uniform bounds for the actual source structures built by strong row feedback.
The atom and signed views are temporary coordinate systems, decoded back to the
original dimension before the next feedback step. Sizes count finite source
records, not machine time or the eventual positive carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SaturationMonoid.ComplexityProjection.SATSource.StrongFeedbackScale

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open CapacityMatching.RowCost (rowCells rowsCells)

theorem literalCount_flatten {n : Nat} (formula : CNFFormula n) :
    Extract.literalCount formula = formula.flatten.length := by
  simp only [Extract.literalCount,List.length_flatten]

theorem literalCount_same {n : Nat} (formula : CNFFormula n) :
    SATJoint.literalCount formula = Extract.literalCount formula := rfl

theorem rows_storage (n : Nat) (rows : List Row) (valid : ∀ row ∈ rows, Table.RowValid n row) :
    rowsCells rows ≤ rows.length*(n+2) := by
  simpa using CapacityMatching.RowCost.table_storage n rows.toArray valid

theorem rows_length (rows : List Row) : rows.length ≤ rowsCells rows :=
  (AffineCarrier.Cost.row_measures rows).1

theorem atom_width {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (Atoms.keys (Atoms.data basis formula)).length ≤ Extract.literalCount formula+1 := by
  simpa only [literalCount_flatten] using Atoms.atom_count basis formula

theorem data_storage {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    rowsCells (Atoms.data basis formula).flatten ≤ Extract.literalCount formula*(n+2) := by
  simpa only [Atoms.data_literals,literalCount_flatten] using
    rows_storage n _ (Atoms.data_valid basis inside formula)

theorem atom_table_size (source : List (List Row)) : (Atoms.table source).size = (Atoms.keys source).length := by
  simp [Atoms.table]

theorem atom_table_storage {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    rowsCells (Atoms.table (Atoms.data basis formula)).toList ≤ (Extract.literalCount formula+1)*(n+2) := by
  have generated := CapacityMatching.RowCost.table_storage n (Atoms.table (Atoms.data basis formula))
    (Atoms.table_valid n _ (Atoms.data_valid basis inside formula))
  rw [atom_table_size] at generated
  exact generated.trans (Nat.mul_le_mul_right _ (atom_width basis formula))

theorem compile_literals (source : List (List Row)) :
    Extract.literalCount (Atoms.compile source) = source.flatten.length+1 := by
  simp only [Extract.literalCount,Atoms.compile,Atoms.clause,List.map_cons,List.length_cons,List.length_nil,
    List.sum_cons,List.map_map,List.length_map,Function.comp_def,List.length_flatten]
  change 1+(source.map List.length).sum = (source.map List.length).sum+1
  omega

theorem atom_formula_size {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (Atoms.ofFormula basis formula).length ≤ formula.length+1 ∧
      Extract.literalCount (Atoms.ofFormula basis formula) ≤ Extract.literalCount formula+1 := by
  constructor
  · simpa only [Atoms.ofFormula,Atoms.compile_length,Atoms.data_length] using
      Subsumption.reduce_length_le (Atoms.compile (Atoms.data basis formula))
  · have bound := Subsumption.reduce_literalCount_le (Atoms.compile (Atoms.data basis formula))
    rw [literalCount_same,literalCount_same,compile_literals,Atoms.data_literals,← literalCount_flatten] at bound
    exact bound

theorem atom_subsumption_family {n : Nat} (basis : List Row) (formula : CNFFormula n) (fuel : Nat) :
    (Subsumption.reduceFuel fuel (Atoms.compile (Atoms.data basis formula))).length ≤ formula.length+1 ∧
      Extract.literalCount (Subsumption.reduceFuel fuel (Atoms.compile (Atoms.data basis formula))) ≤
        Extract.literalCount formula+1 := by
  constructor
  · simpa only [Atoms.compile_length,Atoms.data_length] using
      Subsumption.reduceFuel_length_le fuel (Atoms.compile (Atoms.data basis formula))
  · have bound := Subsumption.reduceFuel_literalCount_le fuel (Atoms.compile (Atoms.data basis formula))
    rw [literalCount_same,literalCount_same,compile_literals,Atoms.data_literals,← literalCount_flatten] at bound
    exact bound

theorem signed_formula_size {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (SignedCapacity.expand (Atoms.ofFormula basis formula)).length ≤
        2*(formula.length+1)+2*(Extract.literalCount formula+1) ∧
      Extract.literalCount (SignedCapacity.expand (Atoms.ofFormula basis formula)) ≤
        6*(Extract.literalCount formula+1) := by
  have size := atom_formula_size basis formula
  have width := atom_width basis formula
  simp only [SignedCapacity.expand_length,SignedCapacity.expand_literals]
  constructor <;> omega

theorem prepareStorage_mono (n small m M ell E : Nat) (width : n ≤ small) (count : m ≤ M)
    (items : ell ≤ E) :
    CapacityMatching.RowCost.prepareStorage n m ell ≤ CapacityMatching.RowCost.prepareStorage small M E := by
  unfold CapacityMatching.RowCost.prepareStorage CapacityMatching.RowCost.previousStorage CapacityMatching.RowCost.currentStorage
  gcongr

def relationBound (width clauses literals : Nat) : Nat :=
  CapacityMatching.RowCost.prepareStorage width clauses literals+2

theorem tight_relations_storage {n : Nat} (formula : CNFFormula n) :
    rowsCells (TightFeedback.relations formula) ≤ relationBound n formula.length (Extract.literalCount formula) := by
  have generated := CapacityMatching.RowCost.prepare_storage formula
  unfold TightFeedback.relations
  split
  · unfold relationBound
    omega
  · simp [rowCells,relationBound]

def tightRowsBound (n clauses literals : Nat) : Nat :=
  relationBound (literals+1) (clauses+1) (literals+1)*(n+2)

theorem tight_learn_length {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (TightFeedback.learn basis formula).length ≤
      relationBound (Extract.literalCount formula+1) (formula.length+1) (Extract.literalCount formula+1) := by
  have size := atom_formula_size basis formula
  have width := atom_width basis formula
  have produced := tight_relations_storage (Atoms.ofFormula basis formula)
  have records := rows_length (TightFeedback.relations (Atoms.ofFormula basis formula))
  have bound := prepareStorage_mono _ _ _ _ _ _ width size.1 size.2
  simp only [TightFeedback.learn,List.length_map]
  change (TightFeedback.relations (Atoms.ofFormula basis formula)).length ≤ _
  unfold relationBound at *
  omega

theorem tight_learn_storage {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    rowsCells (TightFeedback.learn basis formula) ≤ tightRowsBound n formula.length (Extract.literalCount formula) := by
  have generated := rows_storage n _ (TightFeedback.learn_valid basis inside formula)
  exact generated.trans (Nat.mul_le_mul_right _ (tight_learn_length basis formula))

theorem capacity_learn_length {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (CapacityFeedback.learn basis formula).length ≤ Extract.literalCount formula+formula.length+3 := by
  have bound := Capacity.relations_length (Atoms.ofFormula basis formula)
  have size := atom_formula_size basis formula
  simp only [CapacityFeedback.learn,List.length_map]
  change (Capacity.relations (Atoms.ofFormula basis formula)).length ≤ _
  omega

theorem capacity_learn_storage {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    rowsCells (CapacityFeedback.learn basis formula) ≤ (Extract.literalCount formula+formula.length+3)*(n+2) :=
  (rows_storage n _ (CapacityFeedback.learn_valid basis inside formula)).trans
    (Nat.mul_le_mul_right _ (capacity_learn_length basis formula))

theorem atoms_learn_storage {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    rowsCells (Atoms.learn basis formula) ≤ 2*(formula.length+1)*(n+2) :=
  (rows_storage n _ (Atoms.learn_valid basis inside formula)).trans
    (Nat.mul_le_mul_right _ (Atoms.learn_length basis formula))

/-- Each graph row has the fixed generated group width, including deleted-column probes. -/
def graphBits {m r : Nat} (graph : CapacityMatching.Graph m r) : Nat := graph.toArray.size*r

theorem graphBits_eq {m r : Nat} (graph : CapacityMatching.Graph m r) : graphBits graph = m*r := by
  simp [graphBits]

def cutsStorage {m r : Nat} (cuts : List (CapacityMatching.Cut m r)) : Nat :=
  (cuts.map (fun cut => cut.demands.length+cut.groups.length+2)).sum

theorem tight_cuts_storage {m r : Nat} (graph : CapacityMatching.Graph m r) :
    cutsStorage (CapacityMatching.TightCost.run graph).value ≤ r*(m+r+2) := by
  have length := CapacityMatching.TightCost.run_length graph
  have each : ∀ cut ∈ (CapacityMatching.TightCost.run graph).value,
      cut.demands.length+cut.groups.length+2 ≤ m+r+2 := by
    intro cut member
    have bound := CapacityMatching.RowCost.tight_dimensions graph cut member
    omega
  have all : ∀ cuts : List (CapacityMatching.Cut m r),
      (∀ cut ∈ cuts, cut.demands.length+cut.groups.length+2 ≤ m+r+2) → cutsStorage cuts ≤ cuts.length*(m+r+2) := by
    intro cuts bounded
    induction cuts with
    | nil => simp [cutsStorage]
    | cons cut rest ih =>
        have first := bounded cut (by simp)
        have tail := ih (fun next member => bounded next (by simp [member]))
        simp only [cutsStorage,List.map_cons,List.sum_cons,List.length_cons] at tail ⊢
        nlinarith
  exact (all _ each).trans (Nat.mul_le_mul_right _ length)

theorem setup_graph_size {n : Nat} (formula : CNFFormula n) :
    graphBits (CapacityMatching.SourceCost.setup formula).graph ≤ formula.length*Extract.literalCount formula := by
  have dimensions := CapacityMatching.SourceCost.setup_dimensions formula
  rw [graphBits_eq]
  exact Nat.mul_le_mul dimensions.1 dimensions.2

theorem setup_items_size {n : Nat} (formula : CNFFormula n) :
    (CapacityMatching.SourceCost.setup formula).data.flatten.length ≤ Extract.literalCount formula :=
  CapacityMatching.RowCost.setup_item_count formula

theorem setup_answer_size {n : Nat} (formula : CNFFormula n) :
    CapacityMatching.answerCells (CapacityMatching.generate (CapacityMatching.SourceCost.setup formula).graph).answer ≤
      formula.length+Extract.literalCount formula := by
  have dimensions := CapacityMatching.SourceCost.setup_dimensions formula
  exact (CapacityMatching.generate_storage _).trans (Nat.add_le_add dimensions.1 dimensions.2)

theorem setup_deleted_size {n : Nat} (formula : CNFFormula n)
    (removed : Fin (CapacityMatching.SourceCost.setup formula).data.length) :
    graphBits (CapacityMatching.Tight.without (CapacityMatching.SourceCost.setup formula).graph removed) ≤
        formula.length*Extract.literalCount formula ∧
      CapacityMatching.answerCells
        (CapacityMatching.generate (CapacityMatching.Tight.without (CapacityMatching.SourceCost.setup formula).graph removed)).answer ≤
          formula.length+Extract.literalCount formula := by
  have dimensions := CapacityMatching.SourceCost.setup_dimensions formula
  constructor
  · rw [graphBits_eq]
    exact Nat.mul_le_mul dimensions.1 dimensions.2
  · exact (CapacityMatching.generate_storage _).trans (Nat.add_le_add dimensions.1 dimensions.2)

theorem setup_tight_size {n : Nat} (formula : CNFFormula n) :
    cutsStorage (CapacityMatching.TightCost.run (CapacityMatching.SourceCost.setup formula).graph).value ≤
      Extract.literalCount formula*(formula.length+Extract.literalCount formula+2) := by
  have dimensions := CapacityMatching.SourceCost.setup_dimensions formula
  exact (tight_cuts_storage _).trans (by gcongr <;> omega)

theorem source_reach_size {n : Nat} (formula : CNFFormula n)
    (base : CapacityMatching.Matching (CapacityMatching.SourceCost.setup formula).rows.length
      (CapacityMatching.SourceCost.setup formula).data.length)
    (root : Fin (CapacityMatching.SourceCost.setup formula).rows.length)
    (entries : List (CapacityMatching.Entry (CapacityMatching.SourceCost.setup formula).rows.length
      (CapacityMatching.SourceCost.setup formula).data.length))
    (valid : CapacityMatching.ReachValid (CapacityMatching.SourceCost.setup formula).graph base root entries) :
    entries.length*((CapacityMatching.SourceCost.setup formula).data.length+1) ≤
        formula.length*(Extract.literalCount formula+1) ∧
      (CapacityMatching.pairs entries).length*((CapacityMatching.SourceCost.setup formula).data.length+2) ≤
        formula.length*Extract.literalCount formula*(Extract.literalCount formula+2) := by
  have dimensions := CapacityMatching.SourceCost.setup_dimensions formula
  have bound := CapacityMatching.reach_storage valid
  exact ⟨bound.1.trans (by gcongr <;> omega),bound.2.trans (by gcongr <;> omega)⟩

def graphFamilyBound (clauses literals : Nat) : Nat :=
  (2*(clauses+1)+2*(literals+1))*(6*(literals+1))

theorem atom_graph_family {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    graphBits (CapacityMatching.SourceCost.setup (Atoms.ofFormula basis formula)).graph ≤
        graphFamilyBound formula.length (Extract.literalCount formula) ∧
      graphBits (CapacityMatching.SourceCost.setup (SignedCapacity.expand (Atoms.ofFormula basis formula))).graph ≤
        graphFamilyBound formula.length (Extract.literalCount formula) := by
  have plain := atom_formula_size basis formula
  have mixed := signed_formula_size basis formula
  constructor
  · apply (setup_graph_size _).trans
    unfold graphFamilyBound
    nlinarith [Nat.mul_le_mul plain.1 plain.2]
  · apply (setup_graph_size _).trans
    unfold graphFamilyBound
    exact Nat.mul_le_mul mixed.1 mixed.2

def tightFamilyBound (clauses literals : Nat) : Nat :=
  (6*(literals+1))*(2*(clauses+1)+2*(literals+1)+6*(literals+1)+2)

theorem atom_tight_family {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    cutsStorage (CapacityMatching.TightCost.run
      (CapacityMatching.SourceCost.setup (SignedCapacity.expand (Atoms.ofFormula basis formula))).graph).value ≤
      tightFamilyBound formula.length (Extract.literalCount formula) := by
  have mixed := signed_formula_size basis formula
  apply (setup_tight_size _).trans
  unfold tightFamilyBound
  exact Nat.mul_le_mul mixed.2 (by omega)

theorem prepareStorage_family {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    rowsCells (CapacityMatching.RowCost.prepare (Atoms.ofFormula basis formula)).value ≤
      CapacityMatching.RowCost.prepareStorage (Extract.literalCount formula+1) (formula.length+1)
        (Extract.literalCount formula+1) := by
  have size := atom_formula_size basis formula
  exact (CapacityMatching.RowCost.prepare_storage _).trans
    (prepareStorage_mono _ _ _ _ _ _ (atom_width basis formula) size.1 size.2)

theorem original_initial_storage {n : Nat} (formula : CNFFormula n) :
    rowsCells (Extract.extract formula++(CapacityMatching.RowCost.prepare formula).value) ≤
      5*formula.length+CapacityMatching.RowCost.prepareStorage n formula.length (Extract.literalCount formula) := by
  have extractSize := AffineCollect.Cost.rows_size (Extract.extract formula)
  have extractCount := Extract.extract_length formula
  have extractTerms := EliminateCost.extract_rowTerms formula
  have extra := CapacityMatching.RowCost.prepare_storage formula
  rw [CapacityMatching.RowCost.rowsCells_append,extractSize]
  omega

theorem eliminate_prefix_storage (n : Nat) (rows : List Row) (inside : RowsWithin n rows) (takeCount : Nat) :
    AffineCarrier.resultSize (eliminate (rows.take takeCount)) ≤ AffineCarrier.Cost.cellBound n+1 := by
  have smaller : RowsWithin n (rows.take takeCount) := fun row member => inside row (List.mem_of_mem_take member)
  exact AffineCarrier.Cost.result_size n _ (eliminate_triangular _) (eliminate_within n _ smaller)

theorem tight_prefix_storage {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (formula : CNFFormula n) (takeCount : Nat) :
    AffineCarrier.resultSize (eliminateFrom (.basis basis) ((TightFeedback.learn basis formula).take takeCount)) ≤
      AffineCarrier.Cost.cellBound n+1 := by
  have rowsInside : RowsWithin n ((TightFeedback.learn basis formula).take takeCount) := by
    intro row member
    exact (TightFeedback.learn_valid basis valid.2 formula row (List.mem_of_mem_take member)).2
  exact AffineCarrier.Cost.result_size n _
    (eliminateFrom_triangular (.basis basis) valid.1 _) (eliminateFrom_within n (.basis basis) valid.2 _ rowsInside)

/-- These are the actual four phase inputs and the final state of one strong step. -/
def phaseStates {n : Nat} (formula : CNFFormula n) (initial : Result) : List Result :=
  [initial,Propagation.update formula initial,JointFeedback.step formula initial,
    CapacityFeedback.step formula initial,TightFeedback.step formula initial]

theorem phaseStates_valid {n : Nat} (formula : CNFFormula n) (initial : Result)
    (valid : initial.triangular ∧ initial.within n) :
    ∀ state ∈ phaseStates formula initial, state.triangular ∧ state.within n := by
  have propagated : (Propagation.update formula initial).triangular ∧ (Propagation.update formula initial).within n :=
    ⟨Propagation.update_triangular formula initial valid.1,Propagation.update_within formula initial valid.2⟩
  have atoms := (JointFeedback.step_invariants formula initial valid.2 valid.1).symm
  have capacity := (CapacityFeedback.step_invariants formula initial valid.2 valid.1).symm
  have tight := (TightFeedback.step_invariants formula initial valid.2 valid.1).symm
  intro state member
  simp [phaseStates] at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;> assumption

theorem phaseStates_storage {n : Nat} (formula : CNFFormula n) (initial : Result)
    (valid : initial.triangular ∧ initial.within n) :
    ((phaseStates formula initial).map AffineCarrier.resultSize).sum ≤ 5*(AffineCarrier.Cost.cellBound n+1) := by
  have bounded := phaseStates_valid formula initial valid
  have all : ∀ states : List Result, (∀ state ∈ states, state.triangular ∧ state.within n) →
      (states.map AffineCarrier.resultSize).sum ≤ states.length*(AffineCarrier.Cost.cellBound n+1) := by
    intro states good
    induction states with
    | nil => simp
    | cons state rest ih =>
        have first := AffineCarrier.Cost.result_size n state (good state (by simp)).1 (good state (by simp)).2
        have tail := ih (fun other member => good other (by simp [member]))
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
  simpa only [phaseStates,List.length_cons,List.length_nil] using all _ bounded

theorem phase_learn_family {n : Nat} (formula : CNFFormula n) (initial : Result)
    (valid : initial.triangular ∧ initial.within n) (basis : List Row)
    (member : Result.basis basis ∈ phaseStates formula initial) :
    rowsCells (TightFeedback.learn basis formula) ≤ tightRowsBound n formula.length (Extract.literalCount formula) ∧
      rowsCells (CapacityFeedback.learn basis formula) ≤ (Extract.literalCount formula+formula.length+3)*(n+2) ∧
      rowsCells (Atoms.learn basis formula) ≤ 2*(formula.length+1)*(n+2) := by
  have current := phaseStates_valid formula initial valid (.basis basis) member
  exact ⟨tight_learn_storage basis current.2 formula,capacity_learn_storage basis current.2 formula,
    atoms_learn_storage basis current.2 formula⟩

theorem iterate_phase_family {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) (round : Nat) (basis : List Row)
    (member : Result.basis basis ∈ phaseStates formula (TightFeedback.iterate formula round (eliminate rows))) :
    Triangular basis ∧ RowsWithin n basis ∧
      rowsCells (TightFeedback.learn basis formula) ≤ tightRowsBound n formula.length (Extract.literalCount formula) := by
  have initial := (TightFeedback.iterate_invariants formula round _
    (eliminate_within n rows inside) (eliminate_triangular rows)).symm
  have current := phaseStates_valid formula _ initial (.basis basis) member
  exact ⟨current.1,current.2,tight_learn_storage basis current.2 formula⟩

structure BinaryTrace (n : Nat) where
  value : BinaryRelations.Execution n
  sources : List (CNFFormula n)

/-- The same scans and accepted clauses as `BinaryRelations.run`, with their actual input formulas retained. -/
def traceRun {n : Nat} (candidates : CNFFormula n) : Nat → CNFFormula n → BinaryTrace n
  | 0,formula => ⟨⟨formula,0⟩,[formula]⟩
  | fuel+1,formula =>
      let attempt := BinaryRelations.scan formula candidates
      match attempt.answer with
      | none => ⟨⟨formula,attempt.queries⟩,[formula]⟩
      | some clause =>
          let next := traceRun candidates fuel (clause::formula)
          ⟨⟨next.value.formula,attempt.queries+next.value.queries⟩,formula::next.sources⟩

theorem traceRun_value {n : Nat} (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n) :
    (traceRun candidates fuel formula).value = BinaryRelations.run candidates fuel formula := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : (BinaryRelations.scan formula candidates).answer <;>
        simp only [traceRun,BinaryRelations.run,found,ih]

theorem traceRun_final {n : Nat} (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n) :
    (traceRun candidates fuel formula).value.formula ∈ (traceRun candidates fuel formula).sources := by
  induction fuel generalizing formula with
  | zero => simp [traceRun]
  | succ fuel ih =>
      cases found : (BinaryRelations.scan formula candidates).answer with
      | none => simp [traceRun,found]
      | some clause =>
          have tail := ih (clause::formula)
          simpa only [traceRun,found] using List.mem_cons_of_mem formula tail

theorem traceRun_size {n : Nat} (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n) :
    (traceRun candidates fuel formula).sources.length ≤ fuel+1 := by
  induction fuel generalizing formula with
  | zero => simp [traceRun]
  | succ fuel ih =>
      cases found : (BinaryRelations.scan formula candidates).answer with
      | none => simp [traceRun,found]
      | some clause => simpa only [traceRun,found,List.length_cons] using Nat.add_le_add_right (ih (clause::formula)) 1

theorem traceRun_family {n : Nat} (candidates : CNFFormula n)
    (binary : ∀ clause ∈ candidates, clause.length=2) (fuel : Nat) (formula source : CNFFormula n)
    (member : source ∈ (traceRun candidates fuel formula).sources) :
    source.length ≤ formula.length+fuel ∧ Extract.literalCount source ≤ Extract.literalCount formula+2*fuel := by
  induction fuel generalizing formula with
  | zero =>
      have same : source=formula := by simpa [traceRun] using member
      subst source
      simp
  | succ fuel ih =>
      cases found : (BinaryRelations.scan formula candidates).answer with
      | none =>
          have same : source=formula := by simpa [traceRun,found] using member
          subst source
          constructor <;> omega
      | some clause =>
          simp only [traceRun,found,List.mem_cons] at member
          rcases member with rfl | later
          · constructor <;> omega
          · have tail := ih (clause::formula) later
            have clauseSize := binary clause (BinaryRelations.scan_spec formula candidates clause found).1
            simp only [List.length_cons,Extract.literalCount,List.map_cons,List.sum_cons,clauseSize] at tail
            change _ ≤ _ ∧ (source.map List.length).sum ≤ (formula.map List.length).sum+_
            constructor <;> omega

def traceGenerate {n : Nat} (formula : CNFFormula n) : BinaryTrace n :=
  traceRun (BinaryRelations.inventory n) (BinaryRelations.inventory n).length formula

theorem traceGenerate_value {n : Nat} (formula : CNFFormula n) :
    (traceGenerate formula).value = BinaryRelations.generate formula := traceRun_value _ _ _

def augmentedClauses (n clauses : Nat) : Nat := clauses+4*n*n

def augmentedLiterals (n literals : Nat) : Nat := literals+8*n*n

theorem binary_family {n : Nat} (formula source : CNFFormula n)
    (member : source ∈ (traceGenerate formula).sources) :
    source.length ≤ augmentedClauses n formula.length ∧
      Extract.literalCount source ≤ augmentedLiterals n (Extract.literalCount formula) := by
  have bounded := traceRun_family (BinaryRelations.inventory n)
    (fun clause present => BinaryRelations.inventory_clause clause present) _ formula source member
  simpa only [BinaryRelations.inventory_length,augmentedClauses,augmentedLiterals,← Nat.mul_assoc,Nat.reduceMul] using bounded

theorem binary_family_count {n : Nat} (formula : CNFFormula n) :
    (traceGenerate formula).sources.length ≤ 4*n*n+1 := by
  simpa only [traceGenerate,BinaryRelations.inventory_length] using traceRun_size (BinaryRelations.inventory n) _ formula

def sourceRecords {n : Nat} (formula : CNFFormula n) : Nat := 3*Extract.literalCount formula+2*formula.length+1

theorem binary_retained_storage {n : Nat} (formula : CNFFormula n) :
    ((traceGenerate formula).sources.map sourceRecords).sum ≤
      (4*n*n+1)*(3*augmentedLiterals n (Extract.literalCount formula)+2*augmentedClauses n formula.length+1) := by
  have number := binary_family_count formula
  have each : ∀ source ∈ (traceGenerate formula).sources,
      sourceRecords source ≤ 3*augmentedLiterals n (Extract.literalCount formula)+2*augmentedClauses n formula.length+1 := by
    intro source member
    have bounds := binary_family formula source member
    unfold sourceRecords
    omega
  have all : ∀ sources : List (CNFFormula n),
      (∀ source ∈ sources, sourceRecords source ≤
        3*augmentedLiterals n (Extract.literalCount formula)+2*augmentedClauses n formula.length+1) →
      (sources.map sourceRecords).sum ≤ sources.length*
        (3*augmentedLiterals n (Extract.literalCount formula)+2*augmentedClauses n formula.length+1) := by
    intro sources bounded
    induction sources with
    | nil => simp
    | cons source rest ih =>
        have first := bounded source (by simp)
        have tail := ih (fun next member => bounded next (by simp [member]))
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
  exact (all _ each).trans (Nat.mul_le_mul_right _ number)

theorem binary_queries {n : Nat} (formula : CNFFormula n) :
    (traceGenerate formula).value.queries ≤ 16*n^4 := by
  rw [traceGenerate_value]
  exact BinaryRelations.generate_queries formula

/-- Bounds refer to the actual intermediate producers, rather than only their final bases. -/
structure Family (n clauses literals : Nat) (basis : List Row) (formula : CNFFormula n) : Prop where
  basisRows : basis.length ≤ n
  basisStorage : AffineCarrier.cellSize basis ≤ AffineCarrier.Cost.cellBound n
  dataStorage : rowsCells (Atoms.data basis formula).flatten ≤ literals*(n+2)
  atoms : (Atoms.keys (Atoms.data basis formula)).length ≤ literals+1
  tableStorage : rowsCells (Atoms.table (Atoms.data basis formula)).toList ≤ (literals+1)*(n+2)
  atomClauses : (Atoms.ofFormula basis formula).length ≤ clauses+1
  atomLiterals : Extract.literalCount (Atoms.ofFormula basis formula) ≤ literals+1
  signedClauses : (SignedCapacity.expand (Atoms.ofFormula basis formula)).length ≤ 2*(clauses+1)+2*(literals+1)
  signedLiterals : Extract.literalCount (SignedCapacity.expand (Atoms.ofFormula basis formula)) ≤ 6*(literals+1)
  plainGraph : graphBits (CapacityMatching.SourceCost.setup (Atoms.ofFormula basis formula)).graph ≤ graphFamilyBound clauses literals
  signedGraph : graphBits (CapacityMatching.SourceCost.setup (SignedCapacity.expand (Atoms.ofFormula basis formula))).graph ≤
    graphFamilyBound clauses literals
  tightCuts : cutsStorage (CapacityMatching.TightCost.run
    (CapacityMatching.SourceCost.setup (SignedCapacity.expand (Atoms.ofFormula basis formula))).graph).value ≤
      tightFamilyBound clauses literals
  preparedRows : rowsCells (CapacityMatching.RowCost.prepare (Atoms.ofFormula basis formula)).value ≤
    CapacityMatching.RowCost.prepareStorage (literals+1) (clauses+1) (literals+1)
  decodedTight : rowsCells (TightFeedback.learn basis formula) ≤ tightRowsBound n clauses literals
  decodedCapacity : rowsCells (CapacityFeedback.learn basis formula) ≤ (literals+clauses+3)*(n+2)
  decodedAtoms : rowsCells (Atoms.learn basis formula) ≤ 2*(clauses+1)*(n+2)

theorem family {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (formula : CNFFormula n) (clauses literals : Nat)
    (number : formula.length ≤ clauses) (terms : Extract.literalCount formula ≤ literals) :
    Family n clauses literals basis formula := by
  have atomSizes := atom_formula_size basis formula
  have signedSizes := signed_formula_size basis formula
  have graphs := atom_graph_family basis formula
  have graphBound : graphFamilyBound formula.length (Extract.literalCount formula) ≤ graphFamilyBound clauses literals := by
    unfold graphFamilyBound
    exact Nat.mul_le_mul (by omega) (by omega)
  have cutBound : tightFamilyBound formula.length (Extract.literalCount formula) ≤ tightFamilyBound clauses literals := by
    unfold tightFamilyBound
    exact Nat.mul_le_mul (by omega) (by omega)
  have rowBound := prepareStorage_mono (Extract.literalCount formula+1) (literals+1)
    (formula.length+1) (clauses+1) (Extract.literalCount formula+1) (literals+1)
    (Nat.add_le_add_right terms 1) (Nat.add_le_add_right number 1) (Nat.add_le_add_right terms 1)
  have decodedBound : tightRowsBound n formula.length (Extract.literalCount formula) ≤ tightRowsBound n clauses literals := by
    exact Nat.mul_le_mul_right (n+2) (Nat.add_le_add_right rowBound 2)
  have capBound : (Extract.literalCount formula+formula.length+3)*(n+2) ≤ (literals+clauses+3)*(n+2) :=
    Nat.mul_le_mul_right (n+2) (by omega)
  have atomBound : 2*(formula.length+1)*(n+2) ≤ 2*(clauses+1)*(n+2) := Nat.mul_le_mul_right (n+2) (by omega)
  exact {
    basisRows := basis_length_le n basis valid.1 valid.2
    basisStorage := AffineCarrier.Cost.cell_size n basis valid.1 valid.2
    dataStorage := (data_storage basis valid.2 formula).trans (Nat.mul_le_mul_right (n+2) terms)
    atoms := (atom_width basis formula).trans (Nat.add_le_add_right terms 1)
    tableStorage := (atom_table_storage basis valid.2 formula).trans
      (Nat.mul_le_mul_right (n+2) (Nat.add_le_add_right terms 1))
    atomClauses := atomSizes.1.trans (Nat.add_le_add_right number 1)
    atomLiterals := atomSizes.2.trans (Nat.add_le_add_right terms 1)
    signedClauses := signedSizes.1.trans (by omega)
    signedLiterals := signedSizes.2.trans (by omega)
    plainGraph := graphs.1.trans graphBound
    signedGraph := graphs.2.trans graphBound
    tightCuts := (atom_tight_family basis formula).trans cutBound
    preparedRows := (prepareStorage_family basis formula).trans rowBound
    decodedTight := (tight_learn_storage basis valid.2 formula).trans decodedBound
    decodedCapacity := (capacity_learn_storage basis valid.2 formula).trans capBound
    decodedAtoms := (atoms_learn_storage basis valid.2 formula).trans atomBound }

/-- The two-row input and every phase of every actual strong query stay at the original dimension. -/
theorem binary_feedback_family {n : Nat} (original source : CNFFormula n)
    (sourceMember : source ∈ (traceGenerate original).sources) (clause : CNFClause n)
    (candidate : clause ∈ BinaryRelations.inventory n) (round : Nat) (basis : List Row)
    (state : Result.basis basis ∈ phaseStates source
      (TightFeedback.iterate source round (eliminate (clause.map Propagation.badLiteral)))) :
    rowsCells (clause.map Propagation.badLiteral) = 6 ∧
      Family n (augmentedClauses n original.length) (augmentedLiterals n (Extract.literalCount original)) basis source := by
  have bounded := binary_family original source sourceMember
  have valid := iterate_phase_family source _ (AffineCarrier.Cost.bad_inside clause) round basis state
  have size := BinaryRelations.inventory_clause clause candidate
  constructor
  · rw [AffineCollect.Cost.rows_size,AffineCarrier.Cost.bad_terms,List.length_map,size]
  · exact family basis ⟨valid.1,valid.2.1⟩ source _ _ bounded.1 bounded.2

theorem seed_rows_within {n : Nat} (formula : CNFFormula n) :
    RowsWithin n (Extract.extract formula++(CapacityMatching.RowCost.prepare formula).value) := by
  rw [CapacityMatching.RowCost.prepare_value]
  intro row member
  rcases List.mem_append.mp member with first | second
  · exact extract_rowsWithin formula row first
  · exact CapacityMatching.SourceTight.prepare_within formula row second

/-- This is the enhanced formula and strongest seed consumed by the converged source entrance. -/
theorem strongest_seed_family {n : Nat} (original : CNFFormula n) (round : Nat) (basis : List Row)
    (state : Result.basis basis ∈ phaseStates (BinaryRelations.generate original).formula
      (TightFeedback.iterate (BinaryRelations.generate original).formula round
        (eliminate (Extract.extract (BinaryRelations.generate original).formula++
          (CapacityMatching.RowCost.prepare (BinaryRelations.generate original).formula).value)))) :
    Family n (augmentedClauses n original.length) (augmentedLiterals n (Extract.literalCount original))
      basis (BinaryRelations.generate original).formula := by
  have final := traceRun_final (BinaryRelations.inventory n) (BinaryRelations.inventory n).length original
  change (traceGenerate original).value.formula ∈ (traceGenerate original).sources at final
  rw [traceGenerate_value] at final
  have bounded := binary_family original (BinaryRelations.generate original).formula final
  have valid := iterate_phase_family (BinaryRelations.generate original).formula _
    (seed_rows_within _) round basis state
  exact family basis ⟨valid.1,valid.2.1⟩ _ _ _ bounded.1 bounded.2

theorem strongest_initial_storage {n : Nat} (original : CNFFormula n) :
    rowsCells (Extract.extract (BinaryRelations.generate original).formula++
      (CapacityMatching.RowCost.prepare (BinaryRelations.generate original).formula).value) ≤
      5*augmentedClauses n original.length+
        CapacityMatching.RowCost.prepareStorage n (augmentedClauses n original.length)
          (augmentedLiterals n (Extract.literalCount original)) := by
  have number := BinaryRelations.generate_length original
  have terms := BinaryRelations.generate_literals original
  have generated := original_initial_storage (BinaryRelations.generate original).formula
  have bound := prepareStorage_mono n n _ (augmentedClauses n original.length) _
    (augmentedLiterals n (Extract.literalCount original)) (Nat.le_refl _) number terms
  exact generated.trans (by unfold augmentedClauses at *; omega)

theorem prepareBudget_mono (n N m M ell E : Nat) (width : n ≤ N) (number : m ≤ M) (terms : ell ≤ E) :
    CapacityMatching.RowCost.prepareBudget n m ell ≤ CapacityMatching.RowCost.prepareBudget N M E := by
  unfold CapacityMatching.RowCost.prepareBudget CapacityMatching.RowCost.bothBudget
    CapacityMatching.RowCost.rowsBudget CapacityMatching.RowCost.coordinateBudget
    CapacityMatching.RowCost.decodeBudget CapacityMatching.RowCost.decodeUnit
    CapacityMatching.RowCost.previousStorage CapacityMatching.RowCost.currentStorage
    CapacityMatching.RowCost.renderBudget CapacityMatching.RowCost.oneBudget
    CapacityMatching.RowCost.groupBudget CapacityMatching.RowCost.outsideBudget
    CapacityMatching.RowCost.capacityBudget CapacityMatching.SourceCost.setupBound
    CapacityMatching.TightCost.runBudget CapacityMatching.TightCost.probeBudget
    CapacityMatching.TightCost.generateBudget CapacityMatching.solveUnits CapacityMatching.roundUnits
  gcongr

theorem prepare_copies_family {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (CapacityMatching.RowCost.prepare (Atoms.ofFormula basis formula)).cells ≤
      CapacityMatching.RowCost.prepareBudget (Extract.literalCount formula+1) (formula.length+1)
        (Extract.literalCount formula+1) := by
  have size := atom_formula_size basis formula
  exact (CapacityMatching.RowCost.prepare_cells _).trans
    (prepareBudget_mono _ _ _ _ _ _ (atom_width basis formula) size.1 size.2)

theorem relation_storage_family {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    rowsCells (TightFeedback.relations (Atoms.ofFormula basis formula)) ≤
      relationBound (Extract.literalCount formula+1) (formula.length+1) (Extract.literalCount formula+1) := by
  have size := atom_formula_size basis formula
  have next := prepareStorage_mono _ _ _ _ _ _ (atom_width basis formula) size.1 size.2
  exact (tight_relations_storage _).trans (Nat.add_le_add_right next 2)

/-- This receipt executes the shared table decoder used by `TightFeedback.learn`.
Its ledger covers the decoder and output copying; source-view construction is separate. -/
def decodeLearn {n : Nat} (basis : List Row) (formula : CNFFormula n) : CapacityMatching.SourceCost.Counted (List Row) :=
  let source := Atoms.data basis formula
  let table := Atoms.table source
  let generated := TightFeedback.relations (Subsumption.reduce (Atoms.compile source))
  CapacityMatching.RowCost.decodeRows table generated

theorem decodeLearn_value {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (decodeLearn basis formula).value = TightFeedback.learn basis formula := by
  simp only [decodeLearn,CapacityMatching.RowCost.decodeRows_value,TightFeedback.learn]

theorem decodeBudget_mono (n size large rows more : Nat) (table : size ≤ large) (storage : rows ≤ more) :
    CapacityMatching.RowCost.decodeBudget n size rows ≤ CapacityMatching.RowCost.decodeBudget n large more := by
  unfold CapacityMatching.RowCost.decodeBudget CapacityMatching.RowCost.decodeUnit
  gcongr

def decodeCopiesBound (n clauses literals : Nat) : Nat :=
  CapacityMatching.RowCost.decodeBudget n (literals+1) (relationBound (literals+1) (clauses+1) (literals+1))

theorem decodeLearn_cells {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    (decodeLearn basis formula).cells ≤ decodeCopiesBound n formula.length (Extract.literalCount formula) := by
  have table := Atoms.table_valid n _ (Atoms.data_valid basis inside formula)
  have decoded := CapacityMatching.RowCost.decodeRows_cells n _ table
    (TightFeedback.relations (Atoms.ofFormula basis formula))
  rw [atom_table_size] at decoded
  exact decoded.trans (decodeBudget_mono n _ _ _ _ (atom_width basis formula) (relation_storage_family basis formula))

theorem decodeLearn_intermediate {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n)
    (row : Row) (takeCount : Nat) :
    rowCells (Table.combine (Atoms.table (Atoms.data basis formula)) (row.vars.take takeCount) ⟨[],row.rhs⟩) ≤ n+2 := by
  have table := Atoms.table_valid n _ (Atoms.data_valid basis inside formula)
  have valid := Table.combine_valid n _ table (row.vars.take takeCount) ⟨[],row.rhs⟩
    (by simp [Table.RowValid,Parity.Within])
  exact Nat.add_le_add_right (Table.row_length_le n _ valid) 2

/-- The generated decoder rows are immediately consumed by the original Gaussian advance. -/
def advanceDecoded {n : Nat} (basis : List Row) (formula : CNFFormula n) : CapacityMatching.SourceCost.Counted Result :=
  let rows := decodeLearn basis formula
  let next := EliminateCost.runFrom (.basis basis) rows.value
  ⟨next.result,rows.cells+next.cells+2*rowsCells rows.value+2*AffineCarrier.resultSize next.result+3⟩

theorem advanceDecoded_value {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (advanceDecoded basis formula).value = TightFeedback.advance formula (.basis basis) := by
  simp only [advanceDecoded,decodeLearn_value,EliminateCost.runFrom_result,TightFeedback.advance]

def advanceCopiesBound (n clauses literals : Nat) : Nat :=
  decodeCopiesBound n clauses literals+
    tightRowsBound n clauses literals*(2*n+EliminateCost.insertCellBudget n+8)+
      2*(AffineCarrier.Cost.cellBound n+1)+4

private theorem advance_numbers (a b stored output d bound unit outBound : Nat)
    (decoder : a ≤ d) (gaussian : b ≤ bound*unit+1) (source : stored ≤ bound) (result : output ≤ outBound) :
    a+b+2*stored+2*output+3 ≤ d+bound*(unit+2)+2*outBound+4 := by nlinarith

theorem advanceDecoded_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (formula : CNFFormula n) :
    (advanceDecoded basis formula).cells ≤ advanceCopiesBound n formula.length (Extract.literalCount formula) := by
  have decoded := decodeLearn_cells basis valid.2 formula
  have size := tight_learn_storage basis valid.2 formula
  have measures := AffineCarrier.Cost.row_measures (TightFeedback.learn basis formula)
  have inside : RowsWithin n (TightFeedback.learn basis formula) :=
    fun row member => (TightFeedback.learn_valid basis valid.2 formula row member).2
  simp only [advanceDecoded,decodeLearn_value]
  generalize generated : TightFeedback.learn basis formula = learned at *
  have eliminated := EliminateCost.runFrom_cells n (.basis basis) valid.1 valid.2 learned inside
  have termBound := measures.2.trans size
  have rowBound := measures.1.trans size
  have gaussianBound : (EliminateCost.runFrom (.basis basis) learned).cells ≤
      tightRowsBound n formula.length (Extract.literalCount formula)*(2*n+EliminateCost.insertCellBudget n+6)+1 := by
    apply eliminated.trans
    calc
      _ ≤ tightRowsBound n formula.length (Extract.literalCount formula)*(2*n+5)+
          tightRowsBound n formula.length (Extract.literalCount formula)*(EliminateCost.insertCellBudget n+1)+1 :=
        Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_right _ termBound) (Nat.mul_le_mul_right _ rowBound)) 1
      _ = _ := by ring
  have nextTriangular := eliminateFrom_triangular (.basis basis) valid.1 learned
  have nextWithin := eliminateFrom_within n (.basis basis) valid.2 learned inside
  have resultSize := AffineCarrier.Cost.result_size n (eliminateFrom (.basis basis) learned) nextTriangular nextWithin
  have total := advance_numbers _ _ _ _ _ _ _ _ decoded gaussianBound size resultSize
  simpa only [EliminateCost.runFrom_result,advanceCopiesBound,Nat.add_assoc] using total

end SaturationMonoid.ComplexityProjection.SATSource.StrongFeedbackScale
