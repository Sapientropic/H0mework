import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ConditionalCandidateCost

/-! Paired construction of the original acceptance program. Source literals,
    coordinate rows, lookup results and node records are generated once and
    shared by their consumers. Bills include complete array/list payload copies;
    scalar/address bits and counter evaluation have separate machine costs. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalSourceCost.Initial
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open CapacityMatching.RowCost (rowCells rowsCells)
abbrev Counted := CapacityMatching.SourceCost.Counted
abbrev formulaRecords := @CapacityMatching.RowCost.formulaCells

def literal {n : Nat} (source : CNFLiteral n) : Counted Fragment :=
  let result := ConditionalCandidateCost.Code.signed (!source.positive) (Fragment.input source.var.val)
  ⟨result.value,result.cells+10⟩

theorem literal_value {n : Nat} (source : CNFLiteral n) : (literal source).value=compileLiteral source := by
  cases sign : source.positive <;>
    simp [literal,ConditionalCandidateCost.Code.signed,ConditionalCandidateCost.Code.negate,compileLiteral,sign]

theorem literal_size {n : Nat} (source : CNFLiteral n) : (literal source).value.code.size ≤ 2 := by
  have output := ConditionalCandidateCost.Code.signed_size (!source.positive) (Fragment.input source.var.val)
  change (literal source).value.code.size ≤ 2 at output
  exact output

theorem literal_cells {n : Nat} (source : CNFLiteral n) : (literal source).cells ≤ 52 := by
  have output := ConditionalCandidateCost.Code.signed_cells (!source.positive) (Fragment.input source.var.val)
  change (ConditionalCandidateCost.Code.signed (!source.positive) (Fragment.input source.var.val)).cells ≤ 42 at output
  simp only [literal]
  omega

def clause {n : Nat} : CNFClause n → Counted Fragment
  | [] => ⟨Fragment.constant 1,8⟩
  | source::rest =>
      let first := literal source
      let tail := clause rest
      let output := ConditionalCandidateCost.Code.binary true first.value tail.value
      ⟨output.value,first.cells+tail.cells+output.cells+4*output.value.code.size+8⟩

theorem clause_value {n : Nat} (source : CNFClause n) : (clause source).value=compileClause source := by
  induction source with
  | nil => rfl
  | cons source rest ih =>
      simp only [clause,literal_value,ih,ConditionalCandidateCost.Code.binary,compileClause,if_true]

theorem clause_size {n : Nat} (source : CNFClause n) : (clause source).value.code.size ≤ 1+3*source.length := by
  rw [clause_value]
  exact InterferenceDecision.compileClause_size source

def clauseBudget (length : Nat) : Nat := (length+1)*(100*length+150)

theorem clause_cells {n : Nat} (source : CNFClause n) : (clause source).cells ≤ clauseBudget source.length := by
  induction source with
  | nil => simp [clause,clauseBudget]
  | cons source rest ih =>
      have first := literal_cells source
      have firstSize := literal_size source
      have tailSize := clause_size rest
      have outputSize := ConditionalCandidateCost.Code.binary_size true (literal source).value (clause rest).value
      have outputWork : (ConditionalCandidateCost.Code.binary true (literal source).value (clause rest).value).cells ≤
          60*rest.length+100 := by
        change 20*((literal source).value.code.size+(clause rest).value.code.size+1)+20 ≤ _
        omega
      simp only [clause,clauseBudget,List.length_cons] at *
      nlinarith

theorem clauseBudget_mono (small large : Nat) (bound : small ≤ large) : clauseBudget small ≤ clauseBudget large := by
  unfold clauseBudget
  gcongr

def original {n : Nat} : CNFFormula n → Counted Fragment
  | [] => ⟨Fragment.constant 1,8⟩
  | source::rest =>
      let first := clause source
      let positive := ConditionalCandidateCost.Code.negate first.value
      let tail := original rest
      let output := ConditionalCandidateCost.Code.binary true positive.value tail.value
      ⟨output.value,first.cells+positive.cells+tail.cells+output.cells+
        2*(formulaRecords (source::rest)+first.value.code.size+tail.value.code.size+output.value.code.size)+10⟩

theorem original_value {n : Nat} (source : CNFFormula n) : (original source).value=Acceptance.original source := by
  induction source with
  | nil => rfl
  | cons source rest ih =>
      simp only [original,clause_value,ih,ConditionalCandidateCost.Code.binary,ConditionalCandidateCost.Code.negate,Acceptance.original,if_true]

theorem original_size {n : Nat} (source : CNFFormula n) : (original source).value.code.size ≤ 2*formulaRecords source := by
  have output := Acceptance.original_size source
  change (Acceptance.original source).code.size ≤ 1+3*source.length+3*Extract.literalCount source at output
  rw [original_value]
  unfold formulaRecords CapacityMatching.RowCost.formulaCells
  omega

def originalRound (size : Nat) : Nat := clauseBudget size+200*(size+2)

theorem original_cells_aux {n : Nat} (source : CNFFormula n) (size : Nat) (bounded : formulaRecords source ≤ size) :
    (original source).cells ≤ source.length*originalRound size+8 := by
  induction source with
  | nil => simp [original]
  | cons source rest ih =>
      have total : 3*source.length+formulaRecords rest+2 ≤ size := by
        simpa only [formulaRecords,AffineRelationExtractionCost.size_cons] using bounded
      have tail := ih (by omega)
      have first := (clause_cells source).trans (clauseBudget_mono _ size (by omega))
      have firstSize := clause_size source
      have tailSize := original_size rest
      have positiveSize := ConditionalCandidateCost.Code.negate_size (clause source).value
      have positiveWork : (ConditionalCandidateCost.Code.negate (clause source).value).cells ≤ 36*size+34 := by
        change 12*((clause source).value.code.size+1)+10 ≤ _
        omega
      have outputSize := original_size (source::rest)
      have outputWork : (ConditionalCandidateCost.Code.binary true
          (ConditionalCandidateCost.Code.negate (clause source).value).value (original rest).value).cells ≤ 100*size+80 := by
        change 20*((ConditionalCandidateCost.Code.negate (clause source).value).value.code.size+(original rest).value.code.size+1)+20 ≤ _
        omega
      simp only [original,List.length_cons] at outputSize ⊢
      unfold originalRound at tail ⊢
      nlinarith

def originalBudget (clauses literals : Nat) : Nat := clauses*originalRound (3*literals+2*clauses+1)+8

theorem original_cells {n : Nat} (source : CNFFormula n) :
    (original source).cells ≤ originalBudget source.length (Extract.literalCount source) :=
  original_cells_aux source (formulaRecords source) (by omega)

def rows : List Row → Counted Gates.CoordinateCode
  | [] => ⟨⟨#[.constant 0],[]⟩,8⟩
  | row::rest =>
      let previous := rows rest
      let generated := ConditionalCandidateCost.Code.compileRow row
      let code := join previous.value.code generated.value.code
      let outputs := (previous.value.code.size+generated.value.output.val)::previous.value.outputs
      ⟨⟨code,outputs⟩,previous.cells+generated.cells+
        20*(previous.value.code.size+generated.value.code.size+1)+
        4*(code.size+outputs.length)+2*rowCells row+12⟩

theorem rows_value (source : List Row) : (rows source).value=Gates.compileRows source := by
  induction source with
  | nil => rfl
  | cons row rest ih =>
      have code := congrArg (fun value : Fragment => value.code) (ConditionalCandidateCost.Code.compileRow_value row)
      have output := congrArg (fun value : Fragment => value.output.val) (ConditionalCandidateCost.Code.compileRow_value row)
      simp only [rows,Gates.compileRows,ih,code,output]

theorem rows_outputs (source : List Row) : (rows source).value.outputs.length=source.length := by
  rw [rows_value,Gates.compileRows_outputs_length]

theorem rows_size (source : List Row) : (rows source).value.code.size ≤ 2*rowsCells source+1 := by
  rw [rows_value,Gates.compileRows_size,AffineCollect.Cost.rows_size]
  omega

def rowsRound (size : Nat) : Nat := ConditionalCandidateCost.Code.compileBudget size+160*(size+2)

theorem rows_cells_aux (source : List Row) (size : Nat) (bounded : rowsCells source ≤ size) :
    (rows source).cells ≤ source.length*rowsRound size+8 := by
  induction source with
  | nil => simp [rows]
  | cons row rest ih =>
      have total : rowCells row+rowsCells rest ≤ size := by simpa only [CapacityMatching.RowCost.rowsCells_cons] using bounded
      have tail := ih (by omega)
      have first := (ConditionalCandidateCost.Code.compileRow_cells row).trans
        (ConditionalCandidateCost.Code.compileBudget_mono _ size (by unfold rowCells at total; omega))
      have previousSize := rows_size rest
      have generatedSize := ConditionalCandidateCost.Code.compileRow_size row
      have outputs := rows_outputs rest
      have count := ConditionalCandidateCost.Code.rows_length rest
      have final := rows_size (row::rest)
      simp only [rows,List.length_cons] at final ⊢
      rw [join_size]
      unfold rowCells at total ⊢
      unfold rowsRound at tail ⊢
      nlinarith

def rowsBudget (size : Nat) : Nat := size*rowsRound size+8

theorem rows_cells (source : List Row) (size : Nat) (bounded : rowsCells source ≤ size) :
    (rows source).cells ≤ rowsBudget size := by
  have first := rows_cells_aux source size bounded
  have count := ConditionalCandidateCost.Code.rows_length source
  apply first.trans
  unfold rowsBudget
  gcongr
  omega

def amplitude (source : Fragment) : Counted Program :=
  ⟨InterferenceDecision.fromAmplitude source,12*(source.code.size+1)+20⟩

theorem amplitude_size (source : Fragment) : (amplitude source).value.code.size=source.code.size+1 := by
  simp [amplitude,InterferenceDecision.fromAmplitude]

def rewriteNode (n offset : Nat) (outputs : List Nat) : Node → Counted Node
  | .input i => if i<n then
      let found := Gates.lookup outputs i
      ⟨.bxor found.1 0,found.2+7⟩
    else ⟨.input (i-n),6⟩
  | node => ⟨node.shift offset,12⟩

theorem rewriteNode_value (n offset : Nat) (outputs : List Nat) (node : Node) :
    (rewriteNode n offset outputs node).value=Gates.rewriteNode n 0 offset outputs node := by
  cases node <;> simp only [rewriteNode,Gates.rewriteNode,Nat.zero_add]
  split <;> rfl

theorem rewriteNode_cells (n offset : Nat) (outputs : List Nat) (node : Node) :
    (rewriteNode n offset outputs node).cells ≤ outputs.length+12 := by
  cases node <;> simp only [rewriteNode]
  case input i =>
    have found := Gates.lookup_visits outputs i
    split <;> simp only <;> omega
  all_goals omega

def rewrite (n offset : Nat) (outputs : List Nat) (source : Array Node) : Counted (Array Node) :=
  let paired := source.map (rewriteNode n offset outputs)
  let output := paired.map (·.value)
  ⟨output,(paired.toList.map (·.cells)).sum+12*source.size+12*output.size+8*outputs.length+12⟩

theorem rewrite_value (n offset : Nat) (outputs : List Nat) (source : Array Node) :
    (rewrite n offset outputs source).value=source.map (Gates.rewriteNode n 0 offset outputs) := by
  simp only [rewrite,Array.map_map]
  apply Array.map_congr_left
  intro node _
  exact rewriteNode_value n offset outputs node

theorem rewrite_size (n offset : Nat) (outputs : List Nat) (source : Array Node) :
    (rewrite n offset outputs source).value.size=source.size := by simp only [rewrite_value,Array.size_map]

def rewriteBudget (count outputs : Nat) : Nat := count*(outputs+36)+8*outputs+12

theorem rewrite_cells (n offset : Nat) (outputs : List Nat) (source : Array Node) :
    (rewrite n offset outputs source).cells ≤ rewriteBudget source.size outputs.length := by
  have bound : ∀ nodes : List Node,
      (nodes.map (fun node => (rewriteNode n offset outputs node).cells)).sum ≤ nodes.length*(outputs.length+12) := by
    intro nodes
    induction nodes with
    | nil => simp
    | cons node rest ih =>
        have first := rewriteNode_cells n offset outputs node
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
  have sourceBound := bound source.toList
  simp only [Array.length_toList] at sourceBound
  simp only [rewrite,Array.toList_map,List.map_map,Array.size_map,rewriteBudget,Function.comp_def]
  nlinarith

def compile {n : Nat} (table : Array Row) (formula : CNFFormula n) : Counted Program :=
  let source := rows table.toList
  let raw := original formula
  let accepted := amplitude raw.value
  let rewritten := rewrite n source.value.code.size source.value.outputs accepted.value.code
  have mappedSize : rewritten.value.size=accepted.value.code.size := rewrite_size _ _ _ _
  let code := source.value.code++rewritten.value
  let output : Program := ⟨code,
    ⟨source.value.code.size+accepted.value.weight.val,by
      simpa only [code,Array.size_append,mappedSize] using
        Nat.add_lt_add_left accepted.value.weight.isLt source.value.code.size⟩,
    ⟨source.value.code.size+accepted.value.phase.val,by
      simpa only [code,Array.size_append,mappedSize] using
        Nat.add_lt_add_left accepted.value.phase.isLt source.value.code.size⟩⟩
  ⟨output,source.cells+raw.cells+accepted.cells+rewritten.cells+
    12*(source.value.code.size+accepted.value.code.size+rewritten.value.size+code.size)+
    2*(AffineCollect.tableSize table+formulaRecords formula+source.value.outputs.length)+20⟩

private theorem program_ext (left right : Program) (code : left.code=right.code)
    (weight : left.weight.val=right.weight.val) (phase : left.phase.val=right.phase.val) : left=right := by
  cases left with
  | mk leftCode leftWeight leftPhase =>
      cases right with
      | mk rightCode rightWeight rightPhase =>
          dsimp only at code weight phase
          cases code
          have weights := Fin.ext weight
          have phases := Fin.ext phase
          cases weights
          cases phases
          rfl

theorem compile_value {n : Nat} (table : Array Row) (formula : CNFFormula n) :
    (compile table formula).value=Acceptance.compile table formula := by
  apply program_ext
  · simp only [compile,rows_value,original_value,amplitude,rewrite_value,Acceptance.compile]
  · have same := congrArg (fun source : Fragment => (InterferenceDecision.fromAmplitude source).weight.val) (original_value formula)
    simp only [compile,rows_value,amplitude,Acceptance.compile]
    exact congrArg (fun i => (Gates.compileRows table.toList).code.size+i) same
  · have same := congrArg (fun source : Fragment => (InterferenceDecision.fromAmplitude source).phase.val) (original_value formula)
    simp only [compile,rows_value,amplitude,Acceptance.compile]
    exact congrArg (fun i => (Gates.compileRows table.toList).code.size+i) same

def compileBudget (tableSize clauses literals : Nat) : Nat :=
  rowsBudget tableSize+originalBudget clauses literals+12*(2*(3*literals+2*clauses+1)+1)+20+
    rewriteBudget (2*(3*literals+2*clauses+1)+1) tableSize+
    12*(2*(2*tableSize+1)+3*(2*(3*literals+2*clauses+1)+1))+
    2*(2*tableSize+(3*literals+2*clauses+1))+20

theorem compile_cells {n : Nat} (table : Array Row) (formula : CNFFormula n) (size : Nat)
    (bounded : AffineCollect.tableSize table ≤ size) :
    (compile table formula).cells ≤ compileBudget size formula.length (Extract.literalCount formula) := by
  have records : rowsCells table.toList ≤ size := by unfold AffineCollect.tableSize at bounded; omega
  have source := rows_cells table.toList size records
  have sourceSize := rows_size table.toList
  have outputs := rows_outputs table.toList
  have count := ConditionalCandidateCost.Code.rows_length table.toList
  have raw := original_cells formula
  have rawSize := original_size formula
  have acceptedSize := amplitude_size (original formula).value
  have acceptedWork : (amplitude (original formula).value).cells ≤ 12*(2*formulaRecords formula+1)+20 := by
    change 12*((original formula).value.code.size+1)+20 ≤ _
    omega
  have mapped := rewrite_cells n (rows table.toList).value.code.size (rows table.toList).value.outputs (amplitude (original formula).value).value.code
  have mappedSize := rewrite_size n (rows table.toList).value.code.size (rows table.toList).value.outputs (amplitude (original formula).value).value.code
  have mapBound : (rewrite n (rows table.toList).value.code.size (rows table.toList).value.outputs (amplitude (original formula).value).value.code).cells ≤
      rewriteBudget (2*formulaRecords formula+1) size := by
    apply mapped.trans
    unfold rewriteBudget
    gcongr <;> omega
  simp only [compile,compileBudget,Array.size_append]
  change (rows table.toList).cells+(original formula).cells+(amplitude (original formula).value).cells+
    (rewrite n (rows table.toList).value.code.size (rows table.toList).value.outputs (amplitude (original formula).value).value.code).cells+
    12*((rows table.toList).value.code.size+(amplitude (original formula).value).value.code.size+
      (rewrite n (rows table.toList).value.code.size (rows table.toList).value.outputs (amplitude (original formula).value).value.code).value.size+
      ((rows table.toList).value.code.size+(rewrite n (rows table.toList).value.code.size (rows table.toList).value.outputs (amplitude (original formula).value).value.code).value.size))+
    2*(AffineCollect.tableSize table+formulaRecords formula+(rows table.toList).value.outputs.length)+20 ≤ _
  unfold formulaRecords CapacityMatching.RowCost.formulaCells at rawSize acceptedWork mapBound ⊢
  omega

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalSourceCost.Initial
