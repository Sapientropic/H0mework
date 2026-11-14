import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.RelationExtractionCostAtoms
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ConditionalPivot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalSchedule.Cost

/-! Paired finite gate construction and source-row lookup. Array map, append,
    push and returned payload copies are charged by their actual code lengths.
    Scalar/address bits and counter evaluation have separate machine costs. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ConditionalCandidateCost.Code
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open CapacityMatching.RowCost (rowCells rowsCells)
abbrev Counted := CapacityMatching.SourceCost.Counted

def binary (conjunction : Bool) (left right : Fragment) : Counted Fragment :=
  ⟨if conjunction then left.and right else left.xor right,
    20*(left.code.size+right.code.size+1)+20⟩

theorem binary_size (conjunction : Bool) (left right : Fragment) :
    (binary conjunction left right).value.code.size=left.code.size+right.code.size+1 := by
  cases conjunction <;> simp [binary,Fragment.and,Fragment.xor,Fragment.binary,Nat.add_assoc]

def negate (source : Fragment) : Counted Fragment :=
  ⟨source.not,12*(source.code.size+1)+10⟩

theorem negate_size (source : Fragment) : (negate source).value.code.size=source.code.size+1 := by
  simp [negate,Fragment.not,Fragment.unary]

def compileTerms : List Nat → Fragment → Counted Fragment
  | [],initial => ⟨initial,2*initial.code.size+4⟩
  | i::rest,initial =>
      let first := binary false initial (Fragment.input i)
      let tail := compileTerms rest first.value
      ⟨tail.value,first.cells+tail.cells+4*(initial.code.size+tail.value.code.size)+8⟩

theorem compileTerms_value (terms : List Nat) (initial : Fragment) :
    (compileTerms terms initial).value=Gates.compileTerms terms initial := by
  induction terms generalizing initial with
  | nil => rfl
  | cons i rest ih => simp only [compileTerms,ih,Gates.compileTerms,binary,Bool.false_eq_true,if_false]

theorem compileTerms_size (terms : List Nat) (initial : Fragment) :
    (compileTerms terms initial).value.code.size=initial.code.size+2*terms.length := by
  rw [compileTerms_value,Gates.compileTerms_size]

theorem compileTerms_cells (terms : List Nat) (initial : Fragment) :
    (compileTerms terms initial).cells ≤
      (terms.length+1)*(40*(initial.code.size+2*terms.length)+60) := by
  induction terms generalizing initial with
  | nil => simp only [compileTerms,List.length_nil]; omega
  | cons i rest ih =>
      have tail := ih (binary false initial (Fragment.input i)).value
      have returned := compileTerms_size rest (binary false initial (Fragment.input i)).value
      have first : (binary false initial (Fragment.input i)).value.code.size=initial.code.size+2 := by
        rw [binary_size]
        rfl
      have billed : (binary false initial (Fragment.input i)).cells=20*(initial.code.size+2)+20 := rfl
      rw [first] at tail returned
      simp only [compileTerms,List.length_cons,billed]
      nlinarith

def compileRow (row : Row) : Counted Fragment :=
  let result := compileTerms row.vars (Fragment.constant (bit row.rhs))
  ⟨result.value,result.cells+3*row.vars.length+9⟩

theorem compileRow_value (row : Row) : (compileRow row).value=Gates.compileRow row := by
  simp only [compileRow,compileTerms_value,Gates.compileRow]

theorem compileRow_size (row : Row) : (compileRow row).value.code.size=1+2*row.vars.length := by
  rw [compileRow_value,Gates.compileRow_size]

def compileBudget (length : Nat) : Nat := (length+1)*(40*(1+2*length)+60)+3*length+9

theorem compileRow_cells (row : Row) : (compileRow row).cells ≤ compileBudget row.vars.length := by
  have source := compileTerms_cells row.vars (Fragment.constant (bit row.rhs))
  change (compileTerms row.vars (Fragment.constant (bit row.rhs))).cells ≤
    (row.vars.length+1)*(40*(1+2*row.vars.length)+60) at source
  simp only [compileRow,compileBudget]
  omega

theorem compileBudget_mono (small large : Nat) (bound : small ≤ large) : compileBudget small ≤ compileBudget large := by
  unfold compileBudget
  gcongr

theorem toggle_work (i : Nat) (terms : List Nat) : Table.toggleVisits i terms ≤ 2*terms.length+4 := by
  have source := pivotMemberVisits_bound i terms
  simp only [Table.toggleVisits]
  split <;> omega

theorem merge_work (left right : List Nat) :
    Table.mergeVisits left right ≤ left.length*(2*(left.length+right.length)+5)+1 := by
  induction left generalizing right with
  | nil => simp [Table.mergeVisits]
  | cons i rest ih =>
      have first := toggle_work i right
      have changed := Parity.toggle_length right i
      have tail := ih (Parity.toggle i right)
      simp only [Table.mergeVisits,List.length_cons]
      nlinarith

def xorRow (left right : Row) : Counted Row :=
  let output := left.xor right
  ⟨output,Table.mergeVisits left.vars right.vars+2*(rowCells left+rowCells right+rowCells output)+6⟩

theorem xorRow_size (left right : Row) : rowCells (xorRow left right).value ≤ rowCells left+rowCells right := by
  have source := Parity.merge_length left.vars right.vars
  simp only [xorRow,Row.xor,rowCells]
  omega

def xorBudget (size : Nat) : Nat := size*(2*size+5)+4*size+20

theorem xorRow_cells (left right : Row) (size : Nat) (bounded : rowCells left+rowCells right ≤ size) :
    (xorRow left right).cells ≤ xorBudget size := by
  have source := merge_work left.vars right.vars
  have returned := xorRow_size left right
  have input : left.vars.length+right.vars.length ≤ size := by unfold rowCells at bounded; omega
  have larger : left.vars.length*(2*(left.vars.length+right.vars.length)+5) ≤ size*(2*size+5) := by gcongr; omega
  simp only [xorRow,xorBudget] at *
  omega

theorem rows_member (rows : List Row) (row : Row) (member : row ∈ rows) : rowCells row ≤ rowsCells rows := by
  induction rows with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [CapacityMatching.RowCost.rowsCells_cons]; omega
      · have source := ih member; simp only [CapacityMatching.RowCost.rowsCells_cons]; omega

theorem rows_length (rows : List Row) : rows.length ≤ rowsCells rows := by
  induction rows with
  | nil => simp
  | cons row rest ih => simp only [List.length_cons,CapacityMatching.RowCost.rowsCells_cons]; unfold rowCells; omega

def optionSize : Option Row → Nat
  | none => 1
  | some row => rowCells row+1

def findRow (address : Nat) : List Row → Counted (Option Row)
  | [] => ⟨none,1⟩
  | row::rest =>
      let found := AffineClauseProduct.Cost.member address row.vars
      if found.value then ⟨some row,found.visits+2*rowCells row+5⟩ else
        let tail := findRow address rest
        ⟨tail.value,found.visits+tail.cells+2*optionSize tail.value+5⟩

theorem findRow_value (address : Nat) (rows : List Row) :
    (findRow address rows).value=rows.find? (fun row => decide (address ∈ row.vars)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [findRow,List.find?_cons,AffineClauseProduct.Cost.member_value]
      split <;> simp_all

theorem findRow_size (address : Nat) (rows : List Row) :
    optionSize (findRow address rows).value ≤ rowsCells rows+1 := by
  rw [findRow_value]
  cases found : rows.find? (fun row => decide (address ∈ row.vars)) with
  | none => simp [optionSize]
  | some row =>
      have bound := rows_member rows row (List.mem_of_find?_eq_some found)
      simp only [optionSize]; omega

theorem findRow_cells_aux (address : Nat) (rows : List Row) (size : Nat) (bounded : rowsCells rows ≤ size) :
    (findRow address rows).cells ≤ rows.length*(4*size+8)+1 := by
  induction rows with
  | nil => simp [findRow]
  | cons row rest ih =>
      have total : rowCells row+rowsCells rest ≤ size := by simpa only [CapacityMatching.RowCost.rowsCells_cons] using bounded
      have tail := ih (by omega)
      have found := AffineClauseProduct.Cost.member_visits address row.vars
      have returned := findRow_size address rest
      have measured : rowCells row=row.vars.length+2 := rfl
      simp only [findRow,List.length_cons]
      split <;> simp only <;> nlinarith

def findBudget (size : Nat) : Nat := size*(4*size+8)+1

theorem findRow_cells (address : Nat) (rows : List Row) (size : Nat) (bounded : rowsCells rows ≤ size) :
    (findRow address rows).cells ≤ findBudget size := by
  have scanned := findRow_cells_aux address rows size bounded
  have count := rows_length rows
  unfold findBudget
  nlinarith

def expression (rows : List Row) (address : Nat) : Counted Row :=
  let found := findRow address rows
  match found.value with
  | none => ⟨⟨[address],false⟩,found.cells+11⟩
  | some row =>
      let result := xorRow row ⟨[address],false⟩
      ⟨result.value,found.cells+result.cells+2*rowCells result.value+5⟩

theorem expression_value (rows : List Row) (address : Nat) :
    (expression rows address).value=ConditionalPivot.expression rows address := by
  simp only [expression,findRow_value,ConditionalPivot.expression]
  cases found : rows.find? (fun row => decide (address ∈ row.vars)) <;> rfl

theorem expression_size (rows : List Row) (address : Nat) :
    rowCells (expression rows address).value ≤ rowsCells rows+3 := by
  simp only [expression]
  split
  · simp [rowCells]
  · rename_i row found
    have member := List.mem_of_find?_eq_some ((findRow_value address rows).symm.trans found)
    have source := rows_member rows row member
    have bound := xorRow_size row ⟨[address],false⟩
    have single : rowCells (Row.mk [address] false)=3 := rfl
    rw [single] at bound
    simp only
    omega

def expressionBudget (size : Nat) : Nat := findBudget size+xorBudget (size+3)+2*size+11

theorem expression_cells (rows : List Row) (address size : Nat) (bounded : rowsCells rows ≤ size) :
    (expression rows address).cells ≤ expressionBudget size := by
  have scanned := findRow_cells address rows size bounded
  simp only [expression]
  split
  · simp only; unfold expressionBudget; omega
  · rename_i row found
    have member := List.mem_of_find?_eq_some ((findRow_value address rows).symm.trans found)
    have source := rows_member rows row member
    have output := xorRow_size row ⟨[address],false⟩
    have single : rowCells (Row.mk [address] false)=3 := rfl
    have billed := xorRow_cells row ⟨[address],false⟩ (size+3) (by rw [single]; omega)
    rw [single] at output
    simp only
    unfold expressionBudget
    omega

def tableRead (table : Array Row) (address : Nat) : Counted Row :=
  let result := AffineClauses.Cost.lookup table.toList address
  ⟨result.value,result.cells+2*AffineCollect.tableSize table+2*table.size+4⟩

theorem tableRead_value (table : Array Row) (address : Nat) :
    (tableRead table address).value=table.getD address Gates.zeroRow := by
  simp [tableRead,AffineClauses.Cost.lookup_value,Array.getD_eq_getD_getElem?]

theorem tableRead_size (table : Array Row) (address : Nat) :
    rowCells (tableRead table address).value ≤ AffineCollect.tableSize table+2 := by
  rw [tableRead_value]
  by_cases inside : address < table.size
  · have source := rows_member table.toList table[address] (Array.getElem_mem_toList inside)
    have capped : rowCells table[address] ≤ AffineCollect.tableSize table+2 := by
      unfold AffineCollect.tableSize
      omega
    simpa [Array.getD,inside] using capped
  · simp [Array.getD,inside,Gates.zeroRow,rowCells]

theorem tableRead_cells (table : Array Row) (address : Nat) :
    (tableRead table address).cells ≤ 9*AffineCollect.tableSize table+10 := by
  have source := AffineClauses.Cost.lookup_cells table.toList address
  have count := rows_length table.toList
  simp only [Array.length_toList] at count source
  simp only [tableRead,AffineCollect.tableSize]
  omega

def signed (positive : Bool) (source : Fragment) : Counted Fragment :=
  if positive then ⟨source,2*source.code.size+4⟩ else negate source

theorem signed_size (positive : Bool) (source : Fragment) :
    (signed positive source).value.code.size ≤ source.code.size+1 := by
  cases positive <;> simp [signed,negate_size]

theorem signed_cells (positive : Bool) (source : Fragment) :
    (signed positive source).cells ≤ 14*(source.code.size+1)+14 := by
  cases positive <;> simp only [signed,Bool.false_eq_true,if_false,if_true,negate] <;> omega

def mux (selector left right : Fragment) : Counted Fragment :=
  let opposite := negate selector
  let a := binary true opposite.value left
  let b := binary true selector right
  let result := binary false a.value b.value
  ⟨result.value,opposite.cells+a.cells+b.cells+result.cells+
    4*(selector.code.size+left.code.size+right.code.size+result.value.code.size)+10⟩

theorem mux_value (selector left right : Fragment) :
    (mux selector left right).value=ConditionalPivot.mux selector left right := rfl

theorem mux_size (selector left right : Fragment) :
    (mux selector left right).value.code.size=2*selector.code.size+left.code.size+right.code.size+4 := by
  simp only [mux,binary_size,negate_size]
  omega

theorem mux_cells (selector left right : Fragment) (size : Nat)
    (a : selector.code.size ≤ size) (b : left.code.size ≤ size) (c : right.code.size ≤ size) :
    (mux selector left right).cells ≤ 300*(size+3) := by
  simp only [mux,binary,negate]
  simp only [Bool.false_eq_true,if_true,if_false,
    Fragment.and,Fragment.xor,Fragment.not,Fragment.binary,Fragment.unary,
    Array.size_push,Array.size_append,Array.size_map]
  omega

def conditionalBody (coordinates : Array Row) (i j : Nat) (left right : List Row) : Counted Fragment :=
  let selector := tableRead coordinates i
  let a := compileRow selector.value
  let first := expression left j
  let b := compileRow first.value
  let second := expression right j
  let c := compileRow second.value
  let output := mux a.value b.value c.value
  ⟨output.value,selector.cells+a.cells+first.cells+b.cells+second.cells+c.cells+output.cells+
    2*(rowCells selector.value+rowCells first.value+rowCells second.value+output.value.code.size)+12⟩

theorem conditionalBody_value (coordinates : Array Row) (i j : Nat) (left right : List Row) :
    (conditionalBody coordinates i j left right).value=ConditionalPivot.body coordinates i j left right := by
  simp only [conditionalBody,mux_value,compileRow_value,tableRead_value,expression_value,ConditionalPivot.body]

def conditionalBudget (size : Nat) : Nat :=
  2*expressionBudget size+3*compileBudget (size+3)+1000*(size+5)

theorem conditionalBody_size (coordinates : Array Row) (i j : Nat) (left right : List Row) (size : Nat)
    (tableBound : AffineCollect.tableSize coordinates ≤ size)
    (leftBound : rowsCells left ≤ size) (rightBound : rowsCells right ≤ size) :
    (conditionalBody coordinates i j left right).value.code.size ≤ 12+8*size := by
  have a := tableRead_size coordinates i
  have b := expression_size left j
  have c := expression_size right j
  have asize := compileRow_size (tableRead coordinates i).value
  have bsize := compileRow_size (expression left j).value
  have csize := compileRow_size (expression right j).value
  have final := mux_size (compileRow (tableRead coordinates i).value).value
    (compileRow (expression left j).value).value (compileRow (expression right j).value).value
  simp only [conditionalBody]
  unfold rowCells at a b c
  omega

theorem conditionalBody_cells (coordinates : Array Row) (i j : Nat) (left right : List Row) (size : Nat)
    (tableBound : AffineCollect.tableSize coordinates ≤ size)
    (leftBound : rowsCells left ≤ size) (rightBound : rowsCells right ≤ size) :
    (conditionalBody coordinates i j left right).cells ≤ conditionalBudget size := by
  have readWork := tableRead_cells coordinates i
  have readSize := tableRead_size coordinates i
  have leftWork := expression_cells left j size leftBound
  have leftSize := expression_size left j
  have rightWork := expression_cells right j size rightBound
  have rightSize := expression_size right j
  have ar : (tableRead coordinates i).value.vars.length ≤ size+3 := by unfold rowCells at readSize; omega
  have br : (expression left j).value.vars.length ≤ size+3 := by unfold rowCells at leftSize; omega
  have cr : (expression right j).value.vars.length ≤ size+3 := by unfold rowCells at rightSize; omega
  have a := (compileRow_cells (tableRead coordinates i).value).trans (compileBudget_mono _ _ ar)
  have b := (compileRow_cells (expression left j).value).trans (compileBudget_mono _ _ br)
  have c := (compileRow_cells (expression right j).value).trans (compileBudget_mono _ _ cr)
  have asize := compileRow_size (tableRead coordinates i).value
  have bsize := compileRow_size (expression left j).value
  have csize := compileRow_size (expression right j).value
  have mixed := mux_cells (compileRow (tableRead coordinates i).value).value
    (compileRow (expression left j).value).value (compileRow (expression right j).value).value
    (2*size+7) (by omega) (by omega) (by omega)
  have final := mux_size (compileRow (tableRead coordinates i).value).value
    (compileRow (expression left j).value).value (compileRow (expression right j).value).value
  simp only [conditionalBody,conditionalBudget]
  omega

def literalBody {n : Nat} (coordinates : Array Row) (literal : CNFLiteral n) : Counted Fragment :=
  let source := tableRead coordinates literal.var.val
  let compiled := compileRow source.value
  let output := signed literal.positive compiled.value
  ⟨output.value,source.cells+compiled.cells+output.cells+2*output.value.code.size+8⟩

theorem literalBody_value {n : Nat} (coordinates : Array Row) (literal : CNFLiteral n) :
    (literalBody coordinates literal).value=FunctionalAffine.literalBody coordinates literal := by
  simp only [literalBody,signed,compileRow_value,tableRead_value,FunctionalAffine.literalBody]
  split <;> rfl

def literalBudget (size : Nat) : Nat := compileBudget size+100*(size+2)

theorem literalBody_size {n : Nat} (coordinates : Array Row) (literal : CNFLiteral n) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    (literalBody coordinates literal).value.code.size ≤ 2+2*size := by
  have source := tableRead_size coordinates literal.var.val
  have first := compileRow_size (tableRead coordinates literal.var.val).value
  have last := signed_size literal.positive (compileRow (tableRead coordinates literal.var.val).value).value
  simp only [literalBody]
  unfold rowCells at source
  omega

theorem literalBody_cells {n : Nat} (coordinates : Array Row) (literal : CNFLiteral n) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    (literalBody coordinates literal).cells ≤ literalBudget size := by
  have source := tableRead_size coordinates literal.var.val
  have readWork := tableRead_cells coordinates literal.var.val
  have terms : (tableRead coordinates literal.var.val).value.vars.length ≤ size := by unfold rowCells at source; omega
  have compiled := (compileRow_cells (tableRead coordinates literal.var.val).value).trans (compileBudget_mono _ _ terms)
  have first := compileRow_size (tableRead coordinates literal.var.val).value
  have billed := signed_cells literal.positive (compileRow (tableRead coordinates literal.var.val).value).value
  have stored := signed_size literal.positive (compileRow (tableRead coordinates literal.var.val).value).value
  simp only [literalBody,literalBudget]
  omega

def relationBody {n : Nat} (coordinates : Array Row) (relation : FunctionalRelations.Relation n) : Counted Fragment :=
  let left := literalBody coordinates relation.left
  let right := literalBody coordinates relation.right
  let both := binary true left.value right.value
  let output := signed relation.output.positive both.value
  ⟨output.value,left.cells+right.cells+both.cells+output.cells+2*output.value.code.size+8⟩

theorem relationBody_value {n : Nat} (coordinates : Array Row) (relation : FunctionalRelations.Relation n) :
    (relationBody coordinates relation).value=FunctionalAffine.body coordinates relation := by
  simp only [relationBody,literalBody_value,signed,binary,FunctionalAffine.body,negate]
  split <;> rfl

theorem relationBody_size {n : Nat} (coordinates : Array Row) (relation : FunctionalRelations.Relation n) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    (relationBody coordinates relation).value.code.size ≤ 6+4*size := by
  have left := literalBody_size coordinates relation.left size bounded
  have right := literalBody_size coordinates relation.right size bounded
  have combined := binary_size true (literalBody coordinates relation.left).value (literalBody coordinates relation.right).value
  have output := signed_size relation.output.positive
    (binary true (literalBody coordinates relation.left).value (literalBody coordinates relation.right).value).value
  simp only [relationBody]
  omega

def relationBudget (size : Nat) : Nat := 2*literalBudget size+300*(size+3)

theorem relationBody_cells {n : Nat} (coordinates : Array Row) (relation : FunctionalRelations.Relation n) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    (relationBody coordinates relation).cells ≤ relationBudget size := by
  have left := literalBody_size coordinates relation.left size bounded
  have right := literalBody_size coordinates relation.right size bounded
  have leftWork := literalBody_cells coordinates relation.left size bounded
  have rightWork := literalBody_cells coordinates relation.right size bounded
  have combined := binary_size true (literalBody coordinates relation.left).value (literalBody coordinates relation.right).value
  have output := signed_size relation.output.positive
    (binary true (literalBody coordinates relation.left).value (literalBody coordinates relation.right).value).value
  have signedWork := signed_cells relation.output.positive
    (binary true (literalBody coordinates relation.left).value (literalBody coordinates relation.right).value).value
  simp only [relationBody,relationBudget]
  change (literalBody coordinates relation.left).cells+(literalBody coordinates relation.right).cells+
    (20*((literalBody coordinates relation.left).value.code.size+(literalBody coordinates relation.right).value.code.size+1)+20)+
    (signed relation.output.positive (binary true (literalBody coordinates relation.left).value (literalBody coordinates relation.right).value).value).cells+
    2*(signed relation.output.positive (binary true (literalBody coordinates relation.left).value (literalBody coordinates relation.right).value).value).value.code.size+8 ≤ _
  omega

def functionalBody {n : Nat} (coordinates : Array Row) (relation : FunctionalRelations.Relation n) (address : Nat) : Counted Fragment :=
  let source := tableRead coordinates relation.output.var.val
  let residual := xorRow source.value ⟨[address],false⟩
  let affine := compileRow residual.value
  let functional := relationBody coordinates relation
  let result := binary false affine.value functional.value
  ⟨result.value,source.cells+residual.cells+affine.cells+functional.cells+result.cells+2*result.value.code.size+10⟩

theorem functionalBody_value {n : Nat} (coordinates : Array Row) (relation : FunctionalRelations.Relation n) (address : Nat) :
    (functionalBody coordinates relation address).value=FunctionalPivot.body coordinates relation address := by
  simp only [functionalBody,binary,compileRow_value,relationBody_value,xorRow,tableRead_value,
    FunctionalPivot.body,FunctionalPivot.residual,Bool.false_eq_true,if_false]

def functionalBudget (size : Nat) : Nat := xorBudget (size+5)+compileBudget (size+3)+relationBudget size+500*(size+5)

theorem functionalBody_size {n : Nat} (coordinates : Array Row) (relation : FunctionalRelations.Relation n) (address size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    (functionalBody coordinates relation address).value.code.size ≤ 14+6*size := by
  have source := tableRead_size coordinates relation.output.var.val
  have residual := xorRow_size (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩
  have single : rowCells (Row.mk [address] false)=3 := rfl
  rw [single] at residual
  have left := compileRow_size (xorRow (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩).value
  have right := relationBody_size coordinates relation size bounded
  simp only [functionalBody,binary_size]
  unfold rowCells at source residual
  omega

theorem functionalBody_cells {n : Nat} (coordinates : Array Row) (relation : FunctionalRelations.Relation n) (address size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    (functionalBody coordinates relation address).cells ≤ functionalBudget size := by
  have source := tableRead_size coordinates relation.output.var.val
  have readWork := tableRead_cells coordinates relation.output.var.val
  have residual := xorRow_size (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩
  have single : rowCells (Row.mk [address] false)=3 := rfl
  rw [single] at residual
  have xorWork := xorRow_cells (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩ (size+5) (by rw [single]; omega)
  have terms : (xorRow (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩).value.vars.length ≤ size+3 := by
    unfold rowCells at residual source; omega
  have leftWork := (compileRow_cells (xorRow (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩).value).trans
    (compileBudget_mono _ _ terms)
  have left := compileRow_size (xorRow (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩).value
  have right := relationBody_size coordinates relation size bounded
  have rightWork := relationBody_cells coordinates relation size bounded
  simp only [functionalBody,functionalBudget,binary_size]
  change (tableRead coordinates relation.output.var.val).cells+
    (xorRow (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩).cells+
    (compileRow (xorRow (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩).value).cells+
    (relationBody coordinates relation).cells+
    (20*((compileRow (xorRow (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩).value).value.code.size+
      (relationBody coordinates relation).value.code.size+1)+20)+
    2*((compileRow (xorRow (tableRead coordinates relation.output.var.val).value ⟨[address],false⟩).value).value.code.size+
      (relationBody coordinates relation).value.code.size+1)+10 ≤ _
  omega

end SaturationMonoid.ComplexityProjection.SATSource.ConditionalCandidateCost.Code
