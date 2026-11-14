import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.AtomFeedbackCostBranch

/-! Paired source-list operations for the original normalization and relation
    scans. Literal addresses count as source records; their bit implementations
    and counter arithmetic remain a separate machine ledger. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineRelationExtractionCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
abbrev Counted := CapacityMatching.SourceCost.Counted
abbrev size := @CapacityMatching.RowCost.formulaCells

theorem size_positive {n : Nat} (formula : CNFFormula n) : 1 ≤ size formula := by unfold size CapacityMatching.RowCost.formulaCells; omega

theorem size_measures {n : Nat} (formula : CNFFormula n) :
    formula.length ≤ size formula ∧ Extract.literalCount formula ≤ size formula := by
  unfold size CapacityMatching.RowCost.formulaCells
  omega

theorem size_cons {n : Nat} (clause : CNFClause n) (rest : CNFFormula n) :
    size (clause::rest)=3*clause.length+size rest+2 := by
  simp only [size,CapacityMatching.RowCost.formulaCells,Extract.literalCount,List.map_cons,List.sum_cons,List.length_cons]
  omega

theorem size_sublist {n : Nat} {left right : CNFFormula n} (part : left.Sublist right) : size left ≤ size right := by
  have literals : Extract.literalCount left ≤ Extract.literalCount right := Subsumption.literalCount_sublist part
  have length := part.length_le
  unfold size CapacityMatching.RowCost.formulaCells
  omega

theorem clause_length_le_size {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) (member : clause ∈ formula) :
    clause.length ≤ size formula := by
  have length : clause.length ≤ Extract.literalCount formula := List.le_sum_of_mem (List.mem_map.mpr ⟨clause,member,rfl⟩)
  exact length.trans (size_measures formula).2

def literalEqual {n : Nat} (left right : CNFLiteral n) : Counted Bool :=
  if left.var==right.var then ⟨left.positive==right.positive,3⟩ else ⟨false,2⟩

theorem literalEqual_value {n : Nat} (left right : CNFLiteral n) :
    (literalEqual left right).value=decide (left=right) := by
  cases left with
  | mk i a =>
      cases right with
      | mk j b =>
          by_cases same : i=j
          · subst j
            cases a <;> cases b <;> simp [literalEqual]
          · simp [literalEqual,same]

theorem literalEqual_cells {n : Nat} (left right : CNFLiteral n) : (literalEqual left right).cells ≤ 3 := by
  simp only [literalEqual]
  split <;> simp

def clauseEqual {n : Nat} : CNFClause n → CNFClause n → Counted Bool
  | [],[] => ⟨true,1⟩
  | [],_::_ => ⟨false,1⟩
  | _::_,[] => ⟨false,1⟩
  | a::left,b::right =>
      let tested := literalEqual a b
      if tested.value then let tail := clauseEqual left right; ⟨tail.value,tested.cells+tail.cells+1⟩
      else ⟨false,tested.cells+1⟩

theorem clauseEqual_value {n : Nat} (left right : CNFClause n) :
    (clauseEqual left right).value=decide (left=right) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a left ih =>
      cases right with
      | nil => rfl
      | cons b right => simp only [clauseEqual,literalEqual_value]; split <;> simp_all

theorem clauseEqual_cells {n : Nat} (left right : CNFClause n) :
    (clauseEqual left right).cells ≤ 4*left.length+1 := by
  induction left generalizing right with
  | nil => cases right <;> simp [clauseEqual]
  | cons a left ih =>
      cases right with
      | nil => simp [clauseEqual]
      | cons b right =>
          have first := literalEqual_cells a b
          have tail := ih right
          simp only [clauseEqual,List.length_cons]
          split <;> simp only <;> omega

def literalErase {n : Nat} (literal : CNFLiteral n) : CNFClause n → Counted (CNFClause n)
  | [] => ⟨[],1⟩
  | head::rest =>
      let tested := literalEqual head literal
      if tested.value then ⟨rest,tested.cells+6*rest.length+3⟩
      else let tail := literalErase literal rest
           ⟨head::tail.value,tested.cells+tail.cells+6*tail.value.length+6⟩

theorem literalErase_value {n : Nat} (literal : CNFLiteral n) (clause : CNFClause n) :
    (literalErase literal clause).value=clause.erase literal := by
  induction clause with
  | nil => rfl
  | cons head rest ih => simp only [literalErase,literalEqual_value]; split <;> simp_all

theorem literalErase_length {n : Nat} (literal : CNFLiteral n) (clause : CNFClause n) :
    (literalErase literal clause).value.length ≤ clause.length := by rw [literalErase_value]; exact List.length_erase_le

def eraseBudget (length : Nat) : Nat := length*(6*length+10)+1

theorem literalErase_cells {n : Nat} (literal : CNFLiteral n) (clause : CNFClause n) :
    (literalErase literal clause).cells ≤ eraseBudget clause.length := by
  induction clause with
  | nil => simp [literalErase,eraseBudget]
  | cons head rest ih =>
      have first := literalEqual_cells head literal
      have length := literalErase_length literal rest
      simp only [literalErase,List.length_cons]
      split <;> simp only <;> unfold eraseBudget at * <;> nlinarith

def clauseMember {n : Nat} (clause : CNFClause n) : CNFFormula n → Counted Bool
  | [] => ⟨false,1⟩
  | head::rest =>
      let tested := clauseEqual clause head
      if tested.value then ⟨true,tested.cells+2⟩
      else let tail := clauseMember clause rest; ⟨tail.value,tested.cells+tail.cells+2⟩

theorem clauseMember_value {n : Nat} (clause : CNFClause n) (formula : CNFFormula n) :
    (clauseMember clause formula).value=decide (clause ∈ formula) := by
  induction formula with
  | nil => rfl
  | cons head rest ih => simp only [clauseMember,clauseEqual_value]; split <;> simp_all

theorem clauseMember_cells {n : Nat} (clause : CNFClause n) (formula : CNFFormula n) :
    (clauseMember clause formula).cells ≤ formula.length*(4*clause.length+3)+1 := by
  induction formula with
  | nil => simp [clauseMember]
  | cons head rest ih =>
      have first := clauseEqual_cells clause head
      simp only [clauseMember,List.length_cons]
      split <;> simp only <;> nlinarith

def formulaErase {n : Nat} (clause : CNFClause n) : CNFFormula n → Counted (CNFFormula n)
  | [] => ⟨[],1⟩
  | head::rest =>
      let tested := clauseEqual head clause
      if tested.value then ⟨rest,tested.cells+2*size rest+3⟩
      else let tail := formulaErase clause rest
           ⟨head::tail.value,tested.cells+tail.cells+2*size tail.value+6*head.length+7⟩

theorem formulaErase_value {n : Nat} (clause : CNFClause n) (formula : CNFFormula n) :
    (formulaErase clause formula).value=formula.erase clause := by
  induction formula with
  | nil => rfl
  | cons head rest ih => simp only [formulaErase,clauseEqual_value]; split <;> simp_all

theorem formulaErase_size {n : Nat} (clause : CNFClause n) (formula : CNFFormula n) :
    size (formulaErase clause formula).value ≤ size formula := by
  rw [formulaErase_value]
  exact size_sublist List.erase_sublist

theorem formulaErase_cells {n : Nat} (clause : CNFClause n) (formula : CNFFormula n)
    (limit : Nat) (bounded : size formula ≤ limit) :
    (formulaErase clause formula).cells ≤ formula.length*(12*limit+8)+1 := by
  induction formula with
  | nil => simp [formulaErase]
  | cons head rest ih =>
      have headLength : head.length ≤ limit := (clause_length_le_size (head::rest) head (by simp)).trans bounded
      have restSize : size rest ≤ limit := by rw [size_cons] at bounded; omega
      have first := clauseEqual_cells head clause
      have tail := ih restSize
      have stored := (formulaErase_size clause rest).trans restSize
      simp only [formulaErase,List.length_cons]
      split <;> simp only <;> nlinarith

def uniqueLiterals {n : Nat} : CNFClause n → Counted (CNFClause n)
  | [] => ⟨[],1⟩
  | literal::rest =>
      let tail := uniqueLiterals rest
      let found := Extract.member literal tail.value
      ⟨if found.accepted then tail.value else literal::tail.value,
        tail.cells+found.visits+6*tail.value.length+6⟩

theorem uniqueLiterals_value {n : Nat} (clause : CNFClause n) : (uniqueLiterals clause).value=clause.dedup := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      simp only [uniqueLiterals,ih,List.dedup_cons']
      by_cases member : literal ∈ rest.dedup
      · have yes := (Extract.member_accepted literal rest.dedup).mpr member
        simp [member,yes]
      · have no : (Extract.member literal rest.dedup).accepted=false :=
          Bool.eq_false_iff.mpr (fun hit => member ((Extract.member_accepted _ _).mp hit))
        simp [member,no]

theorem uniqueLiterals_length {n : Nat} (clause : CNFClause n) : (uniqueLiterals clause).value.length ≤ clause.length := by
  rw [uniqueLiterals_value]
  exact (List.dedup_sublist clause).length_le

def literalsBudget (count : Nat) : Nat := count*(8*count+7)+1

theorem uniqueLiterals_cells {n : Nat} (clause : CNFClause n) :
    (uniqueLiterals clause).cells ≤ literalsBudget clause.length := by
  induction clause with
  | nil => simp [uniqueLiterals,literalsBudget]
  | cons literal rest ih =>
      have found := Extract.member_visits literal (uniqueLiterals rest).value
      have length := uniqueLiterals_length rest
      simp only [uniqueLiterals,List.length_cons]
      unfold literalsBudget at *
      nlinarith

def uniqueFormula {n : Nat} : CNFFormula n → Counted (CNFFormula n)
  | [] => ⟨[],1⟩
  | clause::rest =>
      let tail := uniqueFormula rest
      let found := clauseMember clause tail.value
      ⟨if found.value then tail.value else clause::tail.value,
        tail.cells+found.cells+2*size tail.value+6*clause.length+7⟩

theorem uniqueFormula_value {n : Nat} (formula : CNFFormula n) : (uniqueFormula formula).value=formula.dedup := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp only [uniqueFormula,clauseMember_value,ih,List.dedup_cons']; split <;> simp_all

theorem uniqueFormula_size {n : Nat} (formula : CNFFormula n) : size (uniqueFormula formula).value ≤ size formula := by
  rw [uniqueFormula_value]
  exact size_sublist (List.dedup_sublist formula)

def formulaBudget (limit : Nat) : Nat := limit*(limit*(4*limit+3)+8*limit+8)+1

theorem uniqueFormula_cells_aux {n : Nat} (formula : CNFFormula n) (limit : Nat) (bounded : size formula ≤ limit) :
    (uniqueFormula formula).cells ≤ formula.length*(limit*(4*limit+3)+8*limit+8)+1 := by
  induction formula with
  | nil => simp [uniqueFormula]
  | cons clause rest ih =>
      have length : clause.length ≤ limit := (clause_length_le_size _ _ (by simp)).trans bounded
      have restSize : size rest ≤ limit := by rw [size_cons] at bounded; omega
      have tail := ih restSize
      have stored := (uniqueFormula_size rest).trans restSize
      have outputLength := (size_measures (uniqueFormula rest).value).1.trans stored
      have found := clauseMember_cells clause (uniqueFormula rest).value
      have foundCost : (clauseMember clause (uniqueFormula rest).value).cells ≤ limit*(4*limit+3)+1 := by
        apply found.trans; gcongr
      simp only [uniqueFormula,List.length_cons]
      nlinarith

theorem uniqueFormula_cells {n : Nat} (formula : CNFFormula n) :
    (uniqueFormula formula).cells ≤ formulaBudget (size formula) := by
  apply (uniqueFormula_cells_aux formula (size formula) (Nat.le_refl _)).trans
  unfold formulaBudget
  gcongr
  exact (size_measures formula).1

def complementScan {n : Nat} (source : CNFClause n) : CNFClause n → Counted Bool
  | [] => ⟨false,1⟩
  | literal::rest =>
      let found := Extract.member (Alias.negate literal) source
      if found.accepted then ⟨true,found.visits+5⟩
      else let tail := complementScan source rest; ⟨tail.value,found.visits+tail.cells+5⟩

theorem complementScan_value {n : Nat} (source anchors : CNFClause n) :
    (complementScan source anchors).value=true ↔ ∃ literal ∈ anchors, Alias.negate literal ∈ source := by
  induction anchors with
  | nil => simp [complementScan]
  | cons literal rest ih =>
      simp only [complementScan]
      split
      · rename_i found
        have member := (Extract.member_accepted _ _).mp found
        simp [member]
      · rename_i absent
        have missing : Alias.negate literal ∉ source := fun member => absent ((Extract.member_accepted _ _).mpr member)
        simpa [missing] using ih

theorem complementScan_cells {n : Nat} (source anchors : CNFClause n) :
    (complementScan source anchors).cells ≤ anchors.length*(2*source.length+6)+1 := by
  induction anchors with
  | nil => simp [complementScan]
  | cons literal rest ih =>
      have found := Extract.member_visits (Alias.negate literal) source
      simp only [complementScan,List.length_cons]
      split <;> simp only <;> nlinarith

theorem tautology_iff_pair {n : Nat} (clause : CNFClause n) :
    SATJoint.tautologyClause clause=true ↔ ∃ literal ∈ clause, Alias.negate literal ∈ clause := by
  rw [SATJoint.tautologyClause_eq_empty,SATJoint.emptyCube_true_iff_coordinate]
  constructor
  · rintro ⟨i,empty⟩
    have first : (false : Bool) ∉ SATJoint.clauseCube clause i := by rw [empty]; simp
    have second : (true : Bool) ∉ SATJoint.clauseCube clause i := by rw [empty]; simp
    simp only [SATJoint.clauseCube,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_not] at first second
    obtain ⟨a,memberA,atA,valueA⟩ := first
    obtain ⟨b,memberB,atB,valueB⟩ := second
    have same : Alias.negate a=b := by
      cases a
      cases b
      simp_all [Alias.negate]
    exact ⟨a,memberA,same.symm ▸ memberB⟩
  · rintro ⟨literal,member,opposite⟩
    refine ⟨literal.var,Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro value allowed
    have first := (Finset.mem_filter.mp allowed).2 literal member rfl
    have second := (Finset.mem_filter.mp allowed).2 (Alias.negate literal) opposite rfl
    cases value <;> cases polarity : literal.positive <;> simp_all [Alias.negate]

def tautology {n : Nat} (clause : CNFClause n) : Counted Bool := complementScan clause clause

theorem tautology_value {n : Nat} (clause : CNFClause n) : (tautology clause).value=SATJoint.tautologyClause clause := by
  apply Bool.eq_iff_iff.mpr
  exact (complementScan_value clause clause).trans (tautology_iff_pair clause).symm

theorem tautology_cells {n : Nat} (clause : CNFClause n) :
    (tautology clause).cells ≤ clause.length*(2*clause.length+6)+1 := complementScan_cells clause clause

def filterTautologies {n : Nat} : CNFFormula n → Counted (CNFFormula n)
  | [] => ⟨[],1⟩
  | clause::rest =>
      let checked := tautology clause
      let tail := filterTautologies rest
      ⟨if checked.value then tail.value else clause::tail.value,
        checked.cells+tail.cells+2*size tail.value+6*clause.length+8⟩

theorem filterTautologies_value {n : Nat} (formula : CNFFormula n) :
    (filterTautologies formula).value=SATJoint.dropTautologies formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [filterTautologies,tautology_value,ih,SATJoint.dropTautologies,List.filter_cons]
      cases SATJoint.tautologyClause clause <;> rfl

theorem filterTautologies_size {n : Nat} (formula : CNFFormula n) : size (filterTautologies formula).value ≤ size formula := by
  rw [filterTautologies_value]
  exact size_sublist List.filter_sublist

def filterBudget (limit : Nat) : Nat := limit*(limit*(2*limit+6)+8*limit+9)+1

theorem filterTautologies_cells_aux {n : Nat} (formula : CNFFormula n) (limit : Nat) (bounded : size formula ≤ limit) :
    (filterTautologies formula).cells ≤ formula.length*(limit*(2*limit+6)+8*limit+9)+1 := by
  induction formula with
  | nil => simp [filterTautologies]
  | cons clause rest ih =>
      have length := (clause_length_le_size (clause::rest) clause (by simp)).trans bounded
      have restSize : size rest ≤ limit := by rw [size_cons] at bounded; omega
      have first := tautology_cells clause
      have firstCost : (tautology clause).cells ≤ limit*(2*limit+6)+1 := by apply first.trans; gcongr
      have tail := ih restSize
      have stored := (filterTautologies_size rest).trans restSize
      simp only [filterTautologies,List.length_cons]
      nlinarith

theorem filterTautologies_cells {n : Nat} (formula : CNFFormula n) :
    (filterTautologies formula).cells ≤ filterBudget (size formula) := by
  apply (filterTautologies_cells_aux formula (size formula) (Nat.le_refl _)).trans
  unfold filterBudget
  gcongr
  exact (size_measures formula).1

def normalizeClauses {n : Nat} : CNFFormula n → Counted (CNFFormula n)
  | [] => ⟨[],1⟩
  | clause::rest =>
      let first := uniqueLiterals clause
      let tail := normalizeClauses rest
      ⟨first.value::tail.value,first.cells+tail.cells+2*size tail.value+6*first.value.length+6⟩

theorem normalizeClauses_value {n : Nat} (formula : CNFFormula n) :
    (normalizeClauses formula).value=formula.map List.dedup := by
  induction formula <;> simp_all [normalizeClauses,uniqueLiterals_value]

theorem normalizeClauses_size {n : Nat} (formula : CNFFormula n) : size (normalizeClauses formula).value ≤ size formula := by
  have literals : Extract.literalCount (formula.map List.dedup) ≤ Extract.literalCount formula :=
    Subsumption.literalCount_map_dedup_le formula
  simp only [normalizeClauses_value,size,CapacityMatching.RowCost.formulaCells,List.length_map]
  omega

def clausesBudget (limit : Nat) : Nat := limit*(literalsBudget limit+8*limit+6)+1

theorem normalizeClauses_cells_aux {n : Nat} (formula : CNFFormula n) (limit : Nat) (bounded : size formula ≤ limit) :
    (normalizeClauses formula).cells ≤ formula.length*(literalsBudget limit+8*limit+6)+1 := by
  induction formula with
  | nil => simp [normalizeClauses]
  | cons clause rest ih =>
      have length := (clause_length_le_size (clause::rest) clause (by simp)).trans bounded
      have restSize : size rest ≤ limit := by rw [size_cons] at bounded; omega
      have first := uniqueLiterals_cells clause
      have firstCost : (uniqueLiterals clause).cells ≤ literalsBudget limit := by
        apply first.trans; unfold literalsBudget; gcongr
      have tail := ih restSize
      have stored := (normalizeClauses_size rest).trans restSize
      have normalizedLength := (uniqueLiterals_length clause).trans length
      simp only [normalizeClauses,List.length_cons]
      nlinarith

theorem normalizeClauses_cells {n : Nat} (formula : CNFFormula n) :
    (normalizeClauses formula).cells ≤ clausesBudget (size formula) := by
  apply (normalizeClauses_cells_aux formula (size formula) (Nat.le_refl _)).trans
  unfold clausesBudget
  gcongr
  exact (size_measures formula).1

def normalize {n : Nat} (formula : CNFFormula n) : Counted (CNFFormula n) :=
  let filtered := filterTautologies formula
  let clauses := normalizeClauses filtered.value
  let result := uniqueFormula clauses.value
  ⟨result.value,filtered.cells+clauses.cells+result.cells+
    2*(size formula+size filtered.value+size clauses.value+size result.value)+5⟩

theorem normalize_value {n : Nat} (formula : CNFFormula n) : (normalize formula).value=Eliminate.normalize formula := by
  simp only [normalize,uniqueFormula_value,normalizeClauses_value,filterTautologies_value,Eliminate.normalize]

theorem normalize_size {n : Nat} (formula : CNFFormula n) : size (normalize formula).value ≤ size formula := by
  rw [normalize_value]
  have literals : Extract.literalCount (Eliminate.normalize formula) ≤ Extract.literalCount formula :=
    Subsumption.normalize_literalCount_le formula
  have clauses := Eliminate.normalize_length_le formula
  unfold size CapacityMatching.RowCost.formulaCells
  omega

def normalizeBudget (limit : Nat) : Nat := filterBudget limit+clausesBudget limit+formulaBudget limit+8*limit+5

theorem normalize_cells {n : Nat} (formula : CNFFormula n) : (normalize formula).cells ≤ normalizeBudget (size formula) := by
  have first := filterTautologies_cells formula
  have filtered := filterTautologies_size formula
  have second := normalizeClauses_cells (filterTautologies formula).value
  have clauses := (normalizeClauses_size (filterTautologies formula).value).trans filtered
  have third := uniqueFormula_cells (normalizeClauses (filterTautologies formula).value).value
  have final := (uniqueFormula_size (normalizeClauses (filterTautologies formula).value).value).trans clauses
  have secondCost : (normalizeClauses (filterTautologies formula).value).cells ≤ clausesBudget (size formula) := by
    apply second.trans
    unfold clausesBudget literalsBudget
    gcongr
  have thirdCost : (uniqueFormula (normalizeClauses (filterTautologies formula).value).value).cells ≤ formulaBudget (size formula) := by
    apply third.trans
    unfold formulaBudget
    gcongr
  simp only [normalize,normalizeBudget]
  omega

end SaturationMonoid.ComplexityProjection.SATSource.AffineRelationExtractionCost
