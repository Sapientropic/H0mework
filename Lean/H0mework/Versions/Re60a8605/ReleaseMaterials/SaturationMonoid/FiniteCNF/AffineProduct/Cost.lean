import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineProduct.Core

/-!
Paired support extraction, component growth and product-tree construction.
The original rightmost deduplication order is retained. A growth round shares
one generated support and scans the original clauses into two lists once.
Visits include source-field and complete payload-copy allowances. Computing
the counters and implementing address bits/allocation as TM steps remain separate.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineProduct.Cost

open SaturationMonoid.ComplexityProjection.SATSource.Affine

structure Counted (α : Type) where
  value : α
  visits : Nat
  deriving Repr

def member {n : Nat} (i : Fin n) : List (Fin n) → Counted Bool
  | [] => ⟨false,1⟩
  | head::rest => if i == head then ⟨true,2⟩ else
      let next := member i rest
      ⟨next.value,next.visits+2⟩

theorem member_value {n : Nat} (i : Fin n) (vars : List (Fin n)) :
    (member i vars).value = decide (i ∈ vars) := by
  induction vars with
  | nil => rfl
  | cons head rest ih => simp only [member,List.mem_cons]; split <;> simp_all

theorem member_visits {n : Nat} (i : Fin n) (vars : List (Fin n)) : (member i vars).visits ≤ 2*vars.length+1 := by
  induction vars with
  | nil => rfl
  | cons head rest ih => simp only [member,List.length_cons]; split <;> simp only <;> omega

def unique {n : Nat} : List (Fin n) → Counted (List (Fin n))
  | [] => ⟨[],1⟩
  | head::rest =>
      let tail := unique rest
      let found := member head tail.value
      ⟨if found.value then tail.value else head::tail.value,
        tail.visits+found.visits+2*tail.value.length+4⟩

theorem unique_value {n : Nat} (vars : List (Fin n)) : (unique vars).value = vars.dedup := by
  induction vars with
  | nil => rfl
  | cons head rest ih => simp only [unique,member_value,ih,List.dedup_cons']; split <;> simp_all

theorem unique_length {n : Nat} (vars : List (Fin n)) : (unique vars).value.length ≤ vars.length := by
  rw [unique_value]
  exact (List.dedup_sublist vars).length_le

theorem unique_visits {n : Nat} (vars : List (Fin n)) : (unique vars).visits ≤ vars.length*(2*vars.length+5)+1 := by
  induction vars with
  | nil => simp [unique]
  | cons head rest ih =>
      have search := member_visits head (unique rest).value
      have size := unique_length rest
      simp only [unique,List.length_cons]
      nlinarith

def literalVars {n : Nat} : CNFClause n → Counted (List (Fin n))
  | [] => ⟨[],1⟩
  | literal::rest => let tail := literalVars rest; ⟨literal.var::tail.value,tail.visits+4⟩

theorem literalVars_value {n : Nat} (clause : CNFClause n) :
    (literalVars clause).value = clause.map CNFLiteral.var := by
  induction clause <;> simp_all [literalVars]

theorem literalVars_visits {n : Nat} (clause : CNFClause n) : (literalVars clause).visits = 4*clause.length+1 := by
  induction clause with
  | nil => rfl
  | cons literal rest ih => simp only [literalVars,ih,List.length_cons]; omega

def gatherVars {n : Nat} : CNFFormula n → Counted (List (Fin n))
  | [] => ⟨[],1⟩
  | clause::rest =>
      let first := literalVars clause
      let tail := gatherVars rest
      ⟨first.value++tail.value,first.visits+tail.visits+2*first.value.length+2*tail.value.length+5⟩

theorem gatherVars_value {n : Nat} (formula : CNFFormula n) :
    (gatherVars formula).value = formula.flatten.map CNFLiteral.var := by
  induction formula <;> simp_all [gatherVars,literalVars_value]

theorem gatherVars_length {n : Nat} (formula : CNFFormula n) : (gatherVars formula).value.length = Extract.literalCount formula := by
  simp only [gatherVars_value,List.length_map,List.length_flatten,Extract.literalCount]

theorem gatherVars_visits {n : Nat} (formula : CNFFormula n) :
    (gatherVars formula).visits ≤ formula.length*(6*Extract.literalCount formula+6)+1 := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      let total := Extract.literalCount (clause::rest)
      have restSize : Extract.literalCount rest ≤ total := by simp [total,Extract.literalCount]
      have tail : (gatherVars rest).visits ≤ rest.length*(6*total+6)+1 := ih.trans (by gcongr)
      have first : (literalVars clause).visits+2*(literalVars clause).value.length+2*(gatherVars rest).value.length+5 ≤ 6*total+6 := by
        simp only [literalVars_visits,literalVars_value,List.length_map,gatherVars_length,total,
          Extract.literalCount,List.map_cons,List.sum_cons]
        omega
      change _ ≤ (rest.length+1)*(6*total+6)+1
      calc
        _ = (gatherVars rest).visits+
            ((literalVars clause).visits+2*(literalVars clause).value.length+2*(gatherVars rest).value.length+5) := by
          simp only [gatherVars]
          ring
        _ ≤ (rest.length*(6*total+6)+1)+(6*total+6) := Nat.add_le_add tail first
        _ = _ := by ring

def sourceVars {n : Nat} (formula : CNFFormula n) : Counted (List (Fin n)) :=
  let input := gatherVars formula
  let normalized := unique input.value
  ⟨normalized.value,input.visits+normalized.visits+2*normalized.value.length+4⟩

theorem sourceVars_value {n : Nat} (formula : CNFFormula n) : (sourceVars formula).value = Shared.sourceVars formula := by
  simp only [sourceVars,unique_value,gatherVars_value,Shared.sourceVars]

theorem sourceVars_length {n : Nat} (formula : CNFFormula n) : (sourceVars formula).value.length ≤ Extract.literalCount formula := by
  exact (unique_length (gatherVars formula).value).trans_eq (gatherVars_length formula)

def supportBudget (clauses literals : Nat) : Nat := clauses*(6*literals+6)+1+literals*(2*literals+5)+1+2*literals+4

theorem sourceVars_visits {n : Nat} (formula : CNFFormula n) :
    (sourceVars formula).visits ≤ supportBudget formula.length (Extract.literalCount formula) := by
  have first := gatherVars_visits formula
  have second := unique_visits (gatherVars formula).value
  rw [gatherVars_length] at second
  have size := sourceVars_length formula
  change (gatherVars formula).visits+(unique (gatherVars formula).value).visits+
    2*(sourceVars formula).value.length+4 ≤ _
  unfold supportBudget
  omega

def touches {n : Nat} (support : List (Fin n)) : CNFClause n → Counted Bool
  | [] => ⟨false,1⟩
  | literal::rest =>
      let found := member literal.var support
      if found.value then ⟨true,found.visits+2⟩ else
        let tail := touches support rest
        ⟨tail.value,found.visits+tail.visits+2⟩

theorem touches_value {n : Nat} (support : List (Fin n)) (clause : CNFClause n) :
    (touches support clause).value = clause.any (fun literal => decide (literal.var ∈ support)) := by
  induction clause with
  | nil => rfl
  | cons literal rest ih => simp only [touches,member_value,List.any_cons]; split <;> simp_all

theorem touches_visits {n : Nat} (support : List (Fin n)) (clause : CNFClause n) :
    (touches support clause).visits ≤ clause.length*(2*support.length+3)+1 := by
  induction clause with
  | nil => simp [touches]
  | cons literal rest ih =>
      have first := member_visits literal.var support
      simp only [touches,List.length_cons]
      split <;> simp only <;> nlinarith

abbrev formulaSize {n : Nat} (formula : CNFFormula n) : Nat := CapacityMatching.RowCost.formulaCells formula

@[simp] theorem literals_append {n : Nat} (left right : CNFFormula n) :
    Extract.literalCount (left++right) = Extract.literalCount left+Extract.literalCount right := by simp [Extract.literalCount]

def partition {n : Nat} (support : List (Fin n)) : CNFFormula n → Counted (CNFFormula n × CNFFormula n)
  | [] => ⟨([],[]),1⟩
  | clause::rest =>
      let tested := touches support clause
      let tail := partition support rest
      ⟨if tested.value then (clause::tail.value.1,tail.value.2) else (tail.value.1,clause::tail.value.2),
        tested.visits+tail.visits+2*(formulaSize tail.value.1+formulaSize tail.value.2)+3*clause.length+6⟩

theorem partition_value {n : Nat} (support : List (Fin n)) (formula : CNFFormula n) :
    (partition support formula).value =
      (formula.filter (fun clause => clause.any (fun literal => decide (literal.var ∈ support))),
       formula.filter (fun clause => !clause.any (fun literal => decide (literal.var ∈ support)))) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [partition,touches_value,ih,List.filter_cons]
      cases clause.any (fun literal => decide (literal.var ∈ support)) <;> rfl

theorem partition_counts {n : Nat} (support : List (Fin n)) (formula : CNFFormula n) :
    (partition support formula).value.1.length+(partition support formula).value.2.length = formula.length ∧
      Extract.literalCount (partition support formula).value.1+Extract.literalCount (partition support formula).value.2 = Extract.literalCount formula := by
  induction formula with
  | nil => exact ⟨rfl,rfl⟩
  | cons clause rest ih =>
      simp only [partition]
      split <;> simp only [List.length_cons,Extract.literalCount,List.map_cons,List.sum_cons] at * <;> omega

def partitionBudget (support clauses literals : Nat) : Nat := clauses*(literals*(2*support+12)+4*clauses+16)+1

theorem partition_visits {n : Nat} (support : List (Fin n)) (formula : CNFFormula n) :
    (partition support formula).visits ≤ partitionBudget support.length formula.length (Extract.literalCount formula) := by
  induction formula with
  | nil => simp [partition,partitionBudget]
  | cons clause rest ih =>
      have first := touches_visits support clause
      have counts := partition_counts support rest
      let total := Extract.literalCount (clause::rest)
      let unit := total*(2*support.length+12)+4*(rest.length+1)+16
      have sizes : clause.length ≤ total ∧ Extract.literalCount rest ≤ total := by
        simp [total,Extract.literalCount]
      have firstBound : (touches support clause).visits ≤ total*(2*support.length+3)+1 := first.trans (by gcongr; exact sizes.1)
      have copies : 2*(formulaSize (partition support rest).value.1+formulaSize (partition support rest).value.2)+3*clause.length+6 ≤
          6*total+4*rest.length+10 := by
        simp only [formulaSize,CapacityMatching.RowCost.formulaCells,total,Extract.literalCount,List.map_cons,List.sum_cons] at *
        omega
      have step : (touches support clause).visits+
          (2*(formulaSize (partition support rest).value.1+formulaSize (partition support rest).value.2)+3*clause.length+6) ≤ unit := by
        apply (Nat.add_le_add firstBound copies).trans
        unfold unit
        nlinarith
      have tail : (partition support rest).visits ≤ rest.length*unit+1 := by
        apply ih.trans
        unfold partitionBudget unit
        gcongr <;> omega
      change _ ≤ (rest.length+1)*unit+1
      calc
        _ = (partition support rest).visits+((touches support clause).visits+
            (2*(formulaSize (partition support rest).value.1+formulaSize (partition support rest).value.2)+3*clause.length+6)) := by
          simp only [partition]
          ring
        _ ≤ (rest.length*unit+1)+unit := Nat.add_le_add tail step
        _ = _ := by ring

def grow {n : Nat} : Nat → CNFFormula n → CNFFormula n → Counted (CNFFormula n × CNFFormula n)
  | 0,component,rest => ⟨(component,rest),2*(formulaSize component+formulaSize rest)+3⟩
  | fuel+1,component,rest =>
      let support := sourceVars component
      let split := partition support.value rest
      if split.value.1 = [] then
        ⟨(component,rest),support.visits+split.visits+6*(formulaSize component+formulaSize rest)+10⟩
      else
        let next := grow fuel (component++split.value.1) split.value.2
        ⟨next.value,support.visits+split.visits+next.visits+4*(formulaSize component+formulaSize rest)+
          2*(formulaSize next.value.1+formulaSize next.value.2)+10⟩

theorem partition_source_value {n : Nat} (component rest : CNFFormula n) :
    (partition (sourceVars component).value rest).value =
      (rest.filter (Factor.touches component),rest.filter (fun clause => !Factor.touches component clause)) := by
  rw [sourceVars_value,partition_value]
  rfl

theorem grow_value {n : Nat} (fuel : Nat) (component rest : CNFFormula n) :
    (grow fuel component rest).value = Factor.grow fuel component rest := by
  induction fuel generalizing component rest with
  | zero => rfl
  | succ fuel ih =>
      simp only [grow,Factor.grow,partition_source_value,ih]
      split <;> rfl

theorem grow_counts {n : Nat} (fuel : Nat) (component rest : CNFFormula n) :
    (grow fuel component rest).value.1.length+(grow fuel component rest).value.2.length = component.length+rest.length ∧
      Extract.literalCount (grow fuel component rest).value.1+Extract.literalCount (grow fuel component rest).value.2 =
        Extract.literalCount component+Extract.literalCount rest := by
  induction fuel generalizing component rest with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
      have partitioned := partition_counts (sourceVars component).value rest
      simp only [grow]
      split
      · exact ⟨rfl,rfl⟩
      · dsimp only
        have tail := ih (component++(partition (sourceVars component).value rest).value.1)
          (partition (sourceVars component).value rest).value.2
        simp only [List.length_append,literals_append] at tail
        omega

theorem original_grow_counts {n : Nat} (fuel : Nat) (component rest : CNFFormula n) :
    (Factor.grow fuel component rest).1.length+(Factor.grow fuel component rest).2.length = component.length+rest.length ∧
      Extract.literalCount (Factor.grow fuel component rest).1+Extract.literalCount (Factor.grow fuel component rest).2 =
        Extract.literalCount component+Extract.literalCount rest := by simpa only [grow_value] using grow_counts fuel component rest

def roundBudget (clauses literals : Nat) : Nat :=
  supportBudget clauses literals+partitionBudget literals clauses literals+18*literals+12*clauses+25

def growBudget (fuel clauses literals : Nat) : Nat := fuel*roundBudget clauses literals+6*literals+4*clauses+7

theorem grow_visits {n : Nat} (fuel : Nat) (component rest : CNFFormula n) :
    (grow fuel component rest).visits ≤ growBudget fuel (component.length+rest.length)
      (Extract.literalCount component+Extract.literalCount rest) := by
  induction fuel generalizing component rest with
  | zero => simp [grow,growBudget,formulaSize,CapacityMatching.RowCost.formulaCells]; omega
  | succ fuel ih =>
      have support := sourceVars_visits component
      have supportSize := sourceVars_length component
      have splitting := partition_visits (sourceVars component).value rest
      have supportBound : (sourceVars component).visits ≤ supportBudget (component.length+rest.length)
          (Extract.literalCount component+Extract.literalCount rest) := by
        apply support.trans
        unfold supportBudget
        gcongr <;> omega
      have splitBound : (partition (sourceVars component).value rest).visits ≤
          partitionBudget (Extract.literalCount component+Extract.literalCount rest) (component.length+rest.length)
            (Extract.literalCount component+Extract.literalCount rest) := by
        apply splitting.trans
        unfold partitionBudget
        gcongr <;> omega
      simp only [grow]
      split
      · simp only [growBudget,roundBudget,formulaSize,CapacityMatching.RowCost.formulaCells]
        nlinarith
      · let nextComponent := component++(partition (sourceVars component).value rest).value.1
        let nextRest := (partition (sourceVars component).value rest).value.2
        have divided := partition_counts (sourceVars component).value rest
        have count : nextComponent.length+nextRest.length = component.length+rest.length := by
          dsimp only [nextComponent,nextRest]
          simp only [List.length_append]
          omega
        have literals : Extract.literalCount nextComponent+Extract.literalCount nextRest =
            Extract.literalCount component+Extract.literalCount rest := by
          dsimp only [nextComponent,nextRest]
          rw [literals_append]
          omega
        have tail := ih nextComponent nextRest
        rw [count,literals] at tail
        have retained := grow_counts fuel nextComponent nextRest
        rw [count,literals] at retained
        change (sourceVars component).visits+(partition (sourceVars component).value rest).visits+
          (grow fuel nextComponent nextRest).visits+4*(formulaSize component+formulaSize rest)+
          2*(formulaSize (grow fuel nextComponent nextRest).value.1+formulaSize (grow fuel nextComponent nextRest).value.2)+10 ≤ _
        simp only [growBudget,roundBudget,formulaSize,CapacityMatching.RowCost.formulaCells] at tail ⊢
        nlinarith

theorem growBudget_mono (fuel fuel' clauses clauses' literals literals' : Nat)
    (hf : fuel ≤ fuel') (hm : clauses ≤ clauses') (hl : literals ≤ literals') :
    growBudget fuel clauses literals ≤ growBudget fuel' clauses' literals' := by
  unfold growBudget roundBudget supportBudget partitionBudget
  gcongr

def treeSize {n : Nat} : Tree n → Nat
  | .unit => 1
  | .part source model rest => formulaSize source+AffineCarrier.storage model.value+7+treeSize rest

def sourceClauses {n : Nat} : Tree n → Nat
  | .unit => 0
  | .part source _ rest => source.length+sourceClauses rest

def sourceLiterals {n : Nat} : Tree n → Nat
  | .unit => 0
  | .part source _ rest => Extract.literalCount source+sourceLiterals rest

def modelStorage {n : Nat} : Tree n → Nat
  | .unit => 0
  | .part _ model rest => AffineCarrier.storage model.value+modelStorage rest

def modelBudget {n : Nat} : Tree n → Nat
  | .unit => 0
  | .part source _ rest => AffineCarrier.Cost.seedBudget n source.length (Extract.literalCount source)+
      AffineCarrier.Cost.runBudget n source 1+2+modelBudget rest

structure Built (n : Nat) where
  value : Tree n
  grouping : Nat
  copies : Nat
  visits : Nat

def build {n : Nat} : Nat → CNFFormula n → Built n
  | _,[] => ⟨.unit,0,1,1⟩
  | 0,formula =>
      let model := AffineCarrier.generate formula
      let tree := Tree.part formula model .unit
      let copied := 2*treeSize tree+5
      ⟨tree,0,copied,model.visits+copied⟩
  | fuel+1,clause::rest =>
      let factors := grow rest.length [clause] rest
      let model := AffineCarrier.generate factors.value.1
      let tail := build fuel factors.value.2
      let tree := Tree.part factors.value.1 model tail.value
      let copied := 2*treeSize tree+2*formulaSize (clause::rest)+8
      ⟨tree,factors.visits+tail.grouping,tail.copies+copied,
        factors.visits+model.visits+tail.visits+copied⟩

theorem build_value {n : Nat} (fuel : Nat) (formula : CNFFormula n) : (build fuel formula).value = AffineProduct.build fuel formula := by
  induction fuel generalizing formula with
  | zero => cases formula <;> rfl
  | succ fuel ih => cases formula <;> simp only [build,AffineProduct.build,ih,grow_value]

theorem build_account {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    (build fuel formula).visits = (build fuel formula).grouping+(build fuel formula).copies+
      AffineProduct.modelVisits (build fuel formula).value := by
  induction fuel generalizing formula with
  | zero =>
      cases formula <;> simp [build,AffineProduct.modelVisits]
      omega
  | succ fuel ih =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          have tail := ih (grow rest.length [clause] rest).value.2
          simp only [build,AffineProduct.modelVisits]
          omega

theorem build_source_counts {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    sourceClauses (build fuel formula).value = formula.length ∧
      sourceLiterals (build fuel formula).value = Extract.literalCount formula := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [build,sourceClauses,sourceLiterals,Extract.literalCount]
  | succ fuel ih =>
      cases formula with
      | nil => exact ⟨rfl,rfl⟩
      | cons clause rest =>
          have tail := ih (grow rest.length [clause] rest).value.2
          have source := grow_counts rest.length [clause] rest
          simp only [build,sourceClauses,sourceLiterals,tail.1,tail.2]
          simp only [List.length_cons,List.length_nil,Extract.literalCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at source ⊢
          omega

theorem treeSize_eq {n : Nat} (tree : Tree n) : treeSize tree =
    modelStorage tree+3*sourceLiterals tree+2*sourceClauses tree+8*parts tree+1 := by
  induction tree with
  | unit => rfl
  | part source model rest ih =>
      simp only [treeSize,modelStorage,sourceLiterals,sourceClauses,parts,formulaSize,CapacityMatching.RowCost.formulaCells]
      omega

theorem build_modelStorage {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    modelStorage (build fuel formula).value ≤ storedCells (build fuel formula).value*AffineCarrier.Cost.cellBound n := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => simp [build,modelStorage,storedCells]
      | cons clause rest =>
          simpa only [build,modelStorage,storedCells,Nat.add_zero] using
            AffineCarrier.Cost.storage_bound n _ (AffineCarrier.generate_valid (clause::rest))
  | succ fuel ih =>
      cases formula with
      | nil => simp [build,modelStorage,storedCells]
      | cons clause rest =>
          have tail := ih (grow rest.length [clause] rest).value.2
          have first := AffineCarrier.Cost.storage_bound n _
            (AffineCarrier.generate_valid (grow rest.length [clause] rest).value.1)
          simp only [build,modelStorage,storedCells]
          nlinarith

theorem build_treeSize {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    treeSize (build fuel formula).value ≤ 3*Extract.literalCount formula+10*formula.length+
      storedCells (build fuel formula).value*AffineCarrier.Cost.cellBound n+1 := by
  have stored := build_modelStorage fuel formula
  have source := build_source_counts fuel formula
  have count : parts (build fuel formula).value ≤ formula.length := by
    rw [build_value]
    exact build_parts fuel formula
  have size := treeSize_eq (build fuel formula).value
  rw [source.1,source.2] at size
  omega

theorem build_modelBudget {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    AffineProduct.modelVisits (build fuel formula).value ≤ modelBudget (build fuel formula).value := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          simpa only [build,AffineProduct.modelVisits,modelBudget,Nat.add_zero] using AffineCarrier.Cost.generate_visits (clause::rest)
  | succ fuel ih =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          have first := AffineCarrier.Cost.generate_visits (grow rest.length [clause] rest).value.1
          have tail := ih (grow rest.length [clause] rest).value.2
          simp only [build,AffineProduct.modelVisits,modelBudget]
          omega

theorem build_grouping {n : Nat} (fuel : Nat) (formula : CNFFormula n) (clauses literals : Nat)
    (clauseBound : formula.length ≤ clauses) (literalBound : Extract.literalCount formula ≤ literals) :
    (build fuel formula).grouping ≤ formula.length*growBudget clauses clauses literals := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [build]
  | succ fuel ih =>
      cases formula with
      | nil => simp [build]
      | cons clause rest =>
          have counts := grow_counts rest.length [clause] rest
          have restCount : (grow rest.length [clause] rest).value.2.length ≤ rest.length := by
            rw [grow_value]
            exact Factor.grow_rest_length_le _ _ _
          have restLiterals : Extract.literalCount (grow rest.length [clause] rest).value.2 ≤ Extract.literalCount (clause::rest) := by
            simp only [Extract.literalCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at counts ⊢
            omega
          have tail := ih (grow rest.length [clause] rest).value.2 (by simpa using restCount.trans (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) clauseBound)))
            (restLiterals.trans literalBound)
          have first := grow_visits rest.length [clause] rest
          have charged : (grow rest.length [clause] rest).visits ≤ growBudget clauses clauses literals := by
            apply first.trans
            apply growBudget_mono
            · simp only [List.length_cons] at clauseBound
              omega
            · simp only [List.length_cons,List.length_nil] at *
              omega
            · simpa [Extract.literalCount] using literalBound
          simp only [build,List.length_cons]
          nlinarith

theorem build_copies {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    (build fuel formula).copies ≤ (fuel+1)*(2*treeSize (build fuel formula).value+2*formulaSize formula+8)+1 := by
  induction fuel generalizing formula with
  | zero =>
      cases formula <;> simp [build,treeSize]
      omega
  | succ fuel ih =>
      cases formula with
      | nil => simp [build,treeSize]
      | cons clause rest =>
          let factors := (grow rest.length [clause] rest).value
          let tail := build fuel factors.2
          let tree := Tree.part factors.1 (AffineCarrier.generate factors.1) tail.value
          have copies := ih factors.2
          have counts := grow_counts rest.length [clause] rest
          have count : factors.2.length ≤ (clause::rest).length := by
            simp only [List.length_cons,List.length_nil] at counts ⊢
            dsimp only [factors]
            omega
          have literals : Extract.literalCount factors.2 ≤ Extract.literalCount (clause::rest) := by
            simp only [Extract.literalCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at counts ⊢
            dsimp only [factors]
            omega
          have formulaBound : formulaSize factors.2 ≤ formulaSize (clause::rest) := by
            unfold formulaSize CapacityMatching.RowCost.formulaCells
            gcongr
          have treeBound : treeSize tail.value ≤ treeSize tree := by dsimp only [tree,treeSize]; omega
          have bounded : tail.copies ≤ (fuel+1)*(2*treeSize tree+2*formulaSize (clause::rest)+8)+1 := by
            apply copies.trans
            gcongr
          change tail.copies+(2*treeSize tree+2*formulaSize (clause::rest)+8) ≤
            (fuel+1+1)*(2*treeSize tree+2*formulaSize (clause::rest)+8)+1
          nlinarith

theorem build_visits {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    (build fuel formula).visits ≤ modelBudget (build fuel formula).value+
      formula.length*growBudget formula.length formula.length (Extract.literalCount formula)+
      (fuel+1)*(2*treeSize (build fuel formula).value+2*formulaSize formula+8)+1 := by
  have grouping := build_grouping fuel formula formula.length (Extract.literalCount formula) (Nat.le_refl _) (Nat.le_refl _)
  have copying := build_copies fuel formula
  have models := build_modelBudget fuel formula
  rw [build_account]
  omega

def generate {n : Nat} (formula : CNFFormula n) : Built n := build formula.length formula

theorem generate_value {n : Nat} (formula : CNFFormula n) : (generate formula).value = AffineProduct.generate formula := build_value _ _

def overheadBudget (n clauses literals stored : Nat) : Nat :=
  clauses*growBudget clauses clauses literals+
    (clauses+1)*(2*(3*literals+10*clauses+stored*AffineCarrier.Cost.cellBound n+1)+
      2*(3*literals+2*clauses+1)+8)+1

theorem generate_visits {n : Nat} (formula : CNFFormula n) :
    (generate formula).visits ≤ modelBudget (generate formula).value+
      overheadBudget n formula.length (Extract.literalCount formula) (storedCells (generate formula).value) := by
  have bound := build_visits formula.length formula
  have stored := build_treeSize formula.length formula
  apply bound.trans
  unfold overheadBudget formulaSize CapacityMatching.RowCost.formulaCells generate
  simp only [Nat.add_assoc]
  gcongr
  simpa only [Nat.add_assoc] using stored

def readPossible {n : Nat} : Tree n → Counted Bool
  | .unit => ⟨true,1⟩
  | .part _ model rest =>
      let tail := readPossible rest
      ⟨!model.value.isEmpty && tail.value,tail.visits+4⟩

theorem readPossible_value {n : Nat} (tree : Tree n) : (readPossible tree).value = AffineProduct.possible tree := by
  induction tree <;> simp_all [readPossible,AffineProduct.possible]

theorem readPossible_visits {n : Nat} (tree : Tree n) : (readPossible tree).visits = 4*parts tree+1 := by
  induction tree with
  | unit => rfl
  | part source model rest ih => simp only [readPossible,parts,ih]; omega

def decideFormula {n : Nat} (formula : CNFFormula n) : Counted Bool :=
  let generated := generate formula
  let answer := readPossible generated.value
  ⟨answer.value,generated.visits+answer.visits+1⟩

theorem decideFormula_value {n : Nat} (formula : CNFFormula n) : (decideFormula formula).value = AffineProduct.decideFormula formula := by
  simp only [decideFormula,readPossible_value,generate_value,AffineProduct.decideFormula]

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    (decideFormula formula).value = true ↔ CNFSatisfiable formula := by rw [decideFormula_value,AffineProduct.decideFormula_correct]

theorem decideFormula_visits {n : Nat} (formula : CNFFormula n) :
    (decideFormula formula).visits ≤ modelBudget (generate formula).value+
      overheadBudget n formula.length (Extract.literalCount formula) (storedCells (generate formula).value)+4*formula.length+2 := by
  have generation := generate_visits formula
  have count : parts (generate formula).value ≤ formula.length := by
    rw [generate_value]
    exact build_parts _ _
  simp only [decideFormula,readPossible_visits]
  omega

end SaturationMonoid.ComplexityProjection.SATSource.AffineProduct.Cost
