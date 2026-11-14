import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineProduct.Cost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.JointCost

/-!
Paired full-row support grouping and the actual joint-component producer.
Rightmost deduplication and all original clause/row/term occurrences are retained.
One support is shared by each dual partition. Ledgers include full payload copies;
Nat-address bit operations and counter evaluation are not identified with TM steps.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauseProduct.Cost

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Clause Formula Within formulaRead formulaSize)
open AffineClauses.Cost (rowCount termCount formula_size)
open CapacityMatching.RowCost (rowsCells rowCells)
open AffineCarrier (Cells storage)

abbrev Counted := AffineProduct.Cost.Counted

def member (i : Nat) : List Nat → Counted Bool
  | [] => ⟨false,1⟩
  | head::rest => if i == head then ⟨true,2⟩ else
      let next := member i rest
      ⟨next.value,next.visits+2⟩

theorem member_value (i : Nat) (vars : List Nat) : (member i vars).value = decide (i ∈ vars) := by
  induction vars with
  | nil => rfl
  | cons head rest ih => simp only [member,List.mem_cons]; split <;> simp_all

theorem member_visits (i : Nat) (vars : List Nat) : (member i vars).visits ≤ 2*vars.length+1 := by
  induction vars with
  | nil => rfl
  | cons head rest ih => simp only [member,List.length_cons]; split <;> simp only <;> omega

def unique : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | head::rest =>
      let tail := unique rest
      let found := member head tail.value
      ⟨if found.value then tail.value else head::tail.value,
        tail.visits+found.visits+2*tail.value.length+4⟩

theorem unique_value (vars : List Nat) : (unique vars).value = vars.dedup := by
  induction vars with
  | nil => rfl
  | cons head rest ih => simp only [unique,member_value,ih,List.dedup_cons']; split <;> simp_all

theorem unique_length (vars : List Nat) : (unique vars).value.length ≤ vars.length := by
  rw [unique_value]
  exact (List.dedup_sublist vars).length_le

theorem unique_visits (vars : List Nat) : (unique vars).visits ≤ vars.length*(2*vars.length+5)+1 := by
  induction vars with
  | nil => rfl
  | cons head rest ih =>
      have search := member_visits head (unique rest).value
      have size := unique_length rest
      simp only [unique,List.length_cons]
      nlinarith

def copyVars : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | head::rest => let tail := copyVars rest; ⟨head::tail.value,tail.visits+3⟩

theorem copyVars_value (vars : List Nat) : (copyVars vars).value = vars := by
  induction vars <;> simp_all [copyVars]

theorem copyVars_visits (vars : List Nat) : (copyVars vars).visits = 3*vars.length+1 := by
  induction vars with
  | nil => rfl
  | cons head rest ih => simp only [copyVars,ih,List.length_cons]; omega

def clauseVars : Clause → Counted (List Nat)
  | [] => ⟨[],1⟩
  | row::rest =>
      let first := copyVars row.vars
      let tail := clauseVars rest
      ⟨first.value++tail.value,first.visits+tail.visits+2*(first.value.length+tail.value.length)+5⟩

theorem clauseVars_value (clause : Clause) : (clauseVars clause).value = clause.flatMap Row.vars := by
  induction clause <;> simp_all [clauseVars,copyVars_value]

theorem clauseVars_length (clause : Clause) : (clauseVars clause).value.length = Gates.rowTerms clause := by
  induction clause <;> simp_all [clauseVars,copyVars_value]

theorem terms_le_rows (clause : Clause) : Gates.rowTerms clause ≤ rowsCells clause := by
  rw [AffineCollect.Cost.rows_size]
  omega

theorem clauseVars_visits (clause : Clause) :
    (clauseVars clause).visits ≤ rowsCells clause*(2*rowsCells clause+6)+1 := by
  induction clause with
  | nil => rfl
  | cons row rest ih =>
      have size := terms_le_rows rest
      simp only [clauseVars,copyVars_visits,copyVars_value,clauseVars_length,
        CapacityMatching.RowCost.rowsCells_cons,rowCells]
      nlinarith

def gatherVars : Formula → Counted (List Nat)
  | [] => ⟨[],1⟩
  | clause::rest =>
      let first := clauseVars clause
      let tail := gatherVars rest
      ⟨first.value++tail.value,first.visits+tail.visits+2*(first.value.length+tail.value.length)+5⟩

theorem gatherVars_value (formula : Formula) :
    (gatherVars formula).value = formula.flatten.flatMap Row.vars := by
  induction formula <;> simp_all [gatherVars,clauseVars_value]

theorem gatherVars_length (formula : Formula) : (gatherVars formula).value.length = termCount formula := by
  induction formula <;> simp_all [gatherVars,clauseVars_length]

theorem terms_le_size (formula : Formula) : termCount formula ≤ formulaSize formula := by
  rw [formula_size]
  omega

theorem size_positive (formula : Formula) : 1 ≤ formulaSize formula := by
  rw [formula_size]
  omega

theorem gatherVars_visits (formula : Formula) :
    (gatherVars formula).visits ≤ formulaSize formula*(2*formulaSize formula+8)+1 := by
  induction formula with
  | nil => simp [gatherVars]
  | cons clause rest ih =>
      have first := clauseVars_visits clause
      have firstSize := terms_le_rows clause
      have tailSize := terms_le_size rest
      simp only [gatherVars,clauseVars_length,gatherVars_length,AffineClauses.Cost.formulaSize_cons]
      nlinarith

def support (formula : Formula) : Counted (List Nat) :=
  let input := gatherVars formula
  let normalized := unique input.value
  ⟨normalized.value,input.visits+normalized.visits+2*normalized.value.length+4⟩

theorem support_value (formula : Formula) : (support formula).value = AffineClauseProduct.support formula := by
  simp only [support,unique_value,gatherVars_value,AffineClauseProduct.support]

theorem support_length (formula : Formula) : (support formula).value.length ≤ termCount formula :=
  (unique_length (gatherVars formula).value).trans_eq (gatherVars_length formula)

def supportBudget (size : Nat) : Nat := size*(4*size+20)+8

theorem support_visits (formula : Formula) : (support formula).visits ≤ supportBudget (formulaSize formula) := by
  have first := gatherVars_visits formula
  have second := unique_visits (gatherVars formula).value
  rw [gatherVars_length] at second
  have size := support_length formula
  have total := terms_le_size formula
  have secondBound : (unique (gatherVars formula).value).visits ≤ formulaSize formula*(2*formulaSize formula+5)+1 := by
    apply second.trans
    gcongr
  change (gatherVars formula).visits+(unique (gatherVars formula).value).visits+2*(support formula).value.length+4 ≤ _
  unfold supportBudget
  nlinarith

def termsTouch (support : List Nat) : List Nat → Counted Bool
  | [] => ⟨false,1⟩
  | i::rest =>
      let found := member i support
      if found.value then ⟨true,found.visits+2⟩ else
        let tail := termsTouch support rest
        ⟨tail.value,found.visits+tail.visits+2⟩

theorem termsTouch_value (support : List Nat) (vars : List Nat) :
    (termsTouch support vars).value = vars.any (fun i => decide (i ∈ support)) := by
  induction vars with
  | nil => rfl
  | cons i rest ih => simp only [termsTouch,member_value,List.any_cons]; split <;> simp_all

theorem termsTouch_visits (support vars : List Nat) :
    (termsTouch support vars).visits ≤ vars.length*(2*support.length+3)+1 := by
  induction vars with
  | nil => simp [termsTouch]
  | cons i rest ih =>
      have first := member_visits i support
      simp only [termsTouch,List.length_cons]
      split <;> simp only <;> nlinarith

def touches (support : List Nat) : Clause → Counted Bool
  | [] => ⟨false,1⟩
  | row::rest =>
      let found := termsTouch support row.vars
      if found.value then ⟨true,found.visits+2⟩ else
        let tail := touches support rest
        ⟨tail.value,found.visits+tail.visits+2⟩

theorem touches_value (support : List Nat) (clause : Clause) :
    (touches support clause).value = clause.any (fun row => row.vars.any (fun i => decide (i ∈ support))) := by
  induction clause with
  | nil => rfl
  | cons row rest ih => simp only [touches,termsTouch_value,List.any_cons]; split <;> simp_all

theorem touches_visits (support : List Nat) (clause : Clause) :
    (touches support clause).visits ≤ rowsCells clause*(2*support.length+5)+1 := by
  induction clause with
  | nil => simp [touches]
  | cons row rest ih =>
      have first := termsTouch_visits support row.vars
      simp only [touches,CapacityMatching.RowCost.rowsCells_cons,rowCells]
      split <;> simp only <;> nlinarith

@[simp] theorem rowCount_append (left right : Formula) : rowCount (left++right) = rowCount left+rowCount right := by
  simp [rowCount]

@[simp] theorem termCount_append (left right : Formula) : termCount (left++right) = termCount left+termCount right := by
  simp [termCount]

theorem size_append (left right : Formula) : formulaSize (left++right)+1 = formulaSize left+formulaSize right := by
  simp only [formula_size,rowCount_append,termCount_append,List.length_append]
  omega

def partition (support : List Nat) : Formula → Counted (Formula × Formula)
  | [] => ⟨([],[]),1⟩
  | clause::rest =>
      let tested := touches support clause
      let tail := partition support rest
      ⟨if tested.value then (clause::tail.value.1,tail.value.2) else (tail.value.1,clause::tail.value.2),
        tested.visits+tail.visits+2*(formulaSize tail.value.1+formulaSize tail.value.2)+2*rowsCells clause+8⟩

theorem partition_value (support : List Nat) (formula : Formula) :
    (partition support formula).value =
      (formula.filter (fun clause => clause.any (fun row => row.vars.any (fun i => decide (i ∈ support)))),
       formula.filter (fun clause => !clause.any (fun row => row.vars.any (fun i => decide (i ∈ support))))) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [partition,touches_value,ih,List.filter_cons]
      cases clause.any (fun row => row.vars.any (fun i => decide (i ∈ support))) <;> rfl

theorem partition_counts (support : List Nat) (formula : Formula) :
    (partition support formula).value.1.length+(partition support formula).value.2.length = formula.length ∧
      rowCount (partition support formula).value.1+rowCount (partition support formula).value.2 = rowCount formula ∧
      termCount (partition support formula).value.1+termCount (partition support formula).value.2 = termCount formula := by
  induction formula with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons clause rest ih =>
      simp only [partition]
      split <;> simp only [List.length_cons,AffineClauses.Cost.rowCount_cons,AffineClauses.Cost.termCount_cons] at * <;> omega

theorem partition_size (support : List Nat) (formula : Formula) :
    formulaSize (partition support formula).value.1+formulaSize (partition support formula).value.2 = formulaSize formula+1 := by
  have counts := partition_counts support formula
  simp only [formula_size]
  omega

def partitionBudget (support size : Nat) : Nat := size*(size*(2*support+12)+20)+1

theorem partition_visits (support : List Nat) (formula : Formula) :
    (partition support formula).visits ≤ partitionBudget support.length (formulaSize formula) := by
  induction formula with
  | nil => simp [partition,partitionBudget]
  | cons clause rest ih =>
      have first := touches_visits support clause
      have counts := partition_size support rest
      have positive := size_positive rest
      simp only [partition,AffineClauses.Cost.formulaSize_cons,partitionBudget] at *
      nlinarith

def grow : Nat → Formula → Formula → Counted (Formula × Formula)
  | 0,component,rest => ⟨(component,rest),2*(formulaSize component+formulaSize rest)+3⟩
  | fuel+1,component,rest =>
      let shared := support component
      let divided := partition shared.value rest
      if divided.value.1 = [] then
        ⟨(component,rest),shared.visits+divided.visits+6*(formulaSize component+formulaSize rest)+10⟩
      else
        let next := grow fuel (component++divided.value.1) divided.value.2
        ⟨next.value,shared.visits+divided.visits+next.visits+4*(formulaSize component+formulaSize rest)+
          2*(formulaSize next.value.1+formulaSize next.value.2)+10⟩

theorem partition_source_value (component rest : Formula) :
    (partition (support component).value rest).value =
      (rest.filter (AffineClauseProduct.touches component),rest.filter (fun clause => !AffineClauseProduct.touches component clause)) := by
  rw [support_value,partition_value]
  rfl

theorem grow_value (fuel : Nat) (component rest : Formula) :
    (grow fuel component rest).value = AffineClauseProduct.grow fuel component rest := by
  induction fuel generalizing component rest with
  | zero => rfl
  | succ fuel ih =>
      simp only [grow,AffineClauseProduct.grow,partition_source_value,ih]
      split <;> rfl

theorem grow_counts (fuel : Nat) (component rest : Formula) :
    (grow fuel component rest).value.1.length+(grow fuel component rest).value.2.length = component.length+rest.length ∧
      rowCount (grow fuel component rest).value.1+rowCount (grow fuel component rest).value.2 = rowCount component+rowCount rest ∧
      termCount (grow fuel component rest).value.1+termCount (grow fuel component rest).value.2 = termCount component+termCount rest := by
  induction fuel generalizing component rest with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ fuel ih =>
      have divided := partition_counts (support component).value rest
      simp only [grow]
      split
      · exact ⟨rfl,rfl,rfl⟩
      · dsimp only
        have tail := ih (component++(partition (support component).value rest).value.1)
          (partition (support component).value rest).value.2
        simp only [List.length_append,rowCount_append,termCount_append] at tail
        omega

theorem grow_size (fuel : Nat) (component rest : Formula) :
    formulaSize (grow fuel component rest).value.1+formulaSize (grow fuel component rest).value.2 =
      formulaSize component+formulaSize rest := by
  have counts := grow_counts fuel component rest
  simp only [formula_size]
  omega

def roundBudget (size : Nat) : Nat := supportBudget size+partitionBudget size size+6*size+10
def growBudget (fuel size : Nat) : Nat := fuel*roundBudget size+2*size+3

theorem grow_visits (fuel : Nat) (component rest : Formula) :
    (grow fuel component rest).visits ≤ growBudget fuel (formulaSize component+formulaSize rest) := by
  induction fuel generalizing component rest with
  | zero => simp [grow,growBudget]
  | succ fuel ih =>
      have shared := support_visits component
      have sharedSize := (support_length component).trans (terms_le_size component)
      have split := partition_visits (support component).value rest
      have sharedBound : (support component).visits ≤ supportBudget (formulaSize component+formulaSize rest) := by
        apply shared.trans
        unfold supportBudget
        gcongr <;> omega
      have splitBound : (partition (support component).value rest).visits ≤
          partitionBudget (formulaSize component+formulaSize rest) (formulaSize component+formulaSize rest) := by
        apply split.trans
        unfold partitionBudget
        gcongr <;> omega
      simp only [grow]
      split
      · simp only [growBudget,roundBudget]
        nlinarith
      · let nextComponent := component++(partition (support component).value rest).value.1
        let nextRest := (partition (support component).value rest).value.2
        have divided := partition_size (support component).value rest
        have account : formulaSize nextComponent+formulaSize nextRest = formulaSize component+formulaSize rest := by
          have joined := size_append component (partition (support component).value rest).value.1
          dsimp only [nextComponent,nextRest]
          omega
        have tail := ih nextComponent nextRest
        rw [account] at tail
        have output := grow_size fuel nextComponent nextRest
        rw [account] at output
        change (support component).visits+(partition (support component).value rest).visits+
          (grow fuel nextComponent nextRest).visits+4*(formulaSize component+formulaSize rest)+
          2*(formulaSize (grow fuel nextComponent nextRest).value.1+formulaSize (grow fuel nextComponent nextRest).value.2)+10 ≤ _
        rw [output]
        simp only [growBudget,roundBudget] at *
        nlinarith

theorem growBudget_mono (fuel fuel' size size' : Nat) (hf : fuel ≤ fuel') (hs : size ≤ size') :
    growBudget fuel size ≤ growBudget fuel' size' := by
  unfold growBudget roundBudget supportBudget partitionBudget
  gcongr

def piecesSize : AffineClauses.Joint.Pieces → Nat
  | [] => 1
  | (source,model)::rest => formulaSize source+storage model+7+piecesSize rest

def sourceClauses : AffineClauses.Joint.Pieces → Nat
  | [] => 0
  | (source,_)::rest => source.length+sourceClauses rest

def sourceRows : AffineClauses.Joint.Pieces → Nat
  | [] => 0
  | (source,_)::rest => rowCount source+sourceRows rest

def sourceTerms : AffineClauses.Joint.Pieces → Nat
  | [] => 0
  | (source,_)::rest => termCount source+sourceTerms rest

def storedCells : AffineClauses.Joint.Pieces → Nat
  | [] => 0
  | (_,model)::rest => model.length+storedCells rest

def modelStorage : AffineClauses.Joint.Pieces → Nat
  | [] => 0
  | (_,model)::rest => storage model+modelStorage rest

def leafBudget (n : Nat) : AffineClauses.Joint.Pieces → Nat
  | [] => 0
  | (source,_)::rest => AffineClauses.JointCost.generateBudget n source+leafBudget n rest

structure Built where
  value : AffineClauses.Joint.Pieces
  preparation : Nat
  grouping : Nat
  copies : Nat
  leafCells : Nat
  sourceCells : Nat
  deriving Repr

def factors (n : Nat) : Nat → Formula → Built
  | _,[] => ⟨[],0,0,1,0,1⟩
  | 0,formula =>
      let model := AffineClauses.JointCost.generate n formula
      let pieces := [(formula,model.value)]
      let copied := 2*piecesSize pieces+5
      ⟨pieces,0,0,copied,model.sourceCells,model.sourceCells+copied⟩
  | fuel+1,clause::rest =>
      let split := grow rest.length [clause] rest
      let model := AffineClauses.JointCost.generate n split.value.1
      let tail := factors n fuel split.value.2
      let pieces := (split.value.1,model.value)::tail.value
      let copied := 2*piecesSize pieces+2*formulaSize (clause::rest)+8
      ⟨pieces,0,split.visits+tail.grouping,tail.copies+copied,
        model.sourceCells+tail.leafCells,split.visits+model.sourceCells+tail.sourceCells+copied⟩

theorem factors_value (n fuel : Nat) (formula : Formula) :
    (factors n fuel formula).value = AffineClauses.Joint.factors n fuel formula := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp only [factors,AffineClauses.Joint.factors,AffineClauses.JointCost.generate_value]
  | succ fuel ih =>
      cases formula <;> simp only [factors,AffineClauses.Joint.factors,ih,grow_value,AffineClauses.JointCost.generate_value]

theorem factors_account (n fuel : Nat) (formula : Formula) :
    (factors n fuel formula).sourceCells = (factors n fuel formula).grouping+
      (factors n fuel formula).copies+(factors n fuel formula).leafCells := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [factors]; omega
  | succ fuel ih =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          have tail := ih (grow rest.length [clause] rest).value.2
          simp only [factors]
          omega

theorem factors_source_counts (n fuel : Nat) (formula : Formula) :
    sourceClauses (factors n fuel formula).value = formula.length ∧
      sourceRows (factors n fuel formula).value = rowCount formula ∧
      sourceTerms (factors n fuel formula).value = termCount formula := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [factors,sourceClauses,sourceRows,sourceTerms]
  | succ fuel ih =>
      cases formula with
      | nil => exact ⟨rfl,rfl,rfl⟩
      | cons clause rest =>
          have tail := ih (grow rest.length [clause] rest).value.2
          have counts := grow_counts rest.length [clause] rest
          simp only [factors,sourceClauses,sourceRows,sourceTerms,tail.1,tail.2.1,tail.2.2]
          simp only [List.length_cons,List.length_nil,AffineClauses.Cost.rowCount_cons,AffineClauses.Cost.rowCount_nil,
            AffineClauses.Cost.termCount_cons,AffineClauses.Cost.termCount_nil] at counts ⊢
          omega

theorem factors_length (n fuel : Nat) (formula : Formula) : (factors n fuel formula).value.length ≤ formula.length := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [factors]
  | succ fuel ih =>
      cases formula with
      | nil => simp [factors]
      | cons clause rest =>
          have tail := ih (grow rest.length [clause] rest).value.2
          have remaining : (grow rest.length [clause] rest).value.2.length ≤ rest.length := by
            rw [grow_value]
            exact AffineClauseProduct.grow_rest_length _ _ _
          simp only [factors,List.length_cons]
          omega

theorem piecesSize_eq (pieces : AffineClauses.Joint.Pieces) : piecesSize pieces =
    modelStorage pieces+sourceTerms pieces+2*sourceRows pieces+sourceClauses pieces+8*pieces.length+1 := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      rcases piece with ⟨source,model⟩
      simp only [piecesSize,modelStorage,sourceTerms,sourceRows,sourceClauses,List.length_cons,formula_size]
      omega

theorem split_sizes (clause : Clause) (rest : Formula) :
    formulaSize (grow rest.length [clause] rest).value.1 ≤ formulaSize (clause::rest) ∧
      formulaSize (grow rest.length [clause] rest).value.2 ≤ formulaSize (clause::rest) := by
  have divided := grow_size rest.length [clause] rest
  have first := size_positive (grow rest.length [clause] rest).value.1
  have second := size_positive (grow rest.length [clause] rest).value.2
  have joined := size_append [clause] rest
  simp only [List.singleton_append] at joined
  omega

theorem split_within (n : Nat) (clause : Clause) (rest : Formula) (inside : Within n (clause::rest)) :
    Within n (grow rest.length [clause] rest).value.1 ∧ Within n (grow rest.length [clause] rest).value.2 := by
  rw [grow_value]
  exact AffineClauseProduct.grow_within n rest.length [clause] rest inside

theorem factors_modelStorage (n fuel : Nat) (formula : Formula) (inside : Within n formula) :
    modelStorage (factors n fuel formula).value ≤
      storedCells (factors n fuel formula).value*AffineCarrier.Cost.cellBound n := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => simp [factors,modelStorage,storedCells]
      | cons clause rest =>
          have valid : AffineCarrier.Valid n (AffineClauses.JointCost.generate n (clause::rest)).value := by
            rw [AffineClauses.JointCost.generate_value]
            exact AffineClauses.Joint.generate_valid n _ inside
          simpa only [factors,modelStorage,storedCells,Nat.add_zero] using AffineCarrier.Cost.storage_bound n _ valid
  | succ fuel ih =>
      cases formula with
      | nil => simp [factors,modelStorage,storedCells]
      | cons clause rest =>
          have bounds := split_within n clause rest inside
          have tail := ih (grow rest.length [clause] rest).value.2 bounds.2
          have valid : AffineCarrier.Valid n (AffineClauses.JointCost.generate n (grow rest.length [clause] rest).value.1).value := by
            rw [AffineClauses.JointCost.generate_value]
            exact AffineClauses.Joint.generate_valid n _ bounds.1
          have first := AffineCarrier.Cost.storage_bound n _ valid
          simp only [factors,modelStorage,storedCells]
          nlinarith

theorem factors_piecesSize (n fuel : Nat) (formula : Formula) (inside : Within n formula) :
    piecesSize (factors n fuel formula).value ≤ formulaSize formula+8*formula.length+
      storedCells (factors n fuel formula).value*AffineCarrier.Cost.cellBound n := by
  have stored := factors_modelStorage n fuel formula inside
  have counts := factors_source_counts n fuel formula
  have parts := factors_length n fuel formula
  have size := piecesSize_eq (factors n fuel formula).value
  rw [counts.1,counts.2.1,counts.2.2] at size
  rw [formula_size]
  omega

theorem factors_leafCells (n fuel : Nat) (formula : Formula) (inside : Within n formula) :
    (factors n fuel formula).leafCells ≤ leafBudget n (factors n fuel formula).value := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          simpa only [factors,leafBudget,Nat.add_zero] using AffineClauses.JointCost.generate_cells n (clause::rest) inside
  | succ fuel ih =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          have bounds := split_within n clause rest inside
          have first := AffineClauses.JointCost.generate_cells n (grow rest.length [clause] rest).value.1 bounds.1
          have tail := ih (grow rest.length [clause] rest).value.2 bounds.2
          simp only [factors,leafBudget]
          omega

theorem factors_grouping (n fuel : Nat) (formula : Formula) (clauses size : Nat)
    (count : formula.length ≤ clauses) (records : formulaSize formula ≤ size) :
    (factors n fuel formula).grouping ≤ formula.length*growBudget clauses (size+1) := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [factors]
  | succ fuel ih =>
      cases formula with
      | nil => simp [factors]
      | cons clause rest =>
          have sizes := split_sizes clause rest
          have remaining : (grow rest.length [clause] rest).value.2.length ≤ rest.length := by
            rw [grow_value]
            exact AffineClauseProduct.grow_rest_length _ _ _
          have tail := ih (grow rest.length [clause] rest).value.2 (by simp only [List.length_cons] at count; omega) (sizes.2.trans records)
          have first := grow_visits rest.length [clause] rest
          have total := size_append [clause] rest
          simp only [List.singleton_append] at total
          have bounded : (grow rest.length [clause] rest).visits ≤ growBudget clauses (size+1) := by
            apply first.trans
            apply growBudget_mono
            · simp only [List.length_cons] at count
              omega
            · omega
          simp only [factors,List.length_cons]
          nlinarith

theorem factors_copies (n fuel : Nat) (formula : Formula) :
    (factors n fuel formula).copies ≤
      (fuel+1)*(2*piecesSize (factors n fuel formula).value+2*formulaSize formula+8)+1 := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [factors,piecesSize]; omega
  | succ fuel ih =>
      cases formula with
      | nil => simp [factors,piecesSize]
      | cons clause rest =>
          let split := (grow rest.length [clause] rest).value
          let tail := factors n fuel split.2
          let pieces := (split.1,(AffineClauses.JointCost.generate n split.1).value)::tail.value
          have first := ih split.2
          have source := (split_sizes clause rest).2
          have pieceBound : piecesSize tail.value ≤ piecesSize pieces := by dsimp only [pieces,piecesSize]; omega
          have bounded : tail.copies ≤ (fuel+1)*(2*piecesSize pieces+2*formulaSize (clause::rest)+8)+1 := by
            apply first.trans
            gcongr
          change tail.copies+(2*piecesSize pieces+2*formulaSize (clause::rest)+8) ≤
            (fuel+1+1)*(2*piecesSize pieces+2*formulaSize (clause::rest)+8)+1
          nlinarith

theorem factors_cells (n fuel : Nat) (formula : Formula) (inside : Within n formula) :
    (factors n fuel formula).sourceCells ≤ leafBudget n (factors n fuel formula).value+
      formula.length*growBudget formula.length (formulaSize formula+1)+
      (fuel+1)*(2*piecesSize (factors n fuel formula).value+2*formulaSize formula+8)+1 := by
  have grouping := factors_grouping n fuel formula formula.length (formulaSize formula) (Nat.le_refl _) (Nat.le_refl _)
  have copied := factors_copies n fuel formula
  have leaf := factors_leafCells n fuel formula inside
  rw [factors_account]
  omega

def emit (n : Nat) (formula : Formula) : Built :=
  let cleaned := AffineClauses.cleanRun formula
  let built := factors n cleaned.value.length cleaned.value
  let copied := 2*(formulaSize formula+formulaSize cleaned.value+piecesSize built.value)+6
  ⟨built.value,cleaned.visits,built.grouping,built.copies+copied,built.leafCells,
    cleaned.visits+built.sourceCells+copied⟩

theorem emit_value (n : Nat) (formula : Formula) : (emit n formula).value = AffineClauses.Joint.emit n formula := by
  simp only [emit,AffineClauses.Joint.emit,factors_value]

theorem emit_account (n : Nat) (formula : Formula) :
    (emit n formula).sourceCells = (emit n formula).preparation+(emit n formula).grouping+
      (emit n formula).copies+(emit n formula).leafCells := by
  have paid := factors_account n (AffineClauses.cleanRun formula).value.length (AffineClauses.cleanRun formula).value
  simp only [emit]
  omega

theorem emit_length (n : Nat) (formula : Formula) : (emit n formula).value.length ≤ formula.length := by
  have count := factors_length n (AffineClauses.clean formula).length (AffineClauses.clean formula)
  have filtered := List.length_filter_le (fun clause => !AffineClauses.tautology clause) formula
  simpa only [emit,AffineClauses.cleanRun_value] using count.trans filtered

def overheadBudget (n clauses size stored : Nat) : Nat :=
  let output := size+8*clauses+stored*AffineCarrier.Cost.cellBound n
  clauses*growBudget clauses (size+1)+
    (clauses+1)*(2*output+2*size+8)+1+4*size+2*output+6

theorem emit_cells (n : Nat) (formula : Formula) (inside : Within n formula) :
    (emit n formula).sourceCells ≤
      AffineClauses.Cost.cleanBudget n formula.length (rowCount formula) (termCount formula)+
      leafBudget n (emit n formula).value+
      overheadBudget n formula.length (formulaSize formula) (storedCells (emit n formula).value) := by
  let cleaned := AffineClauses.clean formula
  have cleanInside := AffineClauses.clean_within n formula inside
  have pre := AffineClauses.Cost.cleanRun_visits n formula inside
  have size := AffineClauses.Cost.clean_size formula
  have count : cleaned.length ≤ formula.length := List.length_filter_le _ _
  have groups := factors_grouping n cleaned.length cleaned formula.length (formulaSize formula) count size
  have copies := factors_copies n cleaned.length cleaned
  have leaves := factors_leafCells n cleaned.length cleaned cleanInside
  have output := factors_piecesSize n cleaned.length cleaned cleanInside
  have outputBound : piecesSize (factors n cleaned.length cleaned).value ≤ formulaSize formula+8*formula.length+
      storedCells (factors n cleaned.length cleaned).value*AffineCarrier.Cost.cellBound n := by
    apply output.trans
    gcongr
  have copyBound : (factors n cleaned.length cleaned).copies ≤
      (formula.length+1)*(2*(formulaSize formula+8*formula.length+
        storedCells (factors n cleaned.length cleaned).value*AffineCarrier.Cost.cellBound n)+2*formulaSize formula+8)+1 := by
    apply copies.trans
    gcongr
  have groupBound : (factors n cleaned.length cleaned).grouping ≤ formula.length*growBudget formula.length (formulaSize formula+1) := by
    apply groups.trans
    gcongr
  have account := factors_account n cleaned.length cleaned
  simp only [emit,AffineClauses.cleanRun_value,overheadBudget]
  dsimp only [cleaned] at *
  nlinarith only [pre,size,outputBound,copyBound,groupBound,leaves,account]

def readPossible : AffineClauses.Joint.Pieces → Counted Bool
  | [] => ⟨true,1⟩
  | piece::rest =>
      let tail := readPossible rest
      ⟨!piece.2.isEmpty && tail.value,tail.visits+4⟩

theorem readPossible_value (pieces : AffineClauses.Joint.Pieces) :
    (readPossible pieces).value = AffineClauses.Joint.possible pieces := by
  induction pieces <;> simp_all [readPossible,AffineClauses.Joint.possible]

theorem readPossible_visits (pieces : AffineClauses.Joint.Pieces) :
    (readPossible pieces).visits = 4*pieces.length+1 := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih => simp only [readPossible,List.length_cons,ih]; omega

def decide (n : Nat) (formula : Formula) : Counted Bool :=
  let generated := emit n formula
  let answer := readPossible generated.value
  ⟨answer.value,generated.sourceCells+answer.visits+1⟩

theorem decide_value (n : Nat) (formula : Formula) :
    (decide n formula).value = AffineClauses.Joint.possible (AffineClauses.Joint.emit n formula) := by
  simp only [decide,readPossible_value,emit_value]

theorem decide_correct (n : Nat) (formula : Formula) (inside : Within n formula) :
    (decide n formula).value = true ↔ AffineClauseProduct.Satisfiable formula := by
  rw [decide_value,AffineClauses.Joint.emit_possible n formula inside]

theorem decide_visits (n : Nat) (formula : Formula) (inside : Within n formula) :
    (decide n formula).visits ≤
      AffineClauses.Cost.cleanBudget n formula.length (rowCount formula) (termCount formula)+
      leafBudget n (emit n formula).value+
      overheadBudget n formula.length (formulaSize formula) (storedCells (emit n formula).value)+4*formula.length+2 := by
  have generated := emit_cells n formula inside
  have count := emit_length n formula
  simp only [decide,readPossible_visits]
  omega

theorem emit_read (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Nat → Bool) :
    AffineClauses.Joint.piecesRead (emit n formula).value assignment = formulaRead formula assignment := by
  rw [emit_value,AffineClauses.Joint.emit_read n formula inside]

theorem emit_image (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Assignment n) :
    (∃ p : AffineClauses.Joint.Parameters n (emit n formula).value,
      AffineClauses.Joint.lift n (emit n formula).value p=assignment) ↔
      formulaRead formula (extendAssignment assignment) = true := by
  rw [emit_value,AffineClauses.Joint.emit_image n formula inside]

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauseProduct.Cost
