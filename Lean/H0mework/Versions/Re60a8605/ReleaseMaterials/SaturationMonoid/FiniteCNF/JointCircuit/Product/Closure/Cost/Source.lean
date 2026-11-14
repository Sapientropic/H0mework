import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Closure.Consumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.AtomFeedbackCostInventory

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductClosureCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open CapacityMatching.RowCost (rowCells rowsCells)
abbrev Counted := ArenaCost.Counted

def coordinate (frame : Frame) (source : Array Row) (i : Nat) : Counted (List Row) :=
  let root := PortEmbedding.ref frame.state frame.ports i
  let found := AffineClauses.Cost.lookup source.toList root.val
  ⟨[found.value],found.cells+16*(frame.ports.size+rowCells found.value+1)+24⟩

theorem coordinate_value (frame : Frame) (source : Array Row) (i : Nat) :
    (coordinate frame source i).value=[source.getD (PortEmbedding.ref frame.state frame.ports i).val Gates.zeroRow] := by
  simp [coordinate,AffineClauses.Cost.lookup_value]

def table (frame : Frame) (keep : Nat) (basis : List Row) : Counted (Array Row) :=
  let source := Table.coordinates frame.state.arena.code.size basis
  let chosen := CapacityMatching.RowCost.gather (fun i : Fin keep => coordinate frame source i.val) (List.finRange keep)
  ⟨chosen.value.toArray,AffineCollect.coordinateWork frame.state.arena.code.size basis+chosen.cells+
    16*(AffineCollect.tableSize source+rowsCells chosen.value+frame.ports.size+keep+1)+24⟩

theorem table_value (frame : Frame) (keep : Nat) (basis : List Row) : (table frame keep basis).value=ProductClosure.table frame keep basis := by
  simp only [table,CapacityMatching.RowCost.gather_value,coordinate_value,ProductCost.singleton_flatMap]
  apply Array.toList_inj.mp
  simp only [ProductClosure.table,Array.toList_ofFn,List.finRange,List.map_ofFn,Function.comp_def]

def project (frame : Frame) (keep : Nat) (basis : List Row) : Counted (List Row) :=
  let source := table frame keep basis
  let image := PortCost.image frame.state.arena.code.size source.value
  ⟨image.value.kernel,source.cells+image.cells+
    16*(AffineCollect.tableSize source.value+AffineForget.Cost.imageSize image.value+rowsCells image.value.kernel+1)+24⟩

theorem project_value (frame : Frame) (keep : Nat) (basis : List Row) :
    (project frame keep basis).value=ProductClosure.project frame keep basis := by
  simp only [project,PortCost.image_value,table_value,ProductClosure.project]

theorem project_holds (frame : Frame) (keep : Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift frame.state point)=true) : holds (project frame keep basis).value (frame.read point)=true := by
  rw [project_value]
  exact ProductClosure.project_holds frame keep basis valid point accepted

theorem coordinate_storage (frame : Frame) (source : Array Row) (n : Nat) (valid : Table.Valid n source) (i : Nat) :
    rowsCells (coordinate frame source i).value ≤ n+2 := by
  rw [coordinate_value]
  have bound := Table.row_length_le n _ (Table.read_valid n source valid (PortEmbedding.ref frame.state frame.ports i).val)
  simp only [CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,rowCells]
  omega

def coordinateBudget (n p : Nat) : Nat := 2*n*(n+2)+3*n+3+16*(p+n+3)+24

theorem coordinate_cells (frame : Frame) (source : Array Row) (n : Nat) (valid : Table.Valid n source)
    (size : source.size=n) (i : Nat) : (coordinate frame source i).cells ≤ coordinateBudget n frame.ports.size := by
  have lookup := AffineClauses.Cost.lookup_cells source.toList (PortEmbedding.ref frame.state frame.ports i).val
  have storage := AffineClauses.Cost.source_storage n source.toList valid
  have output := Table.row_length_le n _ (AffineClauses.Cost.lookup_valid n source.toList valid (PortEmbedding.ref frame.state frame.ports i).val)
  simp only [Array.length_toList,size] at lookup storage
  simp only [coordinate,coordinateBudget,rowCells]
  nlinarith

theorem table_storage (frame : Frame) (keep : Nat) (basis : List Row) :
    AffineCollect.tableSize (table frame keep basis).value ≤ keep*(frame.state.arena.code.size+2)+1 := by
  have stored := Table.rowTerms_bound frame.state.arena.code.size (ProductClosure.table frame keep basis) (ProductClosure.table_valid frame keep basis)
  rw [ProductClosure.table_size] at stored
  rw [table_value,AffineCollect.Cost.table_size,ProductClosure.table_size]
  nlinarith

def tableBudget (n p keep : Nat) : Nat := AffineCollect.Cost.coordinateBudget n+
  keep*(coordinateBudget n p+(keep+1)*(n+2)+5)+1+
    16*(AffineCarrier.Cost.cellBound n+keep*(n+2)+p+keep+1)+24

theorem table_cells (frame : Frame) (keep : Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) :
    (table frame keep basis).cells ≤ tableBudget frame.state.arena.code.size frame.ports.size keep := by
  let source := Table.coordinates frame.state.arena.code.size basis
  have sourceValid : Table.Valid frame.state.arena.code.size source := ConditionalCandidateCost.table_valid _ _
  have size : source.size=frame.state.arena.code.size := Table.coordinates_size _ _
  have first := AffineCollect.Cost.coordinate_visits frame.state.arena.code.size basis valid
  have stored := AffineCollect.Cost.coordinate_size frame.state.arena.code.size basis
  have chosen := CapacityMatching.RowCost.gather_cells (fun i : Fin keep => coordinate frame source i.val) (List.finRange keep)
    (coordinateBudget frame.state.arena.code.size frame.ports.size) (frame.state.arena.code.size+2)
    (fun i _ => coordinate_cells frame source _ sourceValid size i.val)
    (fun i _ => coordinate_storage frame source _ sourceValid i.val)
  have output := table_storage frame keep basis
  simp only [List.length_finRange] at chosen
  simp only [table,AffineCollect.tableSize,List.toList_toArray] at output ⊢
  simp only [AffineCollect.tableSize] at stored
  dsimp only [source] at chosen
  unfold tableBudget
  omega

def projectBudget (n p keep : Nat) : Nat := tableBudget n p keep+PortCost.imageBudget n keep+
  16*(keep*(n+2)+1+(n+keep)*(2*(n+keep)+3)+2+keep*(keep+2)+1)+24

theorem project_cells (frame : Frame) (keep : Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) :
    (project frame keep basis).cells ≤ projectBudget frame.state.arena.code.size frame.ports.size keep := by
  let source := table frame keep basis
  have tableValid : Table.Valid frame.state.arena.code.size source.value := by rw [table_value]; exact ProductClosure.table_valid _ _ _
  have sourceSize : source.value.size=keep := by rw [table_value,ProductClosure.table_size]
  have first := table_cells frame keep basis valid
  have second := PortCost.image_cells frame.state.arena.code.size source.value tableValid
  rw [sourceSize] at second
  have stored := table_storage frame keep basis
  have imageValid := AtomImage.generate_valid frame.state.arena.code.size source.value (fun row member => (tableValid row member).2)
  have count := AtomImage.generate_count source.value
  have imageStored := AffineForget.Cost.imageSize_bound (frame.state.arena.code.size+keep) (AtomImage.generate source.value)
    (PortCost.image_valid_mono _ _ _ _ imageValid (by omega) (by omega)) (by omega)
  rw [← PortCost.image_value frame.state.arena.code.size source.value] at imageStored
  have rowsStored := ProductClosure.project_storage frame keep basis
  rw [← project_value] at rowsStored
  change rowsCells (PortCost.image frame.state.arena.code.size source.value).value.kernel ≤ _ at rowsStored
  change source.cells+(PortCost.image frame.state.arena.code.size source.value).cells+
    16*(AffineCollect.tableSize source.value+AffineForget.Cost.imageSize (PortCost.image frame.state.arena.code.size source.value).value+
      rowsCells (PortCost.image frame.state.arena.code.size source.value).value.kernel+1)+24 ≤ _
  change source.cells ≤ _ at first
  change AffineCollect.tableSize source.value ≤ _ at stored
  unfold projectBudget
  omega

def insert (frame : Frame) (result : Result) (source : List Row) : Counted Result :=
  let mapped := ProductCost.remap frame source
  let generated := EliminateCost.runFrom result mapped.value
  ⟨generated.result,mapped.cells+(generated.cells+1)*
    (16*(AffineCarrier.Cost.cellBound frame.state.arena.code.size+AffineCarrier.resultSize result+rowsCells source+1)+32)+
      16*(rowsCells mapped.value+AffineCarrier.resultSize generated.result+AffineCarrier.resultSize result+1)+32⟩

theorem insert_value (frame : Frame) (result : Result) (source : List Row) :
    (insert frame result source).value=eliminateFrom result (source.map (ProductRows.mapped frame)) := by
  simp only [insert,EliminateCost.runFrom_result,ProductCost.remap_value]

theorem mapped_within (frame : Frame) (source : List Row) :
    RowsWithin frame.state.arena.code.size (ProductCost.remap frame source).value := by
  rw [ProductCost.remap_value]
  intro row member
  obtain ⟨old,_,rfl⟩ := List.mem_map.mp member
  exact ProductRows.mapped_within frame old

theorem insert_valid (frame : Frame) (result : Result) (valid : result.triangular ∧ result.within frame.state.arena.code.size)
    (source : List Row) : (insert frame result source).value.triangular ∧ (insert frame result source).value.within frame.state.arena.code.size := by
  have inside := mapped_within frame source
  rw [ProductCost.remap_value] at inside
  rw [insert_value]
  exact ⟨eliminateFrom_triangular result valid.1 _,eliminateFrom_within _ result valid.2 _ inside⟩

def insertBudget (n p s : Nat) : Nat := ProductCost.remapBudget p s+
  (ProductCost.gaussianBudget n s+1)*(16*(2*AffineCarrier.Cost.cellBound n+s+2)+32)+
    16*(s+2*AffineCarrier.Cost.cellBound n+3)+32

theorem insert_cells (frame : Frame) (result : Result) (valid : result.triangular ∧ result.within frame.state.arena.code.size)
    (source : List Row) : (insert frame result source).cells ≤ insertBudget frame.state.arena.code.size frame.ports.size (rowsCells source) := by
  have first := ProductCost.remap_cells frame source
  have storage := ProductCost.remap_storage frame source
  have count := ProductCost.rows_length (ProductCost.remap frame source).value
  have terms : Gates.rowTerms (ProductCost.remap frame source).value ≤ rowsCells source := by
    have same := AffineCollect.Cost.rows_size (ProductCost.remap frame source).value
    rw [storage] at same
    omega
  have second := EliminateCost.runFrom_cells frame.state.arena.code.size result valid.1 valid.2 _ (mapped_within frame source)
  have work : (EliminateCost.runFrom result (ProductCost.remap frame source).value).cells ≤
      ProductCost.gaussianBudget frame.state.arena.code.size (rowsCells source) := second.trans (by
    unfold ProductCost.gaussianBudget
    gcongr
    omega)
  have before := AffineCarrier.Cost.result_size frame.state.arena.code.size result valid.1 valid.2
  have afterValid := insert_valid frame result valid source
  have after := AffineCarrier.Cost.result_size frame.state.arena.code.size (insert frame result source).value afterValid.1 afterValid.2
  simp only [insert] at after ⊢
  rw [storage]
  unfold insertBudget
  have multiplied := Nat.mul_le_mul (Nat.add_le_add_right work 1)
    (show 16*(AffineCarrier.Cost.cellBound frame.state.arena.code.size+AffineCarrier.resultSize result+rowsCells source+1)+32 ≤
      16*(2*AffineCarrier.Cost.cellBound frame.state.arena.code.size+rowsCells source+2)+32 by omega)
  omega

def step (original expanded : Frame) : Result → Counted Result
  | .contradiction => ⟨.contradiction,32*(original.state.arena.code.size+original.ports.size+original.state.relations.length+
      expanded.state.arena.code.size+expanded.ports.size+expanded.state.relations.length+1)+48⟩
  | .basis basis =>
      let projected := project expanded original.ports.size basis
      let generated := ProductCost.multiplied original projected.value
      let next := insert expanded (.basis basis) generated.value
      ⟨next.value,projected.cells+generated.cells+next.cells+
        32*(original.state.arena.code.size+original.ports.size+original.state.relations.length+
          expanded.state.arena.code.size+expanded.ports.size+expanded.state.relations.length+
            rowsCells projected.value+rowsCells generated.value+AffineCarrier.resultSize (.basis basis)+AffineCarrier.resultSize next.value+1)+48⟩

theorem step_value (original expanded : Frame) (result : Result) :
    (step original expanded result).value=ProductClosure.stepAt original expanded result := by
  cases result <;> simp only [step,project_value,ProductCost.multiplied_value,insert_value,ProductClosure.stepAt]

theorem step_valid (original expanded : Frame) (result : Result)
    (valid : result.triangular ∧ result.within expanded.state.arena.code.size) :
    (step original expanded result).value.triangular ∧ (step original expanded result).value.within expanded.state.arena.code.size := by
  cases result with
  | contradiction => exact ⟨trivial,trivial⟩
  | basis basis => exact insert_valid expanded (.basis basis) valid _

def multipliedSize (p : Nat) : Nat := p*(p*(p+2)+p)
def stepBudget (n p c m q d : Nat) : Nat := projectBudget m q p+ProductCost.multipliedBudget p (p*(p+2))+
  insertBudget m q (multipliedSize p)+32*(n+p+c+m+q+d+p*(p+2)+multipliedSize p+2*(AffineCarrier.Cost.cellBound m+1)+1)+48

theorem step_cells (original expanded : Frame) (result : Result)
    (valid : result.triangular ∧ result.within expanded.state.arena.code.size) :
    (step original expanded result).cells ≤ stepBudget original.state.arena.code.size original.ports.size original.state.relations.length
      expanded.state.arena.code.size expanded.ports.size expanded.state.relations.length := by
  cases result with
  | contradiction => simp only [step,stepBudget]; omega
  | basis basis =>
      have first := project_cells expanded original.ports.size basis valid
      have projected := ProductClosure.project_storage expanded original.ports.size basis
      have count := ProductClosure.project_count expanded original.ports.size basis
      rw [← project_value] at projected count
      have second := ProductCost.multiplied_cells original (project expanded original.ports.size basis).value
      have secondBound := second.trans (show ProductCost.multipliedBudget original.ports.size (rowsCells (project expanded original.ports.size basis).value) ≤
          ProductCost.multipliedBudget original.ports.size (original.ports.size*(original.ports.size+2)) by
        unfold ProductCost.multipliedBudget ProductCost.multiplyPoolBudget ProductCost.multiplyBudget; gcongr)
      have generated := ProductRows.multiplyRows_storage original (project expanded original.ports.size basis).value
      rw [← ProductCost.multiplied_value] at generated
      have generatedBound : rowsCells (ProductCost.multiplied original (project expanded original.ports.size basis).value).value ≤ multipliedSize original.ports.size :=
        generated.trans (by unfold multipliedSize; gcongr)
      have third := insert_cells expanded (.basis basis) valid (ProductCost.multiplied original (project expanded original.ports.size basis).value).value
      have thirdBound := third.trans (show insertBudget expanded.state.arena.code.size expanded.ports.size _ ≤
          insertBudget expanded.state.arena.code.size expanded.ports.size (multipliedSize original.ports.size) by
        unfold insertBudget ProductCost.remapBudget ProductCost.rowBudget ProductCost.refsBudget ProductCost.gaussianBudget; gcongr)
      have before := AffineCarrier.Cost.result_size expanded.state.arena.code.size (.basis basis) valid.1 valid.2
      have afterValid := step_valid original expanded (.basis basis) valid
      have after := AffineCarrier.Cost.result_size expanded.state.arena.code.size (step original expanded (.basis basis)).value afterValid.1 afterValid.2
      simp only [step] at after ⊢
      unfold stepBudget
      omega

def equalRows : List Row → List Row → Counted Bool
  | [],[] => ⟨true,1⟩
  | [],_::_ => ⟨false,1⟩
  | _::_,[] => ⟨false,1⟩
  | left::rest,right::tail =>
      let head := AffineAtomFeedbackCost.equalTerms left.vars right.vars
      let next := equalRows rest tail
      ⟨head.value && (left.rhs==right.rhs) && next.value,head.cells+next.cells+5⟩

theorem equalRows_value (left right : List Row) : (equalRows left right).value=decide (left=right) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons left rest ih =>
      cases right with
      | nil => rfl
      | cons right tail =>
          rcases left with ⟨vars,rhs⟩
          rcases right with ⟨other,bit⟩
          cases rhs <;> cases bit <;> simp [equalRows,AffineAtomFeedbackCost.equalTerms_value,ih]

theorem equalRows_cells (left right : List Row) : (equalRows left right).cells ≤ 6*rowsCells left+1 := by
  induction left generalizing right with
  | nil => cases right <;> simp [equalRows,rowsCells]
  | cons left rest ih =>
      cases right with
      | nil => simp [equalRows,rowsCells]
      | cons right tail =>
          have first := AffineAtomFeedbackCost.equalTerms_cells left.vars right.vars
          have next := ih tail
          simp only [equalRows,CapacityMatching.RowCost.rowsCells_cons,rowCells]
          omega

def equalResult : Result → Result → Counted Bool
  | .basis left,.basis right => let result := equalRows left right; ⟨result.value,result.cells+3⟩
  | .contradiction,.contradiction => ⟨true,2⟩
  | _,_ => ⟨false,2⟩

theorem equalResult_value (left right : Result) : (equalResult left right).value=decide (left=right) := by
  cases left <;> cases right <;> simp [equalResult,equalRows_value]

theorem equalResult_cells (left right : Result) : (equalResult left right).cells ≤ 6*AffineCarrier.resultSize left+4 := by
  cases left with
  | contradiction => cases right <;> simp [equalResult,AffineCarrier.resultSize]
  | basis left =>
      cases right with
      | contradiction => simp [equalResult]
      | basis right =>
          have cost := equalRows_cells left right
          simp only [equalResult,AffineCarrier.resultSize,AffineCarrier.cellSize]
          omega

def context (original expanded : Frame) : Nat := original.state.arena.code.size+original.ports.size+original.state.relations.length+
  expanded.state.arena.code.size+expanded.ports.size+expanded.state.relations.length

def iterate (original expanded : Frame) : Nat → Result → Counted Result
  | 0,result => ⟨result,32*(context original expanded+AffineCarrier.resultSize result+1)+48⟩
  | fuel+1,result =>
      let first := step original expanded result
      let tested := equalResult first.value result
      if tested.value then
        ⟨result,first.cells+tested.cells+32*(context original expanded+AffineCarrier.resultSize result+AffineCarrier.resultSize first.value+1)+48⟩
      else
        let tail := iterate original expanded fuel first.value
        ⟨tail.value,first.cells+tested.cells+tail.cells+
          32*(context original expanded+AffineCarrier.resultSize result+AffineCarrier.resultSize first.value+AffineCarrier.resultSize tail.value+1)+48⟩

theorem iterate_value (original expanded : Frame) (fuel : Nat) (result : Result) :
    (iterate original expanded fuel result).value=ProductClosure.iterateAt original expanded fuel result := by
  induction fuel generalizing result with
  | zero => rfl
  | succ fuel ih => simp only [iterate,equalResult_value,step_value,ih,ProductClosure.iterateAt]; split <;> simp_all

theorem iterate_valid (original expanded : Frame) (fuel : Nat) (result : Result)
    (valid : result.triangular ∧ result.within expanded.state.arena.code.size) :
    (iterate original expanded fuel result).value.triangular ∧ (iterate original expanded fuel result).value.within expanded.state.arena.code.size := by
  induction fuel generalizing result with
  | zero => exact valid
  | succ fuel ih =>
      have next := ih _ (step_valid original expanded result valid)
      simp only [iterate]
      split
      · exact valid
      · exact next

def roundBudget (n p c m q d : Nat) : Nat := stepBudget n p c m q d+6*(AffineCarrier.Cost.cellBound m+1)+4+
  32*(n+p+c+m+q+d+3*(AffineCarrier.Cost.cellBound m+1)+1)+48

theorem iterate_cells (original expanded : Frame) (fuel : Nat) (result : Result)
    (valid : result.triangular ∧ result.within expanded.state.arena.code.size) :
    (iterate original expanded fuel result).cells ≤ (fuel+1)*roundBudget original.state.arena.code.size original.ports.size original.state.relations.length
      expanded.state.arena.code.size expanded.ports.size expanded.state.relations.length := by
  induction fuel generalizing result with
  | zero =>
      have stored := AffineCarrier.Cost.result_size expanded.state.arena.code.size result valid.1 valid.2
      simp only [iterate,context,roundBudget,Nat.zero_add,Nat.one_mul]
      omega
  | succ fuel ih =>
      have first := step_cells original expanded result valid
      have nextValid := step_valid original expanded result valid
      have before := AffineCarrier.Cost.result_size expanded.state.arena.code.size result valid.1 valid.2
      have next := AffineCarrier.Cost.result_size expanded.state.arena.code.size (step original expanded result).value nextValid.1 nextValid.2
      have tested := equalResult_cells (step original expanded result).value result
      have tail := ih _ nextValid
      have tailValid := iterate_valid original expanded fuel (step original expanded result).value nextValid
      have last := AffineCarrier.Cost.result_size expanded.state.arena.code.size (iterate original expanded fuel (step original expanded result).value).value tailValid.1 tailValid.2
      simp only [iterate]
      split
      · have cost : (step original expanded result).cells+(equalResult (step original expanded result).value result).cells+
            32*(context original expanded+AffineCarrier.resultSize result+AffineCarrier.resultSize (step original expanded result).value+1)+48 ≤
              roundBudget original.state.arena.code.size original.ports.size original.state.relations.length
                expanded.state.arena.code.size expanded.ports.size expanded.state.relations.length := by
          unfold context roundBudget
          omega
        exact cost.trans (Nat.le_mul_of_pos_left _ (by omega))
      · simp only [context,roundBudget] at tail ⊢
        nlinarith only [first,before,next,tested,tail,last]

def fromPrepared (original : Frame) (source : ProductRows.Prepared) : Counted Result :=
  let initial := ProductCost.analyze source.frame source.rows
  let generated := iterate original source.frame (source.frame.state.arena.code.size+1) initial.value
  ⟨generated.value,initial.cells+generated.cells+
    32*(context original source.frame+rowsCells source.rows+AffineCarrier.resultSize initial.value+AffineCarrier.resultSize generated.value+1)+48⟩

theorem fromPrepared_value (original : Frame) (source : ProductRows.Prepared) :
    (fromPrepared original source).value=ProductClosure.fromPrepared original source := by
  simp only [fromPrepared,iterate_value,ProductCost.analyze_value,ProductClosure.fromPrepared]

theorem fromPrepared_valid (original : Frame) (source : ProductRows.Prepared) :
    (fromPrepared original source).value.triangular ∧ (fromPrepared original source).value.within source.frame.state.arena.code.size := by
  have initial := ProductRows.analyze_valid source.frame source.rows
  rw [← ProductCost.analyze_value] at initial
  exact iterate_valid original source.frame _ _ initial

def preparedBudget (n p c m q d s : Nat) : Nat := ProductCost.analyzeBudget m q s+(m+2)*roundBudget n p c m q d+
  32*(n+p+c+m+q+d+s+2*(AffineCarrier.Cost.cellBound m+1)+1)+48

theorem fromPrepared_cells (original : Frame) (source : ProductRows.Prepared) :
    (fromPrepared original source).cells ≤ preparedBudget original.state.arena.code.size original.ports.size original.state.relations.length
      source.frame.state.arena.code.size source.frame.ports.size source.frame.state.relations.length (rowsCells source.rows) := by
  have first := ProductCost.analyze_cells source.frame source.rows
  have initialValid := ProductRows.analyze_valid source.frame source.rows
  rw [← ProductCost.analyze_value] at initialValid
  have initial := AffineCarrier.Cost.result_size source.frame.state.arena.code.size (ProductCost.analyze source.frame source.rows).value initialValid.1 initialValid.2
  have generated := iterate_cells original source.frame (source.frame.state.arena.code.size+1) _ initialValid
  have valid := fromPrepared_valid original source
  have stored := AffineCarrier.Cost.result_size source.frame.state.arena.code.size (fromPrepared original source).value valid.1 valid.2
  simp only [fromPrepared] at stored ⊢
  simp only [preparedBudget,context]
  nlinarith only [first,initial,generated,stored]

theorem preparedBudget_mono (n N p P c C m M q Q d D s S : Nat)
    (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) (hm : m ≤ M) (hq : q ≤ Q) (hd : d ≤ D) (hs : s ≤ S) :
    preparedBudget n p c m q d s ≤ preparedBudget N P C M Q D S := by
  simp only [preparedBudget,roundBudget,stepBudget,projectBudget,tableBudget,coordinateBudget,insertBudget,multipliedSize,
    ProductCost.analyzeBudget,ProductCost.gaussianBudget,ProductCost.remapBudget,ProductCost.rowBudget,ProductCost.refsBudget,
    ProductCost.multipliedBudget,ProductCost.multiplyPoolBudget,ProductCost.multiplyBudget,ProductCost.indexBudget,
    ProductCost.pairsBudget,AffineCarrier.Cost.cellBound,EliminateCost.insertCellBudget,EliminateCost.reduceCellBudget,
    PortCost.imageBudget,PortCost.imageVisitsBudget,AffineForget.Cost.imageWorkspace,AtomImage.stepBudget,AffineCollect.Cost.coordinateBudget]
  gcongr

end SaturationMonoid.ComplexityProjection.SATSource.ProductClosureCost
