import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Forget
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.ProductCost

/-!
Paired projection from the same coordinate table and tagged image. Membership,
lookup, erasure and the tagged insertion loop run on the source data. Full-record
copy allowances accompany the paid algebraic visits. These source units do not
include evaluation of counters or identify Nat-address operations with TM steps.
-/

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineForget.Cost

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.SourceCost (Counted)
open CapacityMatching.RowCost (rowCells rowsCells)
open AffineCarrier (Cells Valid cellSize storage resultSize)
open AffineCarrier.Cost (cellBound)

def selectRow (keep : List Nat) (rows : List Row) (i : Nat) : Counted (List Row) :=
  let found := AffineClauseProduct.Cost.member i keep
  if found.value then
    let read := AffineClauses.Cost.lookup rows i
    ⟨[read.value],found.visits+read.cells+2*rowCells read.value+6⟩
  else ⟨[Gates.zeroRow],found.visits+10⟩

theorem selectRow_value (keep : List Nat) (rows : List Row) (i : Nat) :
    (selectRow keep rows i).value = [if i ∈ keep then rows.getD i Gates.zeroRow else Gates.zeroRow] := by
  simp only [selectRow,AffineClauseProduct.Cost.member_value,AffineClauses.Cost.lookup_value]
  split <;> simp_all

theorem selectRow_storage (n : Nat) (keep : List Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid n row) (i : Nat) :
    rowsCells (selectRow keep rows i).value ≤ n+2 := by
  have bounded := Table.row_length_le n _ (AffineClauses.Cost.lookup_valid n rows valid i)
  simp only [selectRow]
  split <;> simp only [CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,rowCells]
  · omega
  · simp [Gates.zeroRow]

def selectBudget (n count : Nat) : Nat := 2*count+2*n*(n+2)+5*n+14

theorem selectRow_cells (n : Nat) (keep : List Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid n row) (size : rows.length=n) (i : Nat) :
    (selectRow keep rows i).cells ≤ selectBudget n keep.length := by
  have found := AffineClauseProduct.Cost.member_visits i keep
  have looked := AffineClauses.Cost.lookup_cells rows i
  have input := AffineClauses.Cost.source_storage n rows valid
  have output := Table.row_length_le n _ (AffineClauses.Cost.lookup_valid n rows valid i)
  rw [size] at looked input
  simp only [selectRow,selectBudget,rowCells]
  split <;> simp only <;> nlinarith

def source (n : Nat) (keep : List Nat) (basis : List Row) : Counted (Array Row) :=
  let coordinates := Table.coordinates n basis
  let rows := coordinates.toList
  let chosen := CapacityMatching.RowCost.gather (fun i : Fin n => selectRow keep rows i.val) (List.finRange n)
  let output := chosen.value.toArray
  ⟨output,AffineCollect.coordinateWork n basis+chosen.cells+
    2*(AffineCollect.tableSize coordinates+AffineCollect.tableSize output+keep.length)+3*n+7⟩

theorem source_value (n : Nat) (keep : List Nat) (basis : List Row) :
    (source n keep basis).value = AffineForget.source n keep basis := by
  simp only [source,CapacityMatching.RowCost.gather_value,selectRow_value]
  have flatten (items : List (Fin n)) :
      items.flatMap (fun i => [if i.val ∈ keep then (Table.coordinates n basis).toList.getD i.val Gates.zeroRow else Gates.zeroRow]) =
        items.map (fun i => if i.val ∈ keep then (Table.coordinates n basis).toList.getD i.val Gates.zeroRow else Gates.zeroRow) := by
    induction items <;> simp_all
  rw [flatten]
  simp [AffineForget.source,List.finRange,Array.ofFn,Function.comp_def]

theorem source_valid (n : Nat) (keep : List Nat) (basis : List Row) :
    Table.Valid n (AffineForget.source n keep basis) := by
  intro row member
  have generated := AffineForget.source_valid n keep basis row member
  refine ⟨generated.1,?_⟩
  intro i present
  exact (generated.2 i present).trans_le (Table.freeWidth_le n basis)

theorem source_inside (n : Nat) (keep : List Nat) (basis : List Row) :
    AtomImage.SourceWithin n (AffineForget.source n keep basis) :=
  fun row member => (source_valid n keep basis row member).2

theorem source_storage (n : Nat) (keep : List Nat) (basis : List Row) :
    AffineCollect.tableSize (AffineForget.source n keep basis) ≤ cellBound n := by
  have terms := Table.rowTerms_bound n _ (source_valid n keep basis)
  rw [AffineForget.source_size] at terms
  rw [AffineCollect.Cost.table_size,AffineForget.source_size]
  unfold cellBound
  nlinarith

def sourceBudget (n count : Nat) : Nat :=
  AffineCollect.Cost.coordinateBudget n+n*(selectBudget n count+(n+1)*(n+2)+5)+1+
    2*(2*cellBound n+count)+3*n+7

theorem source_cells (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (source n keep basis).cells ≤ sourceBudget n keep.length := by
  have coordinates := AffineCollect.Cost.coordinate_visits n basis valid
  have tableValid : Table.Valid n (Table.coordinates n basis) := by
    intro row member
    have generated := Table.coordinates_valid n basis row member
    exact ⟨generated.1,fun i present => (generated.2 i present).trans_le (Table.freeWidth_le n basis)⟩
  have first := AffineCollect.Cost.coordinate_size n basis
  have second := source_storage n keep basis
  have generated := CapacityMatching.RowCost.gather_cells
    (fun i : Fin n => selectRow keep (Table.coordinates n basis).toList i.val) (List.finRange n)
    (selectBudget n keep.length) (n+2)
    (fun i _ => selectRow_cells n keep _ tableValid (by simp) i.val)
    (fun i _ => selectRow_storage n keep _ tableValid i.val)
  simp only [List.length_finRange] at generated
  change AffineCollect.coordinateWork n basis+_+2*(AffineCollect.tableSize (Table.coordinates n basis)+
    AffineCollect.tableSize (source n keep basis).value+keep.length)+3*n+7 ≤ _
  rw [source_value]
  unfold sourceBudget
  nlinarith

def eraseTerms (keep : List Nat) : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | i::rest =>
      let found := AffineClauseProduct.Cost.member i keep
      let tail := eraseTerms keep rest
      ⟨if found.value then i::tail.value else tail.value,
        found.visits+tail.cells+2*tail.value.length+4⟩

theorem eraseTerms_value (keep vars : List Nat) :
    (eraseTerms keep vars).value = vars.filter (fun i => decide (i ∈ keep)) := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      simp only [eraseTerms,AffineClauseProduct.Cost.member_value,ih,List.filter_cons]

theorem eraseTerms_length (keep vars : List Nat) : (eraseTerms keep vars).value.length ≤ vars.length := by
  rw [eraseTerms_value]
  exact List.length_filter_le _ _

theorem eraseTerms_cells (keep vars : List Nat) :
    (eraseTerms keep vars).cells ≤ vars.length*(2*keep.length+2*vars.length+5)+1 := by
  induction vars with
  | nil => simp [eraseTerms]
  | cons i rest ih =>
      have found := AffineClauseProduct.Cost.member_visits i keep
      have copied := eraseTerms_length keep rest
      simp only [eraseTerms,List.length_cons]
      nlinarith

def eraseRow (keep : List Nat) (row : Row) : Counted (List Row) :=
  let vars := eraseTerms keep row.vars
  let output : Row := ⟨vars.value,row.rhs⟩
  ⟨[output],vars.cells+2*(rowCells row+rowCells output)+4⟩

theorem eraseRow_value (keep : List Nat) (row : Row) : (eraseRow keep row).value = [AffineForget.erase keep row] := by
  simp only [eraseRow,eraseTerms_value,AffineForget.erase]

theorem eraseRow_storage (keep : List Nat) (row : Row) : rowsCells (eraseRow keep row).value ≤ rowCells row := by
  have size := eraseTerms_length keep row.vars
  simp only [eraseRow,CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,rowCells]
  omega

def eraseRowBudget (n count : Nat) : Nat := n*(2*count+2*n+5)+1+4*(n+2)+4

theorem eraseRow_cells (n : Nat) (keep : List Nat) (row : Row) (size : row.vars.length ≤ n) :
    (eraseRow keep row).cells ≤ eraseRowBudget n keep.length := by
  have first := eraseTerms_cells keep row.vars
  have output := eraseTerms_length keep row.vars
  have bound : (eraseTerms keep row.vars).cells ≤ n*(2*keep.length+2*n+5)+1 := first.trans (by gcongr)
  simp only [eraseRow,eraseRowBudget,rowCells]
  omega

def eraseRows (keep : List Nat) (rows : List Row) : Counted (List Row) :=
  CapacityMatching.RowCost.gather (eraseRow keep) rows

theorem eraseRows_value (keep : List Nat) (rows : List Row) :
    (eraseRows keep rows).value = rows.map (AffineForget.erase keep) := by
  induction rows <;> simp_all [eraseRows,CapacityMatching.RowCost.gather,CapacityMatching.RowCost.append,eraseRow_value]

theorem eraseRows_storage (keep : List Nat) (rows : List Row) : rowsCells (eraseRows keep rows).value ≤ rowsCells rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      have first := eraseRow_storage keep row
      simp only [eraseRows,CapacityMatching.RowCost.gather,CapacityMatching.RowCost.append,
        CapacityMatching.RowCost.rowsCells_append,CapacityMatching.RowCost.rowsCells_cons] at *
      omega

def eraseBudget (n count : Nat) : Nat := n*(eraseRowBudget n count+(n+1)*(n+2)+5)+1

theorem eraseRows_cells (n : Nat) (keep : List Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid n row) (count : rows.length ≤ n) :
    (eraseRows keep rows).cells ≤ eraseBudget n keep.length := by
  have generated := CapacityMatching.RowCost.gather_cells (eraseRow keep) rows (eraseRowBudget n keep.length) (n+2)
    (fun row member => eraseRow_cells n keep row (Table.row_length_le n row (valid row member)))
    (fun row member => (eraseRow_storage keep row).trans (by
      have bound := Table.row_length_le n row (valid row member)
      unfold rowCells
      omega))
  apply generated.trans
  unfold eraseBudget
  gcongr

def tagSize (row : AtomImage.Tagged) : Nat := row.vars.length+rowCells row.label+1
def tagsSize (rows : List AtomImage.Tagged) : Nat := (rows.map tagSize).sum
def imageSize (image : AtomImage.State) : Nat := tagsSize image.basis+rowsCells image.kernel+2

theorem tagsSize_eq (rows : List AtomImage.Tagged) : tagsSize rows = AtomImage.tagTerms rows+3*rows.length := by
  induction rows <;> simp_all [tagsSize,tagSize,rowCells,AtomImage.tagTerms]
  omega

theorem imageSize_bound (n : Nat) (image : AtomImage.State) (valid : image.Valid n n)
    (count : image.basis.length+image.kernel.length ≤ n) : imageSize image ≤ n*(2*n+3)+2 := by
  have tagged : tagsSize image.basis ≤ image.basis.length*(2*n+3) := by
    have general : ∀ rows : List AtomImage.Tagged, (∀ row ∈ rows, row.Valid n n) →
        tagsSize rows ≤ rows.length*(2*n+3) := by
      intro rows
      induction rows with
      | nil => intro _; simp [tagsSize]
      | cons row rest ih =>
          intro known
          have tail := ih (fun other member => known other (by simp [member]))
          have first := Table.row_length_le n row.coeff (known row (by simp)).1
          have second := Table.row_length_le n row.label (known row (by simp)).2
          change row.vars.length ≤ n at first
          simp only [tagsSize,List.map_cons,List.sum_cons,List.length_cons,tagSize,rowCells] at *
          nlinarith
    exact general image.basis valid.1
  have kernel : rowsCells image.kernel ≤ image.kernel.length*(n+2) :=
    AffineClauses.Cost.source_storage n image.kernel valid.2
  unfold imageSize
  nlinarith

/-- The state and its paid primitive ledger follow the same insertion calls. -/
def imageRun : AtomImage.State → List AtomImage.Tagged → Counted AtomImage.State
  | state,[] => ⟨state,1⟩
  | state,row::rest =>
      let next := AtomImage.insert state row
      let tail := imageRun next rest
      ⟨tail.value,AtomImage.insertVisits state row+tail.cells+1⟩

theorem imageRun_value (state : AtomImage.State) (rows : List AtomImage.Tagged) :
    (imageRun state rows).value = AtomImage.runFrom state rows := by
  induction rows generalizing state <;> simp_all [imageRun,AtomImage.runFrom]

theorem imageRun_cells (state : AtomImage.State) (rows : List AtomImage.Tagged) :
    (imageRun state rows).cells = AtomImage.runVisits state rows := by
  induction rows generalizing state <;> simp_all [imageRun,AtomImage.runVisits]

def imageWorkspace (n : Nat) : Nat := 4*cellBound n+2*n*(2*n+3)+8

def buildImage (n : Nat) (source : Array Row) : Counted AtomImage.State :=
  let tagged := AtomImage.tagged source
  let run := imageRun AtomImage.initial tagged
  ⟨run.value,(run.cells+4*source.size+2)*(8*imageWorkspace n+8)+
    2*(AffineCollect.tableSize source+tagsSize tagged+imageSize run.value)+7⟩

theorem buildImage_value (n : Nat) (source : Array Row) : (buildImage n source).value = AtomImage.generate source := by
  simp only [buildImage,imageRun_value,AtomImage.generate,AtomImage.run]

def imageVisitsBudget (n : Nat) : Nat :=
  (n*n+n)*(4*n+5)+n*(n*AtomImage.stepBudget n n+n+11)+2

def imageBudget (n : Nat) : Nat :=
  (imageVisitsBudget n+1)*(8*imageWorkspace n+8)+
    2*(cellBound n+(n*n+4*n)+(n*(2*n+3)+2))+7

theorem buildImage_cells (n : Nat) (source : Array Row) (valid : Table.Valid n source) (size : source.size=n) :
    (buildImage n source).cells ≤ imageBudget n := by
  have inside : AtomImage.SourceWithin n source := fun row member => (valid row member).2
  have count := AtomImage.generate_count source
  have bounded := AtomImage.generate_valid n source inside
  rw [size] at count bounded
  have stored := imageSize_bound n (AtomImage.generate source) bounded count.le
  have terms := Table.rowTerms_bound n source valid
  rw [size] at terms
  have visits := AtomImage.generateVisits_bound n source inside
  rw [size] at visits
  rw [show 2*(n+n)+5=4*n+5 by omega] at visits
  have visitBound : AtomImage.generateVisits source ≤ imageVisitsBudget n := by
    apply visits.trans
    unfold imageVisitsBudget
    gcongr
  have tagged : tagsSize (AtomImage.tagged source) ≤ n*n+4*n := by
    rw [tagsSize_eq,AtomImage.tagged_terms]
    simp only [AtomImage.tagged,List.length_ofFn,size]
    omega
  have tableBound : AffineCollect.tableSize source ≤ cellBound n := by
    rw [AffineCollect.Cost.table_size,size]
    unfold cellBound
    nlinarith
  change ((imageRun AtomImage.initial (AtomImage.tagged source)).cells+4*source.size+2)*(8*imageWorkspace n+8)+
    2*(AffineCollect.tableSize source+tagsSize (AtomImage.tagged source)+imageSize (buildImage n source).value)+7 ≤ _
  rw [imageRun_cells,buildImage_value]
  have ledger : AtomImage.runVisits AtomImage.initial (AtomImage.tagged source)+4*source.size+2 =
      AtomImage.generateVisits source+1 := by unfold AtomImage.generateVisits; omega
  rw [ledger]
  unfold imageBudget
  gcongr

theorem imagePrefix_size (n : Nat) (source : Array Row) (valid : Table.Valid n source)
    (size : source.size=n) (length : Nat) :
    imageSize (imageRun AtomImage.initial ((AtomImage.tagged source).take length)).value ≤ n*(2*n+3)+2 := by
  have inside := AtomImage.tagged_within n source (fun row member => (valid row member).2)
  rw [size] at inside
  have known := AtomImage.runFrom_valid n n AtomImage.initial (by simp [AtomImage.State.Valid,AtomImage.initial])
    ((AtomImage.tagged source).take length) (fun row member => inside row (List.mem_of_mem_take member))
  have counts := AtomImage.runFrom_count AtomImage.initial ((AtomImage.tagged source).take length)
  have tags : (AtomImage.tagged source).length=n := by simp [AtomImage.tagged,size]
  have prefixLength : ((AtomImage.tagged source).take length).length ≤ n := by
    simp only [List.length_take,tags]
    omega
  simp only [AtomImage.initial,List.length_nil,Nat.zero_add] at counts
  rw [imageRun_value]
  exact imageSize_bound n _ known (by simp only [AtomImage.initial]; omega)

theorem kernel_valid (n : Nat) (keep : List Nat) (basis : List Row) :
    ∀ row ∈ (AtomImage.generate (AffineForget.source n keep basis)).kernel, Table.RowValid n row := by
  have generated := (AtomImage.generate_valid n _ (source_inside n keep basis)).2
  simpa only [AffineForget.source_size] using generated

theorem kernel_length (n : Nat) (keep : List Nat) (basis : List Row) :
    (AtomImage.generate (AffineForget.source n keep basis)).kernel.length ≤ n := by
  have count := AtomImage.generate_count (AffineForget.source n keep basis)
  rw [AffineForget.source_size] at count
  omega

theorem kernel_storage (n : Nat) (keep : List Nat) (basis : List Row) :
    rowsCells (AtomImage.generate (AffineForget.source n keep basis)).kernel ≤ n*(n+2) :=
  (AffineClauses.Cost.source_storage n _ (kernel_valid n keep basis)).trans (by gcongr; exact kernel_length n keep basis)

theorem erased_inside (n : Nat) (keep : List Nat) (basis : List Row) :
    RowsWithin n (eraseRows keep (AtomImage.generate (AffineForget.source n keep basis)).kernel).value := by
  rw [eraseRows_value]
  intro row member
  obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
  exact AffineForget.erase_within n keep old (kernel_valid n keep basis old present).2

def gaussianBudget (n : Nat) : Nat := n*(n+2)*(2*n+5)+n*(EliminateCost.insertCellBudget n+1)+1

theorem gaussian_cells (n : Nat) (keep : List Nat) (basis : List Row) :
    (EliminateCost.run (eraseRows keep (AtomImage.generate (AffineForget.source n keep basis)).kernel).value).cells ≤ gaussianBudget n := by
  have bounded := EliminateCost.run_cells n _ (erased_inside n keep basis)
  have stored := (eraseRows_storage keep _).trans (kernel_storage n keep basis)
  have terms : Gates.rowTerms (eraseRows keep (AtomImage.generate (AffineForget.source n keep basis)).kernel).value ≤ n*(n+2) := by
    rw [AffineCollect.Cost.rows_size] at stored
    omega
  have count : (eraseRows keep (AtomImage.generate (AffineForget.source n keep basis)).kernel).value.length ≤ n := by
    rw [eraseRows_value,List.length_map]
    exact kernel_length n keep basis
  apply bounded.trans
  unfold gaussianBudget
  gcongr

def modelSize (model : AffineForget.Model) : Nat :=
  cellSize model.basis+model.keep.length+AffineCollect.tableSize model.table+imageSize model.image+resultSize model.value+7

def modelBudget (n count : Nat) : Nat := 3*cellBound n+count+n*(2*n+3)+10

theorem generated_modelSize (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    modelSize (AffineForget.generate n keep basis) ≤ modelBudget n keep.length := by
  have first := AffineCarrier.Cost.cell_size n basis valid.1 valid.2
  have table := source_storage n keep basis
  have imageValid := AtomImage.generate_valid n _ (source_inside n keep basis)
  rw [AffineForget.source_size] at imageValid
  have count := AtomImage.generate_count (AffineForget.source n keep basis)
  rw [AffineForget.source_size] at count
  have image := imageSize_bound n _ imageValid count.le
  have generated := AffineForget.generate_valid n keep basis
  have result := AffineCarrier.Cost.result_size n _ generated.1 generated.2
  simp only [modelSize,AffineForget.generate,modelBudget] at *
  omega

structure Generated where
  value : AffineForget.Model
  cells : Nat
  deriving Repr

def generate (n : Nat) (keep : List Nat) (basis : List Row) : Generated :=
  let table := source n keep basis
  let image := buildImage n table.value
  let erased := eraseRows keep image.value.kernel
  let projected := EliminateCost.run erased.value
  let model : AffineForget.Model := ⟨basis,keep,table.value,image.value,projected.result⟩
  ⟨model,table.cells+image.cells+erased.cells+(projected.cells+1)*(8*cellBound n+8)+
    2*(modelSize model+rowsCells erased.value)+11⟩

theorem generate_value (n : Nat) (keep : List Nat) (basis : List Row) :
    (generate n keep basis).value = AffineForget.generate n keep basis := by
  simp only [generate,source_value,buildImage_value,eraseRows_value,AffineForget.generate]

def generateBudget (n count : Nat) : Nat :=
  sourceBudget n count+imageBudget n+eraseBudget n count+(gaussianBudget n+1)*(8*cellBound n+8)+
    2*(modelBudget n count+n*(n+2))+11

theorem generate_cells (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (generate n keep basis).cells ≤ generateBudget n keep.length := by
  have table := source_cells n keep basis valid
  have image := buildImage_cells n (AffineForget.source n keep basis) (source_valid n keep basis) (AffineForget.source_size n keep basis)
  have erased := eraseRows_cells n keep (AtomImage.generate (AffineForget.source n keep basis)).kernel
    (kernel_valid n keep basis) (kernel_length n keep basis)
  have gaussian := gaussian_cells n keep basis
  have output := generated_modelSize n keep basis valid
  have stored := (eraseRows_storage keep _).trans (kernel_storage n keep basis)
  change (source n keep basis).cells+(buildImage n (source n keep basis).value).cells+
    (eraseRows keep (buildImage n (source n keep basis).value).value.kernel).cells+
    ((EliminateCost.run (eraseRows keep (buildImage n (source n keep basis).value).value.kernel).value).cells+1)*(8*cellBound n+8)+
      2*(modelSize (generate n keep basis).value+rowsCells (eraseRows keep (buildImage n (source n keep basis).value).value.kernel).value)+11 ≤ _
  rw [source_value,buildImage_value,generate_value]
  unfold generateBudget
  gcongr

def cells (n : Nat) (keep : List Nat) : Cells → AffineProduct.Cost.Counted Cells
  | [] => ⟨[],1⟩
  | basis::rest =>
      let model := generate n keep basis
      let packed := AffineCarrier.pack model.value.value
      let tail := cells n keep rest
      let joined := AffineCarrier.append packed ⟨tail.value,0,0,tail.visits⟩
      ⟨joined.value,model.cells+joined.visits+
        2*(modelSize model.value+cellSize basis)+5⟩

theorem cells_value (n : Nat) (keep : List Nat) (original : Cells) :
    (cells n keep original).value = AffineForget.cells n keep original := by
  induction original with
  | nil => rfl
  | cons basis rest ih =>
      simp only [cells,generate_value,AffineCarrier.append,AffineForget.cells,List.flatMap_cons,ih]

theorem cells_valid (n : Nat) (keep : List Nat) (original : Cells) : Valid n (cells n keep original).value := by
  rw [cells_value]
  exact AffineForget.cells_valid n keep original

theorem cells_length (n : Nat) (keep : List Nat) (original : Cells) : (cells n keep original).value.length ≤ original.length := by
  rw [cells_value]
  exact AffineForget.cells_length n keep original

def cellsBudget (n count quantity : Nat) : Nat :=
  quantity*(generateBudget n count+2*modelBudget n count+(2*quantity+8)*cellBound n+17)+1

theorem cells_visits (n : Nat) (keep : List Nat) (original : Cells) (valid : Valid n original) :
    (cells n keep original).visits ≤ cellsBudget n keep.length original.length := by
  induction original with
  | nil => simp [cells,cellsBudget]
  | cons basis rest ih =>
      have input := valid basis (by simp)
      have restValid : Valid n rest := fun b member => valid b (by simp [member])
      have head := generate_cells n keep basis input
      have copied := generated_modelSize n keep basis input
      have basisStored := AffineCarrier.Cost.cell_size n basis input.1 input.2
      have generated := AffineForget.generate_valid n keep basis
      have packedCost := AffineCarrier.Cost.pack_visits n _ generated.1 generated.2
      have packedValid := AffineCarrier.pack_valid n _ generated.1 generated.2
      have packedLength := AffineCarrier.Cost.pack_length (AffineForget.generate n keep basis).value
      have packedStorage := (AffineCarrier.Cost.storage_bound n _ packedValid).trans
        (Nat.mul_le_mul_right (cellBound n) packedLength)
      have tail := ih restValid
      have tailStorage := (AffineCarrier.Cost.storage_bound n _ (cells_valid n keep rest)).trans
        (Nat.mul_le_mul_right (cellBound n) (cells_length n keep rest))
      simp only [Nat.one_mul] at packedStorage
      simp only [cells,generate_value,AffineCarrier.append,cellsBudget,List.length_cons] at *
      nlinarith

theorem generate_image (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (assignment : Assignment n) :
    (generate n keep basis).value.value.holds (extendAssignment assignment)=true ↔
      ∃ original : Assignment n, holds basis (extendAssignment original)=true ∧
        ∀ i : Fin n, i.val ∈ keep → original i=assignment i := by
  rw [generate_value]
  exact AffineForget.generate_image n keep basis valid assignment

theorem fibre_image (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (after : Assignment n)
    (accepted : (generate n keep basis).value.value.holds (extendAssignment after)=true) (before : Assignment n) :
    (∃ p : AffineForget.FibreParameters n (generate n keep basis).value after,
      AffineForget.fibreLift n (generate n keep basis).value after p=before) ↔
      holds basis (extendAssignment before)=true ∧ ∀ i : Fin n, i.val ∈ keep → before i=after i := by
  rw [generate_value] at accepted ⊢
  exact AffineForget.fibreLift_image n keep basis valid after accepted before

theorem cells_future (n : Nat) (formula : AffineClauses.Formula) (inside : AffineClauses.Within n formula)
    (original : Cells) (valid : Valid n original) :
    (∃ x : Assignment n, AffineCarrier.read (cells n (AffineClauseProduct.support formula) original).value (extendAssignment x)=true ∧
      AffineClauses.formulaRead formula (extendAssignment x)=true) ↔
    ∃ x : Assignment n, AffineCarrier.read original (extendAssignment x)=true ∧
      AffineClauses.formulaRead formula (extendAssignment x)=true := by
  rw [cells_value]
  exact AffineForget.cells_row_future n formula inside original valid

end SaturationMonoid.ComplexityProjection.SATSource.AffineForget.Cost
