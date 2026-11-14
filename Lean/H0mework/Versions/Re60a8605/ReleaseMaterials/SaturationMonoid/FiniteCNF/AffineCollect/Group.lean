import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Joint

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineGroupCover
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Valid Separated read storage cellSize resultSize)

structure Check where
  apart : Bool
  calls : Nat
  cells : Nat
  deriving Repr

def pair (left right : List Row) : Check :=
  let joint := EliminateCost.runFrom (.basis left) right
  ⟨match joint.result with | .contradiction => true | .basis _ => false,
    1,joint.cells+2*(cellSize left+cellSize right+resultSize joint.result)+5⟩

theorem pair_iff (left right : List Row) (valid : Triangular left) :
    (pair left right).apart=true ↔ ∀ assignment : Nat → Bool,
      (holds left assignment && holds right assignment)=false := by
  have equation (assignment : Nat → Bool) := eliminateFrom_holds (.basis left) right assignment
  rw [← EliminateCost.runFrom_result] at equation
  cases result : (EliminateCost.runFrom (.basis left) right).result with
  | contradiction =>
      simp only [pair,result,true_iff]
      intro assignment
      simpa only [result,Result.holds] using (equation assignment).symm
  | basis basis =>
      have triangular : Triangular basis := by
        have generated := eliminateFrom_triangular (.basis left) valid right
        rwa [← EliminateCost.runFrom_result,result] at generated
      simp only [pair,result,Bool.false_eq_true,false_iff]
      intro separated
      have realized := fill_holds basis triangular (fun _ => false)
      have same := equation (fill basis (fun _ => false))
      rw [result] at same
      change holds basis (fill basis (fun _ => false)) =
        (holds left (fill basis (fun _ => false)) && holds right (fill basis (fun _ => false))) at same
      rw [realized,separated] at same
      cases same

def against (left : List Row) : Cells → Check
  | [] => ⟨true,0,1⟩
  | right::rest =>
      let first := pair left right
      if first.apart then
        let tail := against left rest
        ⟨tail.apart,first.calls+tail.calls,first.cells+tail.cells+2⟩
      else ⟨false,first.calls,first.cells+2⟩

theorem against_iff (left : List Row) (valid : Triangular left) (group : Cells) :
    (against left group).apart=true ↔ ∀ right ∈ group, ∀ assignment : Nat → Bool,
      (holds left assignment && holds right assignment)=false := by
  induction group with
  | nil => simp [against]
  | cons right rest ih =>
      simp only [against]
      split
      · rename_i accepted
        simp only [ih,List.forall_mem_cons]
        exact (and_iff_right ((pair_iff left right valid).mp accepted)).symm
      · rename_i rejected
        simp only [Bool.false_eq_true,List.forall_mem_cons,false_iff]
        intro facts
        exact rejected ((pair_iff left right valid).mpr facts.1)

def groupStorage (groups : List Cells) : Nat := (groups.map (fun group => storage group+1)).sum

structure Grouping where
  value : List Cells
  checks : Nat
  cells : Nat
  deriving Repr

def insert (left : List Row) : List Cells → Grouping
  | [] => ⟨[[left]],0,2*cellSize left+7⟩
  | group::rest =>
      let tested := against left group
      if tested.apart then
        ⟨(left::group)::rest,tested.calls,
          tested.cells+2*(cellSize left+groupStorage (group::rest))+9⟩
      else
        let tail := insert left rest
        ⟨group::tail.value,tested.calls+tail.checks,
          tested.cells+tail.cells+2*(storage group+groupStorage tail.value)+9⟩

theorem insert_members (left basis : List Row) (groups : List Cells) :
    basis ∈ (insert left groups).value.flatten ↔ basis=left ∨ basis ∈ groups.flatten := by
  induction groups with
  | nil => simp [insert]
  | cons group rest ih =>
      simp only [insert]
      split <;> simp only [List.flatten_cons,List.mem_append,List.mem_cons,ih]
      · tauto
      · tauto

theorem insert_count (left : List Row) (groups : List Cells) :
    (insert left groups).value.flatten.length=groups.flatten.length+1 := by
  induction groups with
  | nil => simp [insert]
  | cons group rest ih =>
      simp only [insert]
      split <;> simp only [List.flatten_cons,List.length_append,List.length_cons,ih] <;> omega

theorem insert_length (left : List Row) (groups : List Cells) :
    (insert left groups).value.length ≤ groups.length+1 := by
  induction groups with
  | nil => simp [insert]
  | cons group rest ih =>
      simp only [insert]
      split <;> simp only [List.length_cons] <;> omega

theorem insert_separated (left : List Row) (groups : List Cells) (valid : Triangular left)
    (separated : ∀ group ∈ groups, Separated group) :
    ∀ group ∈ (insert left groups).value, Separated group := by
  induction groups with
  | nil => simp [insert,Separated]
  | cons group rest ih =>
      have first := separated group (by simp)
      have tail := ih (fun g member => separated g (by simp [member]))
      simp only [insert]
      split
      · rename_i accepted
        intro g member
        rcases List.mem_cons.mp member with rfl | member
        · exact List.pairwise_cons.mpr ⟨(against_iff left valid group).mp accepted,first⟩
        · exact separated g (by simp [member])
      · intro g member
        rcases List.mem_cons.mp member with rfl | member
        · exact first
        · exact tail g member

def partition : Cells → Grouping
  | [] => ⟨[],0,1⟩
  | basis::rest =>
      let tail := partition rest
      let placed := insert basis tail.value
      ⟨placed.value,tail.checks+placed.checks,
        tail.cells+placed.cells+2*(groupStorage tail.value+groupStorage placed.value)+5⟩

theorem partition_members (cells : Cells) (basis : List Row) :
    basis ∈ (partition cells).value.flatten ↔ basis ∈ cells := by
  induction cells with
  | nil => rfl
  | cons first rest ih => simp only [partition,insert_members,ih,List.mem_cons]

theorem partition_count (cells : Cells) : (partition cells).value.flatten.length=cells.length := by
  induction cells with
  | nil => rfl
  | cons first rest ih => simp only [partition,insert_count,ih,List.length_cons]

theorem partition_length (cells : Cells) : (partition cells).value.length ≤ cells.length := by
  induction cells with
  | nil => rfl
  | cons first rest ih => exact (insert_length first _).trans (Nat.add_le_add_right ih 1)

theorem partition_valid (n : Nat) (cells : Cells) (valid : Valid n cells) :
    Valid n (partition cells).value.flatten :=
  fun basis member => valid basis ((partition_members cells basis).mp member)

theorem partition_separated (n : Nat) (cells : Cells) (valid : Valid n cells) :
    ∀ group ∈ (partition cells).value, Separated group := by
  induction cells with
  | nil => simp [partition]
  | cons first rest ih =>
      exact insert_separated first _ (valid first (by simp)).1
        (ih (fun basis member => valid basis (by simp [member])))

theorem partition_read (cells : Cells) (assignment : Nat → Bool) :
    read (partition cells).value.flatten assignment=read cells assignment := by
  apply Bool.eq_iff_iff.mpr
  simp only [AffineCarrier.read,List.any_eq_true,partition_members]

def compress (n : Nat) : List Cells → AffineJointCover.Cost.Compression
  | [] => ⟨[],0,0,1⟩
  | group::rest =>
      let first := AffineJointCover.Cost.compact n group
      let tail := compress n rest
      ⟨first.value++tail.value,first.machineSteps+tail.machineSteps,
        max first.maxInput tail.maxInput,
        first.cells+tail.cells+2*(storage first.value+storage tail.value)+5⟩

theorem compress_valid (n : Nat) (groups : List Cells) (valid : Valid n groups.flatten) :
    Valid n (compress n groups).value := by
  induction groups with
  | nil => simp [compress,Valid]
  | cons group rest ih =>
      exact AffineCarrier.valid_append _ _ (AffineJointCover.Cost.compact_valid n group
        (fun basis member => valid basis (by simp [member])))
        (ih (fun basis member => valid basis (by simp [member])))

theorem compress_read (n : Nat) (groups : List Cells) (valid : Valid n groups.flatten)
    (separated : ∀ group ∈ groups, Separated group) (assignment : Assignment n) :
    read (compress n groups).value (extendAssignment assignment) =
      read groups.flatten (extendAssignment assignment) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      have first := AffineJointCover.Cost.compact_read n group
        (fun basis member => valid basis (by simp [member])) (separated group (by simp)) assignment
      have tail := ih (fun basis member => valid basis (by simp [member]))
        (fun g member => separated g (by simp [member]))
      simp only [compress,AffineCarrier.read_append,List.flatten_cons,first,tail]

def compact (n : Nat) (cells : Cells) : AffineJointCover.Cost.Compression :=
  let groups := partition cells
  let compressed := compress n groups.value
  let collected := AffineCollect.collect n compressed.value
  ⟨collected.value,compressed.machineSteps,compressed.maxInput,
    groups.cells+compressed.cells+collected.visits+
      2*(groupStorage groups.value+storage compressed.value+storage collected.value)+7⟩

theorem compact_valid (n : Nat) (cells : Cells) (valid : Valid n cells) : Valid n (compact n cells).value :=
  AffineCollect.collect_valid n _ (compress_valid n _ (partition_valid n cells valid))

theorem compact_read (n : Nat) (cells : Cells) (valid : Valid n cells) (assignment : Nat → Bool) :
    read (compact n cells).value assignment=read cells assignment := by
  have generated := partition_valid n cells valid
  have compressed := compress_valid n _ generated
  have same := compress_read n _ generated (partition_separated n cells valid) (fun i => assignment i.val)
  rw [AffineClauses.Joint.read_restrict n _ compressed,
    AffineClauses.Joint.read_restrict n _ generated,partition_read] at same
  simp only [compact,AffineCollect.collect_read n _ compressed,same]



open AffineCarrier.Cost (cellBound)

def pairBudget (n : Nat) : Nat :=
  n*n*(2*n+5)+n*(EliminateCost.insertCellBudget n+1)+6*cellBound n+8

theorem pair_cells (n : Nat) (left right : List Row)
    (first : Triangular left ∧ RowsWithin n left) (second : Triangular right ∧ RowsWithin n right) :
    (pair left right).cells ≤ pairBudget n := by
  have actual := EliminateCost.runFrom_cells n (.basis left) first.1 first.2 right second.2
  have rows := basis_length_le n right second.1 second.2
  have terms := Table.rowTerms_bound n right.toArray
    (fun row member => ⟨second.1.1 row member,second.2 row member⟩)
  simp only [List.size_toArray] at terms
  have leftSize := AffineCarrier.Cost.cell_size n left first.1 first.2
  have rightSize := AffineCarrier.Cost.cell_size n right second.1 second.2
  have generated : (EliminateCost.runFrom (.basis left) right).result.triangular ∧
      (EliminateCost.runFrom (.basis left) right).result.within n := by
    rw [EliminateCost.runFrom_result]
    exact ⟨eliminateFrom_triangular (.basis left) first.1 _,eliminateFrom_within n (.basis left) first.2 _ second.2⟩
  have resultSizeBound := AffineCarrier.Cost.result_size n _ generated.1 generated.2
  have termBound : Gates.rowTerms right ≤ n*n := terms.trans (Nat.mul_le_mul_right n rows)
  simp only [pair,pairBudget]
  nlinarith

theorem against_calls (left : List Row) (group : Cells) : (against left group).calls ≤ group.length := by
  induction group with
  | nil => simp [against]
  | cons right rest ih =>
      simp only [against,List.length_cons]
      split <;> simp only [pair] <;> omega

theorem against_cells (n : Nat) (left : List Row) (group : Cells)
    (first : Triangular left ∧ RowsWithin n left) (valid : Valid n group) :
    (against left group).cells ≤ group.length*(pairBudget n+2)+1 := by
  induction group with
  | nil => simp [against]
  | cons right rest ih =>
      have pairCost := pair_cells n left right first (valid right (by simp))
      have tail := ih (fun basis member => valid basis (by simp [member]))
      simp only [against,List.length_cons]
      split <;> simp only <;> nlinarith

theorem insert_checks (left : List Row) (groups : List Cells) :
    (insert left groups).checks ≤ groups.flatten.length := by
  induction groups with
  | nil => simp [insert]
  | cons group rest ih =>
      have first := against_calls left group
      simp only [insert]
      split <;> simp only [List.flatten_cons,List.length_append] <;> omega

theorem partition_checks (cells : Cells) : (partition cells).checks ≤ cells.length*cells.length := by
  induction cells with
  | nil => simp [partition]
  | cons first rest ih =>
      have added := insert_checks first (partition rest).value
      rw [partition_count] at added
      simp only [partition,List.length_cons]
      nlinarith

theorem groupStorage_cons (group : Cells) (rest : List Cells) :
    groupStorage (group::rest)=storage group+1+groupStorage rest := rfl

theorem insert_storage (left : List Row) (groups : List Cells) :
    groupStorage (insert left groups).value ≤ groupStorage groups+cellSize left+1 := by
  induction groups with
  | nil => simp [insert,groupStorage,storage]
  | cons group rest ih =>
      simp only [insert]
      split <;> simp only [groupStorage_cons,storage,List.map_cons,List.sum_cons] at * <;> omega

theorem group_storage_bound (n : Nat) (groups : List Cells) (valid : Valid n groups.flatten) :
    groupStorage groups ≤ groups.flatten.length*cellBound n+groups.length := by
  induction groups with
  | nil => simp [groupStorage]
  | cons group rest ih =>
      have first := AffineCarrier.Cost.storage_bound n group (fun basis member => valid basis (by simp [member]))
      have tail := ih (fun basis member => valid basis (by simp [member]))
      simp only [groupStorage_cons,List.flatten_cons,List.length_append,List.length_cons]
      nlinarith

theorem partition_storage (n : Nat) (cells : Cells) (valid : Valid n cells) :
    groupStorage (partition cells).value ≤ cells.length*(cellBound n+1) := by
  have stored := group_storage_bound n _ (partition_valid n cells valid)
  have count := partition_length cells
  rw [partition_count] at stored
  nlinarith

def insertRound (n count : Nat) : Nat :=
  count*(pairBudget n+2)+1+8*(count+1)*(cellBound n+1)+16

def insertBudget (n count : Nat) : Nat := count*insertRound n count+2*cellBound n+7

theorem insert_cells (n count : Nat) (left : List Row) (first : Triangular left ∧ RowsWithin n left)
    (groups : List Cells) (valid : Valid n groups.flatten) (size : groups.flatten.length ≤ count)
    (number : groups.length ≤ count) :
    (insert left groups).cells ≤ groups.length*insertRound n count+2*cellBound n+7 := by
  have leftSize := AffineCarrier.Cost.cell_size n left first.1 first.2
  induction groups with
  | nil => simp only [insert,List.length_nil,Nat.zero_mul,Nat.zero_add]; omega
  | cons group rest ih =>
      have groupValid : Valid n group := fun basis member => valid basis (by simp [member])
      have restValid : Valid n rest.flatten := fun basis member => valid basis (by simp [member])
      have sizes : group.length+rest.flatten.length ≤ count := by simpa only [List.flatten_cons,List.length_append] using size
      have numbers : rest.length+1 ≤ count := number
      have tail := ih restValid (by omega) (by omega)
      have checked := against_cells n left group first groupValid
      have groupSize := AffineCarrier.Cost.storage_bound n group groupValid
      have oldStorage := group_storage_bound n (group::rest) valid
      have restStorage := group_storage_bound n rest restValid
      have newStorage := insert_storage left rest
      simp only [List.flatten_cons,List.length_append,List.length_cons] at oldStorage
      simp only [insert]
      split <;> simp only [List.length_cons,insertRound] at * <;> nlinarith

def partitionRound (n count : Nat) : Nat := insertBudget n count+4*(count+1)*(cellBound n+1)+5

theorem partition_cells_bound (n count : Nat) (cells : Cells) (valid : Valid n cells) (size : cells.length ≤ count) :
    (partition cells).cells ≤ cells.length*partitionRound n count+1 := by
  induction cells with
  | nil => simp [partition]
  | cons first rest ih =>
      have restValid : Valid n rest := fun basis member => valid basis (by simp [member])
      have firstValid := valid first (by simp)
      have tail := ih restValid (by simp only [List.length_cons] at size; omega)
      have oldStorage := partition_storage n rest restValid
      have added := insert_storage first (partition rest).value
      have firstSize := AffineCarrier.Cost.cell_size n first firstValid.1 firstValid.2
      have num := partition_length rest
      have countExact := partition_count rest
      have inserting := insert_cells n count first firstValid (partition rest).value
        (partition_valid n rest restValid) (by rw [countExact]; simp only [List.length_cons] at size; omega)
        (by simp only [List.length_cons] at size; omega)
      have numBound : (partition rest).value.length ≤ count := by simp only [List.length_cons] at size; omega
      have insertBound : (insert first (partition rest).value).cells ≤ insertBudget n count := by
        apply inserting.trans
        unfold insertBudget
        gcongr
      simp only [partition,List.length_cons,partitionRound] at *
      nlinarith

theorem compact_length (n : Nat) (cells : Cells) : (AffineJointCover.Cost.compact n cells).value.length ≤ cells.length := by
  rw [AffineJointCover.Cost.compact_value]
  cases cells with
  | nil => simp [AffineJointCover.compact,AffineJointCover.hull]
  | cons first rest =>
      cases generated : AffineJointCover.hull n (first::rest) with
      | contradiction => simp [AffineJointCover.compact,generated]
      | basis basis =>
          simp only [AffineJointCover.compact,generated]
          split <;> simp

theorem compress_length (n : Nat) (groups : List Cells) : (compress n groups).value.length ≤ groups.flatten.length := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      have first := compact_length n group
      simp only [compress,List.length_append,List.flatten_cons]
      omega

theorem compact_count (n : Nat) (cells : Cells) (valid : Valid n cells) : (compact n cells).value.length ≤ cells.length := by
  have collected := AffineCollect.collect_length n (compress n (partition cells).value).value
    (compress_valid n _ (partition_valid n cells valid))
  have compressed := compress_length n (partition cells).value
  rw [partition_count] at compressed
  exact collected.trans compressed



def compressionRound (n count : Nat) : Nat := AffineJointCover.Cost.compactBudget n count+4*count*cellBound n+5

theorem compactBudget_mono (n small large : Nat) (bound : small ≤ large) :
    AffineJointCover.Cost.compactBudget n small ≤ AffineJointCover.Cost.compactBudget n large := by
  unfold AffineJointCover.Cost.compactBudget AffineJointCover.Cost.hullBudget AffineJointCover.Cost.volumeBudget
  gcongr

theorem compress_cells (n count : Nat) (groups : List Cells) (valid : Valid n groups.flatten)
    (size : groups.flatten.length ≤ count) :
    (compress n groups).cells ≤ groups.length*compressionRound n count+1 := by
  induction groups with
  | nil => simp [compress]
  | cons group rest ih =>
      have groupValid : Valid n group := fun basis member => valid basis (by simp [member])
      have restValid : Valid n rest.flatten := fun basis member => valid basis (by simp [member])
      have sizes : group.length+rest.flatten.length ≤ count := by simpa only [List.flatten_cons,List.length_append] using size
      have tail := ih restValid (by omega)
      have first := (AffineJointCover.Cost.compact_cells n group groupValid).trans
        (compactBudget_mono n group.length count (by omega))
      have firstStorage := AffineCarrier.Cost.storage_bound n _ (AffineJointCover.Cost.compact_valid n group groupValid)
      have tailStorage := AffineCarrier.Cost.storage_bound n _ (compress_valid n rest restValid)
      have firstCount := compact_length n group
      have tailCount := compress_length n rest
      simp only [compress,List.length_cons,compressionRound] at *
      nlinarith

theorem microBudget_mono (n small large : Nat) (bound : small ≤ large) :
    AffineJointCover.Cost.microBudget n small ≤ AffineJointCover.Cost.microBudget n large := by
  unfold AffineJointCover.Cost.microBudget
  gcongr

theorem compress_machineSteps (n count : Nat) (groups : List Cells) (size : groups.flatten.length ≤ count) :
    (compress n groups).machineSteps ≤ groups.length*AffineJointCover.Cost.microBudget n count := by
  induction groups with
  | nil => simp [compress]
  | cons group rest ih =>
      have sizes : group.length+rest.flatten.length ≤ count := by simpa only [List.flatten_cons,List.length_append] using size
      have tail := ih (by omega)
      have first := (AffineJointCover.Cost.compact_machineSteps n group).trans
        (microBudget_mono n group.length count (by omega))
      simp only [compress,List.length_cons]
      nlinarith

theorem compress_maxInput (n count : Nat) (groups : List Cells) (size : groups.flatten.length ≤ count) :
    (compress n groups).maxInput ≤ 2*n+2*count+5 := by
  induction groups with
  | nil => simp [compress]
  | cons group rest ih =>
      have sizes : group.length+rest.flatten.length ≤ count := by simpa only [List.flatten_cons,List.length_append] using size
      have tail := ih (by omega)
      have first := AffineJointCover.Cost.compact_maxInput n group
      simp only [compress,Nat.max_le]
      exact ⟨by omega,tail⟩

def compactBudget (n count : Nat) : Nat :=
  count*partitionRound n count+count*compressionRound n count+
    AffineCollect.Cost.collectBudget n count+6*count*(cellBound n+1)+9

theorem compact_cells (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (compact n cells).cells ≤ compactBudget n cells.length := by
  have groupsValid := partition_valid n cells valid
  have compressedValid := compress_valid n _ groupsValid
  have collectedValid := AffineCollect.collect_valid n _ compressedValid
  have groupCount := partition_length cells
  have totalCount := partition_count cells
  have partitioned := partition_cells_bound n cells.length cells valid (Nat.le_refl _)
  have compressed := compress_cells n cells.length (partition cells).value groupsValid totalCount.le
  have outputCount := compress_length n (partition cells).value
  rw [totalCount] at outputCount
  have collected := (AffineCollect.Cost.collect_visits n _ compressedValid).trans
    (AffineCollect.Cost.collectBudget_mono n _ cells.length outputCount)
  have groupStorageBound := partition_storage n cells valid
  have compressedStorage := AffineCarrier.Cost.storage_bound n _ compressedValid
  have finalStorage := AffineCarrier.Cost.storage_bound n _ collectedValid
  have collectedCount := AffineCollect.collect_length n _ compressedValid
  simp only [compact,compactBudget]
  nlinarith

theorem compact_machineSteps (n : Nat) (cells : Cells) :
    (compact n cells).machineSteps ≤ cells.length*AffineJointCover.Cost.microBudget n cells.length := by
  have steps := compress_machineSteps n cells.length (partition cells).value (partition_count cells).le
  exact steps.trans (Nat.mul_le_mul_right _ (partition_length cells))

theorem compact_maxInput (n : Nat) (cells : Cells) :
    (compact n cells).maxInput ≤ 2*n+2*cells.length+5 :=
  compress_maxInput n cells.length (partition cells).value (partition_count cells).le

end SaturationMonoid.ComplexityProjection.SATSource.AffineGroupCover
