import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCollect.Joint
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.IntegerMachine

/-!
The hull is generated from the same tables, common source, tagged image and Gaussian
rows as the original joint cover. Its ledger is in source cells. Volume is instead
stored and operated on as binary words: each addition and comparison has a direct
fixed-machine execution contract. Constructing counters and compiling the outer
source loop to one Turing machine remain separate responsibilities.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineJointCover.Cost

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Valid Separated storage cellSize resultSize)
open AffineCarrier.Cost (cellBound)
open CapacityMatching.SourceCost (Counted)
open Turing

/-- Mathematical interpretation only; the producer never invokes this reader. -/
def naturalValue : List Bool → Nat
  | [] => 0
  | bit::rest => (if bit then 1 else 0)+2*naturalValue rest

theorem payload_natural (bits : List Bool) : IntegerMachine.payloadValue false bits = (naturalValue bits : ℤ) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [naturalValue,IntegerMachine.payloadValue,IntegerMachine.bitValue,ih]

def power : Nat → Counted (List Bool)
  | 0 => ⟨[true],3⟩
  | degree+1 =>
      let tail := power degree
      ⟨false::tail.value,tail.cells+2⟩

theorem power_length (degree : Nat) : (power degree).value.length = degree+1 := by
  induction degree with
  | zero => rfl
  | succ degree ih => simp only [power,List.length_cons,ih]

theorem power_value (degree : Nat) : naturalValue (power degree).value = 2^degree := by
  induction degree with
  | zero => rfl
  | succ degree ih => simp only [power,naturalValue,Bool.false_eq_true,if_false,Nat.zero_add,ih,pow_succ]; omega

theorem power_cells (degree : Nat) : (power degree).cells = 2*degree+3 := by
  induction degree with
  | zero => rfl
  | succ degree ih => simp only [power,ih]; omega

theorem addPayload_sign (carry : Bool) (left right : List Bool) :
    (IntegerMachine.addPayload false false carry left right).1 = false := by
  cases left with
  | nil =>
      cases right with
      | nil => cases carry <;> simp [IntegerMachine.addPayload,IntegerMachine.finalSign,IntegerMachine.nextCarry,IntegerMachine.sumBit]
      | cons bit right =>
          rw [IntegerMachine.addPayload]
          exact addPayload_sign (IntegerMachine.nextCarry false bit carry) [] right
  | cons bit left =>
      cases right with
      | nil =>
          rw [IntegerMachine.addPayload]
          exact addPayload_sign (IntegerMachine.nextCarry bit false carry) left []
      | cons other right =>
          rw [IntegerMachine.addPayload]
          exact addPayload_sign (IntegerMachine.nextCarry bit other carry) left right
termination_by left.length+right.length

theorem addPayload_length (a b carry : Bool) (left right : List Bool) :
    (IntegerMachine.addPayload a b carry left right).2.length = max left.length right.length+1 := by
  cases left with
  | nil =>
      cases right with
      | nil => simp [IntegerMachine.addPayload]
      | cons bit right =>
          have tail := addPayload_length a b (IntegerMachine.nextCarry a bit carry) [] right
          simp only [IntegerMachine.addPayload,List.length_cons,tail,List.length_nil,Nat.zero_max]
  | cons bit left =>
      cases right with
      | nil =>
          have tail := addPayload_length a b (IntegerMachine.nextCarry bit b carry) left []
          simp only [IntegerMachine.addPayload,List.length_cons,tail,List.length_nil,Nat.max_zero]
      | cons other right =>
          have tail := addPayload_length a b (IntegerMachine.nextCarry bit other carry) left right
          simp only [IntegerMachine.addPayload,List.length_cons,tail]
          omega
termination_by left.length+right.length

def addInput (left right : List Bool) : List (Option Bool) :=
  IntegerMachine.inputCode false (false::left) (false::right)

def addWord (left right : List Bool) : List Bool := (IntegerMachine.rawArithmetic (addInput left right)).tail

theorem add_source (left right : List Bool) :
    IntegerMachine.rawArithmetic (addInput left right) =
      false::(IntegerMachine.addPayload false false false left right).2 := by
  rw [addInput,IntegerMachine.rawArithmetic_code]
  simp only [Bool.xor_false,addPayload_sign]
  change false::(IntegerMachine.addPayload false false false left (right.map id)).2 = _
  rw [List.map_id]

theorem addWord_value (left right : List Bool) : naturalValue (addWord left right) = naturalValue left+naturalValue right := by
  have sum := IntegerMachine.addPayload_value false false false left right
  rw [addPayload_sign,payload_natural,payload_natural,payload_natural] at sum
  simp only [IntegerMachine.bitValue,Bool.false_eq_true,if_false,add_zero] at sum
  simp only [addWord,add_source,List.tail_cons]
  exact_mod_cast sum

theorem addWord_length (left right : List Bool) : (addWord left right).length = max left.length right.length+1 := by
  simp only [addWord,add_source,List.tail_cons,addPayload_length]

theorem addInput_length (left right : List Bool) : (addInput left right).length = left.length+right.length+4 := by
  simp only [addInput,IntegerMachine.inputCode_length,List.length_cons]
  omega

def addSteps (left right : List Bool) : Nat := 3*(addInput left right).length+12

def add_outputs (left right : List Bool) :
    TM2OutputsInTime IntegerMachine.machine (addInput left right) (some (false::addWord left right)) (addSteps left right) := by
  have executed := IntegerMachine.rawArithmetic_outputs (addInput left right)
  simpa only [addSteps,addWord,add_source,List.tail_cons] using executed

structure WordRun where
  value : List Bool
  machineSteps : Nat
  cells : Nat
  deriving Repr

def add (left right : List Bool) : WordRun :=
  let input := addInput left right
  let output := IntegerMachine.rawArithmetic input
  ⟨output.tail,3*input.length+12,8*input.length+(3*input.length+12)+4*output.length+10⟩

theorem add_value (left right : List Bool) : (add left right).value = addWord left right := rfl

theorem add_machineSteps (left right : List Bool) : (add left right).machineSteps = 3*(left.length+right.length)+24 := by
  simp only [add,addInput_length]
  omega

theorem add_cells (left right : List Bool) : (add left right).cells ≤ 16*(left.length+right.length+5) := by
  have maximum : max left.length right.length ≤ left.length+right.length := by omega
  simp only [add,addInput_length,add_source,List.length_cons,addPayload_length]
  omega

def pad (width : Nat) (bits : List Bool) : List Bool := bits++List.replicate (width-bits.length) false

theorem natural_append_zeros (bits : List Bool) (zeros : Nat) :
    naturalValue (bits++List.replicate zeros false) = naturalValue bits := by
  induction bits with
  | nil =>
      induction zeros with
      | zero => rfl
      | succ zeros ih => simp only [List.nil_append,List.replicate_succ,naturalValue,Bool.false_eq_true,if_false,Nat.zero_add] at ih ⊢; omega
  | cons bit rest ih => simp only [List.cons_append,naturalValue,ih]

theorem pad_value (width : Nat) (bits : List Bool) : naturalValue (pad width bits) = naturalValue bits := natural_append_zeros _ _

theorem pad_length (width : Nat) (bits : List Bool) (bound : bits.length ≤ width) : (pad width bits).length = width := by
  simp only [pad,List.length_append,List.length_replicate]
  omega

theorem natural_injective (left right : List Bool) (length : left.length = right.length)
    (same : naturalValue left = naturalValue right) : left = right := by
  induction left generalizing right with
  | nil => exact (List.length_eq_zero_iff.mp length.symm).symm
  | cons a left ih =>
      cases right with
      | nil => simp at length
      | cons b right =>
          have tailLength : left.length=right.length := by simpa using length
          cases a <;> cases b <;> simp [naturalValue] at same
          all_goals try omega
          all_goals have tails : naturalValue left=naturalValue right := by omega
          all_goals exact congrArg _ (ih right tailLength tails)

def compareInput (left right : List Bool) : List (Option Bool) :=
  let width := max left.length right.length
  WordMachine.pairCode (pad width left) (pad width right)

structure Comparison where
  value : Bool
  machineSteps : Nat
  cells : Nat
  deriving Repr

def compare (left right : List Bool) : Comparison :=
  let input := compareInput left right
  ⟨WordMachine.rawMatch input,2*input.length+3,
    8*(left.length+right.length+1)+8*input.length+(2*input.length+3)+5⟩

theorem compare_value (left right : List Bool) : (compare left right).value = decide (naturalValue left=naturalValue right) := by
  rw [compare,compareInput,WordMachine.rawMatch_pair]
  change (pad (max left.length right.length) left == pad (max left.length right.length) right) = _
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  constructor
  · intro same
    have values := congrArg naturalValue same
    simpa only [pad_value] using values
  · intro same
    apply natural_injective
    · rw [pad_length _ _ (Nat.le_max_left _ _),pad_length _ _ (Nat.le_max_right _ _)]
    · simpa only [pad_value] using same

theorem compareInput_length (left right : List Bool) :
    (compareInput left right).length = 2*max left.length right.length+1 := by
  simp only [compareInput,WordMachine.pairCode_length,
    pad_length _ _ (Nat.le_max_left _ _),pad_length _ _ (Nat.le_max_right _ _)]
  omega

def compare_outputs (left right : List Bool) :
    TM2OutputsInTime WordMachine.machine (compareInput left right) (some [(compare left right).value])
      (compare left right).machineSteps := WordMachine.rawMatch_outputs _

theorem compare_cells (left right : List Bool) : (compare left right).cells ≤ 40*(left.length+right.length+1) := by
  have maximum : max left.length right.length ≤ left.length+right.length := by omega
  simp only [compare,compareInput_length]
  omega

def join (n : Nat) : Result → Result → Counted Result
  | .contradiction,right => ⟨right,2*resultSize right+3⟩
  | left,.contradiction => ⟨left,2*resultSize left+3⟩
  | .basis left,.basis right =>
      let leftTable := Table.coordinates n left
      let rightTable := Table.coordinates n right
      let source := BranchImage.table n leftTable rightTable
      let image := AtomImage.generate source
      let reduced := EliminateCost.run image.kernel
      ⟨reduced.result,
        AffineCollect.coordinateWork n left+AffineCollect.coordinateWork n right+
          (n+1)*(8*(AffineCollect.tableSize leftTable+AffineCollect.tableSize rightTable+AffineCollect.tableSize source)+8)+
          (AtomImage.generateVisits source+1)*(8*AffineCollect.imageWorkspace n+8)+
          (reduced.cells+2)*(8*cellBound n+8)+2*(cellSize left+cellSize right+resultSize reduced.result)+12⟩

theorem join_value (n : Nat) (left right : Result) : (join n left right).value = BranchImage.join n left right := by
  cases left <;> cases right <;>
    simp only [join,BranchImage.join,EliminateCost.run_result,BranchImage.common,BranchImage.source]

theorem join_valid (n : Nat) (left right : Result) (leftValid : left.triangular ∧ left.within n)
    (rightValid : right.triangular ∧ right.within n) :
    (join n left right).value.triangular ∧ (join n left right).value.within n := by
  rw [join_value]
  exact (BranchImage.join_invariants n left right leftValid.2 leftValid.1 rightValid.2 rightValid.1).symm

def joinBudget (n : Nat) : Nat := AffineCollect.Cost.mergeBudget n+2*cellBound n+5

theorem join_cells (n : Nat) (left right : Result) (leftValid : left.triangular ∧ left.within n)
    (rightValid : right.triangular ∧ right.within n) : (join n left right).cells ≤ joinBudget n := by
  cases left with
  | contradiction =>
      have size := AffineCarrier.Cost.result_size n right rightValid.1 rightValid.2
      simp only [join,joinBudget]
      omega
  | basis left =>
      cases right with
      | contradiction =>
          have size := AffineCarrier.Cost.result_size n (.basis left) leftValid.1 leftValid.2
          simp only [join,joinBudget]
          omega
      | basis right =>
          have complete := AffineCollect.Cost.merge_visits n left right leftValid rightValid
          have bounded : (join n (.basis left) (.basis right)).cells ≤ (AffineCollect.merge n left right).visits := by
            simp only [join,AffineCollect.merge]
            gcongr
            omega
          exact bounded.trans (complete.trans (by unfold joinBudget; omega))

def hull (n : Nat) : Cells → Counted Result
  | [] => ⟨.contradiction,1⟩
  | basis::rest =>
      let tail := hull n rest
      let current := join n (.basis basis) tail.value
      ⟨current.value,tail.cells+current.cells+2*cellSize basis+2*resultSize current.value+7⟩

theorem hull_value (n : Nat) (cells : Cells) : (hull n cells).value = AffineJointCover.hull n cells := by
  induction cells with
  | nil => rfl
  | cons basis rest ih => simp only [hull,join_value,ih,AffineJointCover.hull]

theorem hull_good (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (hull n cells).value.triangular ∧ (hull n cells).value.within n := by
  rw [hull_value]
  exact (AffineJointCover.hull_valid n cells valid).symm

def hullBudget (n count : Nat) : Nat := count*(joinBudget n+4*cellBound n+9)+1

theorem hull_cells (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (hull n cells).cells ≤ hullBudget n cells.length := by
  induction cells with
  | nil => simp [hull,hullBudget]
  | cons basis rest ih =>
      have first := valid basis (by simp)
      have restValid : Valid n rest := fun other member => valid other (by simp [member])
      have tail := ih restValid
      have tailGood := hull_good n rest restValid
      have construction := join_cells n (.basis basis) (hull n rest).value first tailGood
      have current := join_valid n (.basis basis) (hull n rest).value first tailGood
      have currentSize := AffineCarrier.Cost.result_size n _ current.1 current.2
      have sourceSize := AffineCarrier.Cost.cell_size n basis first.1 first.2
      simp only [hull,hullBudget,List.length_cons] at tail ⊢
      nlinarith

def cellPower (n : Nat) (basis : List Row) : Counted (List Bool) :=
  let free := freeIndices n basis
  let emitted := power free.length
  ⟨emitted.value,freeIndexVisits n basis+emitted.cells+2*cellSize basis+3*free.length+2*n+9⟩

theorem cellPower_value (n : Nat) (basis : List Row) :
    naturalValue (cellPower n basis).value = 2^(freeIndices n basis).length := power_value _

theorem cellPower_length (n : Nat) (basis : List Row) : (cellPower n basis).value.length ≤ n+1 := by
  change (power (freeIndices n basis).length).value.length ≤ _
  rw [power_length]
  exact Nat.add_le_add_right (Table.freeWidth_le n basis) 1

def powerBudget (n : Nat) : Nat := (n+1)*(n+2)+2*cellBound n+7*n+12

theorem cellPower_cells (n : Nat) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (cellPower n basis).cells ≤ powerBudget n := by
  have indices := bounded_freeIndexVisits n basis valid.1 valid.2
  have width := Table.freeWidth_le n basis
  have size := AffineCarrier.Cost.cell_size n basis valid.1 valid.2
  simp only [cellPower,power_cells,powerBudget]
  omega

structure Volume where
  digits : List Bool
  additions : Nat
  machineSteps : Nat
  maxInput : Nat
  cells : Nat
  deriving Repr

def volume (n : Nat) : Cells → Volume
  | [] => ⟨[],0,0,0,1⟩
  | basis::rest =>
      let tail := volume n rest
      let weight := cellPower n basis
      let total := add weight.value tail.digits
      ⟨total.value,tail.additions+1,tail.machineSteps+total.machineSteps,
        max tail.maxInput (addInput weight.value tail.digits).length,
        tail.cells+weight.cells+total.cells+2*(tail.digits.length+weight.value.length+total.value.length)+7⟩

theorem volume_value (n : Nat) (cells : Cells) :
    naturalValue (volume n cells).digits = AffineJointCover.volume n cells := by
  induction cells with
  | nil => rfl
  | cons basis rest ih =>
      simp only [volume,add_value,addWord_value,cellPower_value,ih,AffineJointCover.volume,List.map_cons,List.sum_cons]

theorem volume_additions (n : Nat) (cells : Cells) : (volume n cells).additions = cells.length := by
  induction cells with
  | nil => rfl
  | cons basis rest ih => simp only [volume,ih,List.length_cons]

theorem volume_length (n : Nat) (cells : Cells) : (volume n cells).digits.length ≤ n+cells.length+1 := by
  induction cells with
  | nil => simp [volume]
  | cons basis rest ih =>
      have weight := cellPower_length n basis
      simp only [volume,add_value,addWord_length,List.length_cons]
      omega

theorem volume_maxInput (n : Nat) (cells : Cells) : (volume n cells).maxInput ≤ 2*n+cells.length+5 := by
  induction cells with
  | nil => simp [volume]
  | cons basis rest ih =>
      have weight := cellPower_length n basis
      have previous := volume_length n rest
      simp only [volume,addInput_length,List.length_cons]
      omega

theorem volume_machineSteps (n : Nat) (cells : Cells) :
    (volume n cells).machineSteps ≤ cells.length*(6*n+3*cells.length+27) := by
  induction cells with
  | nil => simp [volume]
  | cons basis rest ih =>
      have weight := cellPower_length n basis
      have previous := volume_length n rest
      simp only [volume,add_machineSteps,List.length_cons]
      nlinarith

def volumeBudget (n count : Nat) : Nat := count*(powerBudget n+40*(n+count+5))+1

theorem volume_cells (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (volume n cells).cells ≤ volumeBudget n cells.length := by
  induction cells with
  | nil => simp [volume,volumeBudget]
  | cons basis rest ih =>
      have first := valid basis (by simp)
      have tail := ih (fun other member => valid other (by simp [member]))
      have weight := cellPower_length n basis
      have weightCost := cellPower_cells n basis first
      have previous := volume_length n rest
      have addition := add_cells (cellPower n basis).value (volume n rest).digits
      have resultLength := volume_length n (basis::rest)
      change (add (cellPower n basis).value (volume n rest).digits).value.length ≤ _ at resultLength
      simp only [volume,volumeBudget,List.length_cons] at tail resultLength ⊢
      nlinarith

theorem compare_machineSteps (left right : List Bool) :
    (compare left right).machineSteps = 4*max left.length right.length+5 := by
  simp only [compare,compareInput_length]
  omega

structure Compression where
  value : Cells
  machineSteps : Nat
  maxInput : Nat
  cells : Nat
  deriving Repr

def compact (n : Nat) (cells : Cells) : Compression :=
  let current := hull n cells
  match current.value with
  | .contradiction => ⟨[],0,0,current.cells+2*storage cells+5⟩
  | .basis basis =>
      let total := volume n cells
      let full := cellPower n basis
      let tested := compare total.digits full.value
      let output := if tested.value then [basis] else cells
      ⟨output,total.machineSteps+tested.machineSteps,
        max total.maxInput (compareInput total.digits full.value).length,
        current.cells+total.cells+full.cells+tested.cells+
          2*storage cells+2*storage output+2*resultSize current.value+9⟩

theorem compact_value (n : Nat) (cells : Cells) : (compact n cells).value = AffineJointCover.compact n cells := by
  cases result : (hull n cells).value with
  | contradiction => simp [compact,AffineJointCover.compact,← hull_value,result]
  | basis basis =>
      simp [compact,AffineJointCover.compact,← hull_value,result,compare_value,volume_value,cellPower_value]

theorem compact_valid (n : Nat) (cells : Cells) (valid : Valid n cells) : Valid n (compact n cells).value := by
  rw [compact_value]
  exact AffineJointCover.compact_valid n cells valid

theorem compact_separated (n : Nat) (cells : Cells) (separated : Separated cells) : Separated (compact n cells).value := by
  rw [compact_value]
  exact AffineJointCover.compact_separated n cells separated

theorem compact_read (n : Nat) (cells : Cells) (valid : Valid n cells) (separated : Separated cells)
    (assignment : Assignment n) :
    AffineCarrier.read (compact n cells).value (extendAssignment assignment) =
      AffineCarrier.read cells (extendAssignment assignment) := by
  rw [compact_value]
  exact AffineJointCover.compact_read n cells valid separated assignment

theorem compact_output (n : Nat) (cells : Cells) (valid : Valid n cells) :
    storage (compact n cells).value ≤ storage cells+cellBound n := by
  have generated := hull_good n cells valid
  cases result : (hull n cells).value with
  | contradiction => simp [compact,result,storage]
  | basis basis =>
      simp only [result,Result.triangular,Result.within] at generated
      have size := AffineCarrier.Cost.cell_size n basis generated.1 generated.2
      simp only [compact,result]
      split
      · simp only [storage,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
        omega
      · omega

def compactBudget (n count : Nat) : Nat :=
  hullBudget n count+volumeBudget n count+powerBudget n+40*(2*n+count+3)+
    4*count*cellBound n+4*cellBound n+11

theorem compact_cells (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (compact n cells).cells ≤ compactBudget n cells.length := by
  have constructed := hull_cells n cells valid
  have generated := hull_good n cells valid
  have stored := AffineCarrier.Cost.storage_bound n cells valid
  have output := compact_output n cells valid
  cases result : (hull n cells).value with
  | contradiction =>
      simp only [compact,result,compactBudget]
      nlinarith
  | basis basis =>
      simp only [result,Result.triangular,Result.within] at generated
      have total := volume_cells n cells valid
      have full := cellPower_cells n basis generated
      have compared := compare_cells (volume n cells).digits (cellPower n basis).value
      have totalLength := volume_length n cells
      have fullLength := cellPower_length n basis
      have resultSizeBound := AffineCarrier.Cost.result_size n (.basis basis) generated.1 generated.2
      simp only [compact,result] at output ⊢
      simp only [compactBudget]
      nlinarith

def microBudget (n count : Nat) : Nat := count*(6*n+3*count+27)+4*n+4*count+9

theorem compact_machineSteps (n : Nat) (cells : Cells) :
    (compact n cells).machineSteps ≤ microBudget n cells.length := by
  cases result : (hull n cells).value with
  | contradiction => simp [compact,result]
  | basis basis =>
      have total := volume_machineSteps n cells
      have totalLength := volume_length n cells
      have fullLength := cellPower_length n basis
      have length : max (volume n cells).digits.length (cellPower n basis).value.length ≤ n+cells.length+1 := by omega
      simp only [compact,result,compare_machineSteps,microBudget]
      omega

theorem compact_maxInput (n : Nat) (cells : Cells) :
    (compact n cells).maxInput ≤ 2*n+2*cells.length+5 := by
  cases result : (hull n cells).value with
  | contradiction => simp [compact,result]
  | basis basis =>
      have total := volume_maxInput n cells
      have totalLength := volume_length n cells
      have fullLength := cellPower_length n basis
      simp only [compact,result,compareInput_length]
      omega

/-- Every accumulation call uses this same fixed finite integer machine. -/
def volume_step_outputs (n : Nat) (basis : List Row) (rest : Cells) :
    TM2OutputsInTime IntegerMachine.machine
      (addInput (cellPower n basis).value (volume n rest).digits)
      (some (false::(volume n (basis::rest)).digits))
      (addSteps (cellPower n basis).value (volume n rest).digits) :=
  add_outputs _ _

/-- The final coverage test is a real finite word-machine run on the generated words. -/
def volume_compare_outputs (n : Nat) (cells : Cells) (basis : List Row) :
    TM2OutputsInTime WordMachine.machine
      (compareInput (volume n cells).digits (cellPower n basis).value)
      (some [(compare (volume n cells).digits (cellPower n basis).value).value])
      (compare (volume n cells).digits (cellPower n basis).value).machineSteps :=
  compare_outputs _ _

end SaturationMonoid.ComplexityProjection.SATSource.AffineJointCover.Cost
