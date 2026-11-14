import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Forgetting.Scalar.Source

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ForgettingScalar
open scoped BigOperators
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

def capAdd (cap left right : Nat) : Nat := min cap (left+right)
def capMul (cap left right : Nat) : Nat := min cap (left*right)

theorem capAdd_exact (cap left right : Nat) : capAdd cap (min cap left) (min cap right)=min cap (left+right) := by
  unfold capAdd
  omega

theorem capMul_exact (cap left right : Nat) : capMul cap (min cap left) (min cap right)=min cap (left*right) := by
  unfold capMul
  by_cases zero : cap=0
  · simp [zero]
  by_cases leftZero : left=0
  · simp [leftZero]
  by_cases rightZero : right=0
  · simp [rightZero]
  have capPos : 1 ≤ cap := by omega
  have leftPos : 1 ≤ left := by omega
  have rightPos : 1 ≤ right := by omega
  by_cases smallLeft : left ≤ cap
  · rw [Nat.min_eq_right smallLeft]
    by_cases smallRight : right ≤ cap
    · rw [Nat.min_eq_right smallRight]
    · rw [Nat.min_eq_left (by omega : cap ≤ right),Nat.min_eq_left (by nlinarith : cap ≤ left*cap),Nat.min_eq_left (by nlinarith : cap ≤ left*right)]
  · rw [Nat.min_eq_left (by omega : cap ≤ left)]
    by_cases smallRight : right ≤ cap
    · rw [Nat.min_eq_right smallRight,Nat.min_eq_left (by nlinarith : cap ≤ cap*right),Nat.min_eq_left (by nlinarith : cap ≤ left*right)]
    · rw [Nat.min_eq_left (by omega : cap ≤ right),Nat.min_eq_left (by nlinarith : cap ≤ cap*cap),Nat.min_eq_left (by nlinarith : cap ≤ left*right)]

def cappedWeight {n : Nat} (cap rate : Nat) : CNFFormula n → (Nat → Bool) → Nat
  | [],_ => min cap 1
  | clause::rest,point => capMul cap (min cap (if CNFClause.eval clause point then rate else 1)) (cappedWeight cap rate rest point)

theorem cappedWeight_exact {n : Nat} (cap rate : Nat) (formula : CNFFormula n) (point : Nat → Bool) :
    cappedWeight cap rate formula point=min cap (weight rate formula point) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp only [cappedWeight,ih,capMul_exact,weight]

theorem cappedWeight_bound {n : Nat} (cap rate : Nat) (formula : CNFFormula n) (point : Nat → Bool) :
    cappedWeight cap rate formula point ≤ cap := by rw [cappedWeight_exact]; exact Nat.min_le_left _ _

def sumNat : List Nat → ((Nat → Bool) → Nat) → (Nat → Bool) → Nat
  | [],value,point => value point
  | i::rest,value,point => sumNat rest value (Function.update point i false)+sumNat rest value (Function.update point i true)

theorem sumNat_int (indices : List Nat) (value : (Nat → Bool) → Nat) (point : Nat → Bool) :
    (sumNat indices value point : Int)=InterferenceDecision.sumOver indices (fun x => (value x : Int)) point := by
  induction indices generalizing point with
  | nil => rfl
  | cons i rest ih => simp only [sumNat,Nat.cast_add,InterferenceDecision.sumOver,ih]

def cappedSum (cap : Nat) : List Nat → ((Nat → Bool) → Nat) → (Nat → Bool) → Nat
  | [],value,point => min cap (value point)
  | i::rest,value,point =>
      let first := cappedSum cap rest value (Function.update point i false)
      if first=cap then cap else capAdd cap first (cappedSum cap rest value (Function.update point i true))

theorem cappedSum_exact (cap : Nat) (indices : List Nat) (value : (Nat → Bool) → Nat) (point : Nat → Bool) :
    cappedSum cap indices value point=min cap (sumNat indices value point) := by
  induction indices generalizing point with
  | nil => rfl
  | cons i rest ih =>
      simp only [cappedSum,ih,sumNat]
      split
      · omega
      · exact capAdd_exact _ _ _

theorem cappedSum_bound (cap : Nat) (indices : List Nat) (value : (Nat → Bool) → Nat) (point : Nat → Bool) :
    cappedSum cap indices value point ≤ cap := by rw [cappedSum_exact]; exact Nat.min_le_left _ _

theorem fill_original (n : Nat) (point : Assignment n) :
    InterferenceDecision.fill InterferenceDecision.zeroEnvironment 0 point=extendAssignment point := by
  funext i
  simp only [InterferenceDecision.fill,extendAssignment,InterferenceDecision.zeroEnvironment,Nat.zero_add,Nat.zero_le,true_and,Nat.sub_zero]

theorem sumNat_mass {n : Nat} (formula : CNFFormula n) :
    sumNat (List.range n) (weight (boost n) formula) InterferenceDecision.zeroEnvironment=mass formula := by
  have expanded := sumNat_int (List.range n) (weight (boost n) formula) InterferenceDecision.zeroEnvironment
  rw [InterferenceDecision.sumOver_range] at expanded
  simp only [fill_original] at expanded
  exact_mod_cast expanded

def read {n : Nat} (formula : CNFFormula n) : Nat :=
  cappedSum (capacity formula) (List.range n) (cappedWeight (capacity formula) (boost n) formula) InterferenceDecision.zeroEnvironment

theorem read_exact {n : Nat} (formula : CNFFormula n) : read formula=signal formula := by
  have same : cappedWeight (capacity formula) (boost n) formula=weight (boost n) formula := by
    funext point
    rw [cappedWeight_exact]
    exact Nat.min_eq_right (weight_le _ (boost_pos n) formula point)
  rw [read,same,cappedSum_exact,sumNat_mass]
  rfl

def receive {n : Nat} (formula : CNFFormula n) : Bool := Receiver (read formula) (capacity formula) 0 1

theorem receive_correct {n : Nat} (formula : CNFFormula n) : receive formula=true ↔ CNFSatisfiable formula := by
  rw [receive,read_exact]
  exact energyDecision_correct formula

theorem read_word_bound {n : Nat} (formula : CNFFormula n) : read formula < 2^((n+2)*formula.length+1) := by
  rw [read_exact]
  exact signal_word_bound formula

theorem source_read {n : Nat} (formula : CNFFormula n) : read formula=
    cappedSum (capacity formula) (List.range n) (fun point => (sourceProgram formula).eval point |>.toNat) InterferenceDecision.zeroEnvironment := by
  have same : (fun point => (sourceProgram formula).eval point |>.toNat)=weight (boost n) formula := by
    funext point
    simp only [sourceProgram_eval,Int.toNat_natCast]
  rw [same,cappedSum_exact,sumNat_mass,read_exact]
  rfl

def bucket {n : Nat} (formula : CNFFormula n) : Nat := (4*read formula)/capacity formula

theorem bucket_bound {n : Nat} (formula : CNFFormula n) : bucket formula ≤ 4 := by
  have bound : read formula ≤ capacity formula := by rw [read_exact]; exact Nat.min_le_left _ _
  calc
    bucket formula ≤ (4*capacity formula)/capacity formula := Nat.div_le_div_right (by omega)
    _ = 4 := Nat.mul_div_cancel _ (capacity_pos formula)

theorem bucket_yes {n : Nat} (formula : CNFFormula n) (yes : CNFSatisfiable formula) : bucket formula=4 := by
  rw [bucket,read_exact,signal_yes formula yes]
  exact Nat.mul_div_cancel _ (capacity_pos formula)

theorem bucket_no {n : Nat} (formula : CNFFormula n) (no : ¬ CNFSatisfiable formula) : bucket formula ≤ 1 := by
  have small := signal_no formula no
  rw [← read_exact] at small
  calc
    bucket formula ≤ capacity formula/capacity formula := Nat.div_le_div_right small
    _ = 1 := Nat.div_self (capacity_pos formula)

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer

def adcWord (value : Fin 5) : FiniteADCWord .coarse := ⟨value.val,by
  have small := value.isLt
  norm_num [finiteADCGridDenominator]
  omega⟩

def adcRead (value : Fin 5) : Bool :=
  finiteADCBitVectorEnergyCircuit .coarse
    (adcWord 0) (adcWord 4) (adcWord value)
    (adcWord 0) (adcWord 1) (adcWord 0)

theorem adcRead_integer (value : Fin 5) : adcRead value=Receiver value.val 4 0 1 := by
  rw [adcRead,finiteADCBitVectorEnergyCircuit_exact,finiteADCWordEnergyDecision128_exact]
  simp only [adcWord]
  rfl

def packetRead {n : Nat} (formula : CNFFormula n) : Bool := adcRead ⟨bucket formula,by have bounded := bucket_bound formula; omega⟩

theorem packetRead_integer {n : Nat} (formula : CNFFormula n) : packetRead formula=Receiver (bucket formula) 4 0 1 := adcRead_integer _

theorem packetRead_correct {n : Nat} (formula : CNFFormula n) : packetRead formula=true ↔ CNFSatisfiable formula := by
  rw [packetRead_integer]
  simp only [Receiver,finiteADCEnergyIntegerAboveQuarter,finiteADCEnergyIntegerLeft,finiteADCEnergyIntegerRight,
    decide_eq_true_eq,zero_pow (by omega : 2 ≠ 0),one_pow,mul_one,zero_mul,add_zero]
  constructor
  · intro high
    by_contra no
    have small : (bucket formula : Int) ≤ 1 := by exact_mod_cast bucket_no formula no
    have positive : (0 : Int) ≤ bucket formula := by positivity
    nlinarith [high.2.2]
  · intro yes
    rw [bucket_yes formula yes]
    norm_num

theorem sumNat_signal_yes (cap : Nat) (indices : List Nat) (value : (Nat → Bool) → Bool) (point : Nat → Bool)
    (accepted : Boolean.anyOver indices value point=true) :
    cap ≤ sumNat indices (fun x => if value x then cap else 1) point := by
  induction indices generalizing point with
  | nil =>
      change value point=true at accepted
      simp only [sumNat,accepted,if_true,Nat.le_refl]
  | cons i rest ih =>
      simp only [Boolean.anyOver,Bool.or_eq_true] at accepted
      rcases accepted with yes | yes
      · exact (ih _ yes).trans (Nat.le_add_right _ _)
      · exact (ih _ yes).trans (Nat.le_add_left _ _)

theorem sumNat_signal_no (cap : Nat) (indices : List Nat) (value : (Nat → Bool) → Bool) (point : Nat → Bool)
    (rejected : Boolean.anyOver indices value point=false) :
    sumNat indices (fun x => if value x then cap else 1) point=2^indices.length := by
  induction indices generalizing point with
  | nil =>
      change value point=false at rejected
      simp [sumNat,rejected]
  | cons i rest ih =>
      have both : Boolean.anyOver rest value (Function.update point i false)=false ∧
          Boolean.anyOver rest value (Function.update point i true)=false := by
        simpa only [Boolean.anyOver,Bool.or_eq_false_iff] using rejected
      rw [sumNat,ih _ both.1,ih _ both.2,List.length_cons,pow_succ]
      omega

def programCapacity (program : Program) : Nat := boost (FunctionalSubstitution.inputs program.code).length

def programSignal (program : Program) : Nat :=
  cappedSum (programCapacity program) (FunctionalSubstitution.inputs program.code)
    (fun point => if truth (program.eval point) then programCapacity program else 1) InterferenceDecision.zeroEnvironment

theorem program_nonempty (program : Program) :
    Boolean.anyOver (FunctionalSubstitution.inputs program.code) (fun point => truth (program.eval point)) InterferenceDecision.zeroEnvironment=true ↔
      ∃ point, truth (program.eval point)=true := by
  constructor
  · exact FunctionalSubstitution.anyOver_witness _ _ _
  · rintro ⟨point,accepted⟩
    apply FunctionalSubstitution.anyOver_assign _ _ point _
    rw [FunctionalSubstitution.eval_environment_congr program _ point (FunctionalSubstitution.assign_member _ _ _)]
    exact accepted

theorem programSignal_yes (program : Program) (yes : ∃ point, truth (program.eval point)=true) :
    programSignal program=programCapacity program := by
  rw [programSignal,cappedSum_exact]
  exact Nat.min_eq_left (sumNat_signal_yes _ _ _ _ ((program_nonempty program).mpr yes))

theorem programSignal_no (program : Program) (no : ¬ ∃ point, truth (program.eval point)=true) :
    programSignal program=2^(FunctionalSubstitution.inputs program.code).length := by
  have rejected := Bool.eq_false_iff.mpr (fun yes => no ((program_nonempty program).mp yes))
  rw [programSignal,cappedSum_exact,sumNat_signal_no _ _ _ _ rejected]
  apply Nat.min_eq_right
  unfold programCapacity boost
  exact Nat.pow_le_pow_right (by omega) (by omega)

theorem programSignal_bound (program : Program) : programSignal program ≤ programCapacity program :=
  cappedSum_bound _ _ _ _

def programBucket (program : Program) : Nat := 4*programSignal program/programCapacity program

theorem programBucket_bound (program : Program) : programBucket program ≤ 4 := by
  have bound := programSignal_bound program
  calc
    programBucket program ≤ (4*programCapacity program)/programCapacity program := Nat.div_le_div_right (by omega)
    _ = 4 := Nat.mul_div_cancel _ (boost_pos _)

theorem programBucket_yes (program : Program) (yes : ∃ point, truth (program.eval point)=true) : programBucket program=4 := by
  rw [programBucket,programSignal_yes program yes]
  exact Nat.mul_div_cancel _ (boost_pos _)

theorem programBucket_no (program : Program) (no : ¬ ∃ point, truth (program.eval point)=true) : programBucket program=1 := by
  rw [programBucket,programSignal_no program no]
  unfold programCapacity boost
  rw [pow_add]
  norm_num
  rw [Nat.mul_comm 4]
  exact Nat.div_self (by positivity)

def programRead (program : Program) : Bool := adcRead ⟨programBucket program,by have bound := programBucket_bound program; omega⟩

theorem programRead_correct (program : Program) : programRead program=true ↔ ∃ point, truth (program.eval point)=true := by
  rw [programRead,adcRead_integer]
  change Receiver (programBucket program) 4 0 1=true ↔ ∃ point, truth (program.eval point)=true
  constructor
  · intro accepted
    by_contra no
    rw [programBucket_no program no] at accepted
    norm_num [Receiver,finiteADCEnergyIntegerAboveQuarter,finiteADCEnergyIntegerLeft,finiteADCEnergyIntegerRight] at accepted
  · intro yes
    rw [programBucket_yes program yes]
    norm_num [Receiver,finiteADCEnergyIntegerAboveQuarter,finiteADCEnergyIntegerLeft,finiteADCEnergyIntegerRight]

def compiledRead {n : Nat} (formula : CNFFormula n) (basis : List Row) : Bool :=
  let source := ProductClosureCost.compile formula basis
  !source.value.rejected && programRead source.value.frame.state.program.program

theorem compiledRead_correct {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    compiledRead formula basis=true ↔ ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
  have original := ProductClosureCost.compile_decision formula basis valid
  simpa only [compiledRead,PortUpdate.stateDecision,Bool.and_eq_true,programRead_correct,FunctionalSubstitution.decideProgram_correct] using original

theorem programSignal_word_bound (program : Program) :
    programSignal program < 2^((FunctionalSubstitution.inputs program.code).length+3) := by
  have bound := programSignal_bound program
  have positive := boost_pos (FunctionalSubstitution.inputs program.code).length
  change programSignal program ≤ 2^((FunctionalSubstitution.inputs program.code).length+2) at bound
  calc
    programSignal program ≤ 2^((FunctionalSubstitution.inputs program.code).length+2) := bound
    _ < 2^((FunctionalSubstitution.inputs program.code).length+3) := Nat.pow_lt_pow_right (by omega) (by omega)

theorem compiledRead_original {n : Nat} (formula : CNFFormula n) : compiledRead formula []=true ↔ CNFSatisfiable formula := by
  have source := compiledRead_correct formula [] ⟨triangular_nil,by simp [RowsWithin]⟩
  simpa only [FunctionalMessage.empty_formula,CNFSatisfiable] using source

end SaturationMonoid.ComplexityProjection.SATSource.ForgettingScalar
