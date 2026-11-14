import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Forgetting.Channels
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Closure.Cost
import H0mework.Computation.ADC.EnergyCircuit

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ForgettingScalar
open scoped BigOperators
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

abbrev Receiver := SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteADCEnergyIntegerAboveQuarter

def boost (n : Nat) : Nat := 2^(n+2)
def capacity {n : Nat} (formula : CNFFormula n) : Nat := boost n ^ formula.length

def weight {n : Nat} (rate : Nat) : CNFFormula n → (Nat → Bool) → Nat
  | [],_ => 1
  | clause::rest,point => (if CNFClause.eval clause point then rate else 1)*weight rate rest point

theorem boost_pos (n : Nat) : 0 < boost n := by unfold boost; positivity

theorem boost_ge_four (n : Nat) : 4 ≤ boost n := by
  unfold boost
  have positive : 1 ≤ 2^n := by
    have h : 0 < 2^n := by positivity
    omega
  rw [pow_add]
  norm_num
  omega

theorem capacity_pos {n : Nat} (formula : CNFFormula n) : 0 < capacity formula := pow_pos (boost_pos n) _

theorem weight_pos {n : Nat} (rate : Nat) (positive : 0 < rate) (formula : CNFFormula n) (point : Nat → Bool) :
    0 < weight rate formula point := by
  induction formula with
  | nil => simp [weight]
  | cons clause rest ih => simp only [weight]; split <;> positivity

theorem weight_le {n : Nat} (rate : Nat) (positive : 0 < rate) (formula : CNFFormula n) (point : Nat → Bool) :
    weight rate formula point ≤ rate^formula.length := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [weight,List.length_cons,pow_succ']
      split
      · exact Nat.mul_le_mul_left rate ih
      · simp only [one_mul]
        exact ih.trans (Nat.le_mul_of_pos_left _ positive)

theorem weight_yes {n : Nat} (rate : Nat) (formula : CNFFormula n) (point : Nat → Bool)
    (accepted : CNFFormula.eval formula point=true) : weight rate formula point=rate^formula.length := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      have both : CNFClause.eval clause point=true ∧ CNFFormula.eval rest point=true := by
        simpa only [CNFFormula.eval,List.all_cons,Bool.and_eq_true] using accepted
      simp only [weight,both.1,if_true,ih both.2,List.length_cons,pow_succ']

theorem weight_no {n : Nat} (rate : Nat) (positive : 0 < rate) (formula : CNFFormula n) (point : Nat → Bool)
    (rejected : CNFFormula.eval formula point=false) : rate*weight rate formula point ≤ rate^formula.length := by
  induction formula with
  | nil => simp [CNFFormula.eval] at rejected
  | cons clause rest ih =>
      have restBound := weight_le rate positive rest point
      cases value : CNFClause.eval clause point with
      | false => simp only [weight,value,Bool.false_eq_true,if_false,one_mul,List.length_cons,pow_succ']; exact Nat.mul_le_mul_left rate restBound
      | true =>
          have no : CNFFormula.eval rest point=false := by simpa only [CNFFormula.eval,List.all_cons,value,Bool.true_and] using rejected
          have tail := ih no
          simp only [weight,value,if_true,List.length_cons,pow_succ']
          exact Nat.mul_le_mul_left rate tail

def mass {n : Nat} (formula : CNFFormula n) : Nat :=
  ∑ point : Assignment n, weight (boost n) formula (extendAssignment point)

def signal {n : Nat} (formula : CNFFormula n) : Nat := min (capacity formula) (mass formula)

theorem mass_yes {n : Nat} (formula : CNFFormula n) (yes : CNFSatisfiable formula) : capacity formula ≤ mass formula := by
  obtain ⟨point,accepted⟩ := (satisfiable_iff_finite_assignment formula).mp yes
  have one : weight (boost n) formula (extendAssignment point) ≤ mass formula := by
    unfold mass
    exact Finset.single_le_sum (f := fun x : Assignment n => weight (boost n) formula (extendAssignment x))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ point)
  rw [weight_yes _ _ _ accepted] at one
  exact one

theorem mass_no {n : Nat} (formula : CNFFormula n) (no : ¬ CNFSatisfiable formula) : 4*mass formula ≤ capacity formula := by
  have pointBound (point : Assignment n) : boost n*weight (boost n) formula (extendAssignment point) ≤ capacity formula := by
    apply weight_no _ (boost_pos n)
    apply Bool.eq_false_iff.mpr
    exact fun accepted => no ⟨extendAssignment point,accepted⟩
  have total := Finset.sum_le_sum (fun point (_ : point ∈ (Finset.univ : Finset (Assignment n))) => pointBound point)
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul] at total
  change boost n*mass formula ≤ 2^n*capacity formula at total
  have positive : 0 < 2^n := by positivity
  unfold boost at total
  rw [pow_add] at total
  norm_num at total
  nlinarith

theorem signal_yes {n : Nat} (formula : CNFFormula n) (yes : CNFSatisfiable formula) : signal formula=capacity formula :=
  Nat.min_eq_left (mass_yes formula yes)

theorem signal_no {n : Nat} (formula : CNFFormula n) (no : ¬ CNFSatisfiable formula) : 4*signal formula ≤ capacity formula :=
  (Nat.mul_le_mul_left 4 (Nat.min_le_right _ _)).trans (mass_no formula no)

def decide {n : Nat} (formula : CNFFormula n) : Bool := capacity formula < 2*signal formula

theorem decide_correct {n : Nat} (formula : CNFFormula n) : decide formula=true ↔ CNFSatisfiable formula := by
  have positive := capacity_pos formula
  simp only [decide,decide_eq_true_eq]
  constructor
  · intro high
    by_contra no
    have small := signal_no formula no
    omega
  · intro yes
    rw [signal_yes formula yes]
    omega

def energyDecision {n : Nat} (formula : CNFFormula n) : Bool :=
  Receiver (signal formula) (capacity formula) 0 1

theorem energyDecision_correct {n : Nat} (formula : CNFFormula n) : energyDecision formula=true ↔ CNFSatisfiable formula := by
  have positive := capacity_pos formula
  have natural : signal formula ≤ capacity formula := Nat.min_le_left _ _
  simp only [energyDecision,Receiver,
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteADCEnergyIntegerAboveQuarter,
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteADCEnergyIntegerLeft,
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteADCEnergyIntegerRight,
    decide_eq_true_eq,zero_pow (by omega : 2 ≠ 0),one_pow,mul_one,zero_mul,add_zero]
  constructor
  · intro high
    by_contra no
    have small := signal_no formula no
    have castSmall : (4 : Int)*(signal formula : Int) ≤ capacity formula := by exact_mod_cast small
    have castPos : (0 : Int)<capacity formula := by exact_mod_cast positive
    have castNonneg : (0 : Int) ≤ signal formula := by positivity
    nlinarith [high.2.2]
  · intro yes
    rw [signal_yes formula yes]
    have castPos : (0 : Int)<capacity formula := by exact_mod_cast positive
    exact ⟨castPos,by norm_num,by nlinarith [sq_pos_of_pos castPos]⟩

theorem signal_word_bound {n : Nat} (formula : CNFFormula n) : signal formula < 2^((n+2)*formula.length+1) := by
  have stored : signal formula ≤ capacity formula := Nat.min_le_left _ _
  have positive := capacity_pos formula
  have size : capacity formula=2^((n+2)*formula.length) := by simp only [capacity,boost,pow_mul]
  rw [pow_succ,← size]
  omega

theorem weight_pow {n : Nat} (rate steps : Nat) (formula : CNFFormula n) (point : Nat → Bool) :
    weight (rate^steps) formula point=weight rate formula point^steps := by
  induction formula with
  | nil => simp [weight]
  | cons clause rest ih => simp only [weight,ih,mul_pow]; split <;> simp

def keep {n : Nat} (formula : CNFFormula n) (point : Assignment n) : ℚ :=
  (weight 2 formula (extendAssignment point) : ℚ)/2^formula.length

def sample {n : Nat} (formula : CNFFormula n) (steps : Nat) : ℚ :=
  finitePopulationAggregate (fun _ : Assignment n => (1 : ℚ)) (keep formula) steps

theorem sample_sourceMass {n : Nat} (formula : CNFFormula n) (steps : Nat) :
    sample formula steps=sourceMass n (fun point => keep formula point^steps) := by
  simp only [sample,finitePopulationAggregate,one_mul,sourceMass_apply]

theorem heterogeneity {n : Nat} (formula : CNFFormula n) :
    2*(sample formula 0*sample formula 2-sample formula 1^2)=
      ∑ left : Assignment n, ∑ right : Assignment n, (keep formula left-keep formula right)^2 := by
  simpa [sample,finitePopulationMomentResidual] using
    (finitePopulationMomentResidual_pairwise_double_sum (fun _ : Assignment n => (1 : ℚ)) (keep formula))

theorem scaled_sample {n : Nat} (formula : CNFFormula n) : sample formula (n+2)*(capacity formula : ℚ)=mass formula := by
  simp only [sample,finitePopulationAggregate,one_mul,Finset.sum_mul,mass,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro point _
  have source := weight_pow 2 (n+2) formula (extendAssignment point)
  have positive : (2 : ℚ)^formula.length ≠ 0 := by positivity
  simp only [keep,div_pow,capacity,boost,Nat.cast_pow,Nat.cast_ofNat,source]
  rw [← pow_mul,← pow_mul]
  rw [Nat.mul_comm (n+2) formula.length]
  field_simp

theorem reference_decision {n : Nat} (formula : CNFFormula n) :
    decide formula=true ↔ (1/2 : ℚ)<ForgettingChannels.sample formula (n+2) :=
  (decide_correct formula).trans (ForgettingChannels.approximate_decision formula
    (ForgettingChannels.sample formula (n+2)) (by simp)).symm

theorem keep_one_iff {n : Nat} (formula : CNFFormula n) (point : Assignment n) :
    keep formula point=1 ↔ CNFFormula.eval formula (extendAssignment point)=true := by
  have positive : 0 < 2^formula.length := by positivity
  have den : (2 : ℚ)^formula.length ≠ 0 := by positivity
  simp only [keep,div_eq_one_iff_eq den]
  constructor
  · intro equal
    have same : weight 2 formula (extendAssignment point)=2^formula.length := by exact_mod_cast equal
    by_contra rejected
    have small := weight_no 2 (by omega) formula (extendAssignment point) (Bool.eq_false_iff.mpr rejected)
    omega
  · intro accepted
    rw [weight_yes _ _ _ accepted]
    norm_cast

theorem zero_sector {n : Nat} (formula : CNFFormula n) (source : Source n) :
    (fun point => if keep formula point=1 then source point else 0)=zeroProjector formula source := by
  funext point
  simp only [keep_one_iff,zeroProjector_apply]

def clauseDriver {n : Nat} (rate : Nat) (clause : CNFClause n) : Fragment :=
  (compileClause clause).binary (Fragment.constant rate) (fun bad scaled => .select bad scaled bad)

theorem clauseDriver_eval {n : Nat} (rate : Nat) (clause : CNFClause n) (point : Nat → Bool) :
    (clauseDriver rate clause).eval point=(if CNFClause.eval clause point then rate else 1 : Nat) := by
  have inside : (compileClause clause).output.val < (run point (compileClause clause).code).size := by
    simpa only [run_size] using (compileClause clause).output.isLt
  rw [clauseDriver,Fragment.eval_binary]
  simp only [Node.run,getD_append_left _ _ _ inside]
  have right := getD_append_right (run point (compileClause clause).code) (run point (Fragment.constant rate).code) (Fragment.constant (rate : Int)).output.val
  simp only [run_size] at right
  rw [right]
  change (if (compileClause clause).eval point=0 then (Fragment.constant rate).eval point else (compileClause clause).eval point)=_
  rw [eval_compileClause,Fragment.eval_constant]
  cases CNFClause.eval clause point <;> rfl

def multiply (left right : Fragment) : Fragment := left.binary right Node.mul

theorem multiply_eval (left right : Fragment) (point : Nat → Bool) :
    (multiply left right).eval point=left.eval point*right.eval point := by
  have inside : left.output.val < (run point left.code).size := by simpa only [run_size] using left.output.isLt
  rw [multiply,Fragment.eval_binary]
  simp only [Node.run,getD_append_left _ _ _ inside]
  have shifted := getD_append_right (run point left.code) (run point right.code) right.output.val
  simp only [run_size] at shifted
  rw [shifted]
  rfl

def driver {n : Nat} (rate : Nat) : CNFFormula n → Fragment
  | [] => Fragment.constant 1
  | clause::rest => multiply (clauseDriver rate clause) (driver rate rest)

theorem driver_eval {n : Nat} (rate : Nat) (formula : CNFFormula n) (point : Nat → Bool) :
    (driver rate formula).eval point=weight rate formula point := by
  induction formula with
  | nil => simp [driver,weight]
  | cons clause rest ih => simp only [driver,multiply_eval,clauseDriver_eval,ih,weight,Nat.cast_mul]

theorem clauseDriver_size {n : Nat} (rate : Nat) (clause : CNFClause n) :
    (clauseDriver rate clause).code.size ≤ 3+3*clause.length := by
  have original := InterferenceDecision.compileClause_size clause
  simp only [clauseDriver,Fragment.binary,Fragment.constant,Array.size_push,Array.size_append,Array.size_map,Array.size_singleton]
  omega

theorem driver_size {n : Nat} (rate : Nat) (formula : CNFFormula n) :
    (driver rate formula).code.size ≤ 1+4*formula.length+3*Extract.literalCount formula := by
  induction formula with
  | nil => simp [driver,Fragment.constant,Extract.literalCount]
  | cons clause rest ih =>
      have source := clauseDriver_size rate clause
      simp only [driver,multiply,Fragment.binary,Array.size_push,Array.size_append,Array.size_map,List.length_cons]
      simp only [Extract.literalCount,List.map_cons,List.sum_cons] at ih ⊢
      omega

def sourceProgram {n : Nat} (formula : CNFFormula n) : Program := InterferenceDecision.fromAmplitude (driver (boost n) formula)

theorem sourceProgram_eval {n : Nat} (formula : CNFFormula n) (point : Nat → Bool) :
    (sourceProgram formula).eval point=weight (boost n) formula point := by
  rw [sourceProgram,InterferenceDecision.eval_fromAmplitude,driver_eval]

theorem sourceProgram_size {n : Nat} (formula : CNFFormula n) :
    (sourceProgram formula).code.size ≤ 2+4*formula.length+3*Extract.literalCount formula := by
  have original := driver_size (boost n) formula
  simp only [sourceProgram,InterferenceDecision.fromAmplitude,Array.size_push]
  omega

theorem receiver_energy {n : Nat} (formula : CNFFormula n) : energyDecision formula=true ↔
    (1 : ℚ)/4 < ((signal formula : ℚ)/(capacity formula : ℚ))^2 := by
  have positive : (0 : ℤ)<capacity formula := by exact_mod_cast capacity_pos formula
  have observed := SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.finiteADCEnergyIntegerAboveQuarter_correct
    (signal formula) (capacity formula) 0 1 positive (by omega)
  simpa only [energyDecision,Receiver,Int.cast_natCast,Int.cast_zero,Int.cast_one,zero_div,zero_pow (by omega : 2 ≠ 0),add_zero] using observed

end SaturationMonoid.ComplexityProjection.SATSource.ForgettingScalar
