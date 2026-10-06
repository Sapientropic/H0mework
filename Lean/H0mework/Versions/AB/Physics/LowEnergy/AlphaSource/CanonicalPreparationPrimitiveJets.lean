import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaugeInverse
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoframeOriginal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPrimitiveMatrix
open SaturationMonoid.PhysicsCore
open PreparationScalarCoordinates PreparationCoordinates PreparationChartGuard
open PreparationVacuumSourceChartBudget PreparationVacuumSourceMatrixInverse
open PreparationVacuumCoframeBudget CanonicalPreparationCutoff
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open GaussHistoryHilbert
open scoped BigOperators

def phaseCoordinate (i : Fin 100) : Phase →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

def originalM (i j : Fin 3) : Symbol := fun x => sourceOrbitMinor (fullCoordinates.symm x.1) i j

def linearM : Matrix (Fin 3) (Fin 3) (Phase →L[ℝ] ℝ) :=
  !![0,-phaseCoordinate 72,2 • phaseCoordinate 67;
     2 • phaseCoordinate 67,0,0;
     2 • phaseCoordinate 78,-(2 • phaseCoordinate 77),0]

theorem originalM_readback (x : Phase) (i j : Fin 3) : originalM i j x=linearM i j x := by
  unfold originalM
  rw [sourceOrbitMinor_native]
  have coords (c : Fin 3) :
      nativeCoordinates (gaugeCoordinates (fullCoordinates.symm x.1).2.2.val c)=
        (![insertFree (splitCoordinates x.1).2.2 (⟨12*c.val,by omega⟩),
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+1,by omega⟩),
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+2,by omega⟩),
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+3,by omega⟩),
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+4,by omega⟩),
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+5,by omega⟩),
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+6,by omega⟩),
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+6,by omega⟩)+
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+7,by omega⟩)],
         ![insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+8,by omega⟩),
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+9,by omega⟩),
           insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+10,by omega⟩)],
         insertFree (splitCoordinates x.1).2.2 (⟨12*c.val+11,by omega⟩)) := by
    change nativeCoordinates (gaugeCoordinates (gaugeBuild (insertFree (splitCoordinates x.1).2.2)) c)=_
    simp [gaugeBuild,rawCoordinates,rawBuild,combinedRow]
  unfold firstGauge secondGauge
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  rw [coords 0,coords 1]
  fin_cases i <;> fin_cases j <;>
    norm_num [linearM,phaseCoordinate,insertFree,splitCoordinates]
  all_goals rfl

@[simp] theorem phaseCoordinate_direction (i : Fin 100) (s : Slot) :
    phaseCoordinate i (slotDirection s)=if s=(i,false) then 1 else 0 := by
  rcases s with ⟨j,b⟩
  cases b <;> simp [phaseCoordinate,slotDirection,Pi.single_apply,eq_comm]

theorem linear_jet_one (f : Phase →L[ℝ] ℝ) (w : Word 1) (x : Phase) :
    jet 1 f w x=f (slotDirection (w 0)) := by
  simp [jet,ContinuousLinearMap.fderiv]

theorem linear_jet_higher (f : Phase →L[ℝ] ℝ) (n : ℕ) (w : Word (n+2)) (x : Phase) :
    jet (n+2) f w x=0 := by
  unfold jet
  rw [iteratedFDeriv_succ_apply_right]
  simp only [ContinuousLinearMap.fderiv]
  rw [iteratedFDeriv_const_of_ne (by omega)]
  simp

theorem originalM_jet_higher (n : ℕ) (w : Word (n+2)) (x : Phase) (i j : Fin 3) :
    jet (n+2) (originalM i j) w x=0 := by
  rw [show originalM i j=(linearM i j : Phase→ℝ) by funext y; exact originalM_readback y i j]
  exact linear_jet_higher _ _ _ _


theorem linearM_budget (x : Phase) (B : ℝ) (positive : 0≤B)
    (coordinate : ∀ i,|phaseCoordinate i x|≤B) :
    (∀ i,∑ j,|linearM i j x|≤4*B) ∧ (∀ j,∑ i,|linearM i j x|≤4*B) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [linearM,Fin.sum_univ_succ,abs_mul] <;>
      nlinarith [coordinate 67,coordinate 72,coordinate 77,coordinate 78]
  · intro j
    fin_cases j <;> norm_num [linearM,Fin.sum_univ_succ,abs_mul] <;>
      nlinarith [coordinate 67,coordinate 72,coordinate 77,coordinate 78]

theorem source_coordinate_j15 (x : Phase) (box : x.1∈sourceClosedBox) (i : Fin 100) :
    |phaseCoordinate i x|≤15 := by
  have center : |flatSource i|≤1 := by
    have hp:=Real.sqrt_nonneg (2 : ℝ)
    have hs:=Real.sq_sqrt (show (0 : ℝ)≤2 by norm_num)
    unfold flatSource
    split_ifs <;> try simp only [abs_one,abs_zero,abs_neg]
    all_goals try norm_num
    all_goals rw [abs_of_nonneg (by positivity)]
    all_goals nlinarith
  have difference := box i
  have triangle : |x.1 i|≤|x.1 i-flatSource i|+|flatSource i| := by
    simpa using abs_add_le (x.1 i-flatSource i) (flatSource i)
  change |x.1 i|≤15
  linarith [radius_small.2]

/-- Original integer arrays before the JSON power-of-two compression. -/
theorem originalM_jet_one (w : Word 1) (x : Phase) (i j : Fin 3) :
    jet 1 (originalM i j) w x=linearM i j (slotDirection (w 0)) := by
  rw [show originalM i j=(linearM i j : Phase→ℝ) by funext y; exact originalM_readback y i j]
  exact linear_jet_one _ _ _

def originalMArray : ℕ→ℕ | 0=>14550 | 1=>10 | _=>0

theorem actual_M3_row_budget (n : ℕ) (w : Word n) (x : Phase)
    (box : x.1∈sourceClosedBox) (i : Fin 3) :
    (∑ j,|jet n (originalM i j) w x|)≤(originalMArray n : ℝ) := by
  cases n with
  | zero =>
    simp only [jet,iteratedFDeriv_zero_apply,originalM_readback]
    exact ((linearM_budget x 15 (by norm_num) (source_coordinate_j15 x box)).1 i).trans (by norm_num [originalMArray])
  | succ n =>
    cases n with
    | zero =>
      have equal : (∑ j,|jet 1 (originalM i j) w x|)=∑ j,|linearM i j (slotDirection (w 0))| :=
        Finset.sum_congr rfl (fun j _ => congrArg abs (originalM_jet_one w x i j))
      rw [equal]
      refine ((linearM_budget (slotDirection (w 0)) 1 (by norm_num) ?_).1 i).trans (by norm_num [originalMArray])
      intro k
      simp only [phaseCoordinate_direction]
      split_ifs <;> norm_num
    | succ n =>
      simp [originalM_jet_higher,originalMArray]

theorem actual_M3_column_budget (n : ℕ) (w : Word n) (x : Phase)
    (box : x.1∈sourceClosedBox) (j : Fin 3) :
    (∑ i,|jet n (originalM i j) w x|)≤(originalMArray n : ℝ) := by
  cases n with
  | zero =>
    simp only [jet,iteratedFDeriv_zero_apply,originalM_readback]
    exact ((linearM_budget x 15 (by norm_num) (source_coordinate_j15 x box)).2 j).trans (by norm_num [originalMArray])
  | succ n =>
    cases n with
    | zero =>
      have equal : (∑ i,|jet 1 (originalM i j) w x|)=∑ i,|linearM i j (slotDirection (w 0))| :=
        Finset.sum_congr rfl (fun i _ => congrArg abs (originalM_jet_one w x i j))
      rw [equal]
      refine ((linearM_budget (slotDirection (w 0)) 1 (by norm_num) ?_).2 j).trans (by norm_num [originalMArray])
      intro k
      simp only [phaseCoordinate_direction]
      split_ifs <;> norm_num
    | succ n =>
      simp [originalM_jet_higher,originalMArray]

end LowEnergy.PreparationVacuumPrimitiveMatrix
