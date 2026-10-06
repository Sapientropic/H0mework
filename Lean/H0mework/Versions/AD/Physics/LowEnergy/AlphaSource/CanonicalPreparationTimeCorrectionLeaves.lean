import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationTimeExactReader

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTimeReader
open PreparationVacuumLowerCorrections PreparationVacuumRationalW PreparationVacuumPrincipalBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumDensityBudget
open PreparationVacuumClockSymbol PreparationVacuumEngineSmooth PreparationVacuumEngineBudget
open PreparationVacuumCentralBudget PreparationVacuumMoyalBudget PreparationScalarCoordinates GaussHistoryHilbert
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

def sampleSymbol (F : Fin 13 → Symbol) (t : Fin 13) : Symbol := fun x => sampleValues (fun j => F j x) t

/-- The same source reader transfers a uniform sample array to each actual coefficient function. -/
theorem finite_reader_budget (F : Fin 13 → Symbol) (smooth : ∀ t,SmoothSymbol (sampleSymbol F t))
    (B : ArrayBound) (positive : ∀ m,0 ≤ B m) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (samples : ∀ t,FiniteBound (sampleSymbol F t) M B x) (j : Fin 13) :
    FiniteBound (F j) M (fun m => (originalRowFactors j : ℝ)*B m) x := by
  have same : F j=(fun y => ∑ t : Fin 13,sourceReader j t*sampleSymbol F t y) := read_original_functions F j
  intro m hm w
  rw [same,jet_sum poleDomain_open Finset.univ (fun t y => sourceReader j t*sampleSymbol F t y)
    (fun t _ => contDiffOn_const.mul (smooth t)) m w x hx]
  have scale (t : Fin 13) : jet m (fun y => sourceReader j t*sampleSymbol F t y) w x=
      sourceReader j t*jet m (sampleSymbol F t) w x :=
    PreparationVacuumEngineBudget.jet_scale _ _ (smooth t) m w x hx
  simp only [scale]
  calc
    _ ≤ ∑ t : Fin 13,|sourceReader j t*jet m (sampleSymbol F t) w x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin 13,|sourceReader j t| *B m := Finset.sum_le_sum (fun t _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (samples t m hm w) (abs_nonneg _))
    _ = (∑ t : Fin 13,|sourceReader j t|)*B m := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (reader_row_bound j) (positive m)

def actualHalfLeaves (j : Fin 13) : Symbol := fun x => originalRhoHalfLeaf j (fullCoordinates.symm x.1)
def actualQuarterLeaves (j : Fin 13) : Symbol := fun x => originalRhoQuarterLeaf j (fullCoordinates.symm x.1)

theorem half_sample_source (t : Fin 13) : sampleSymbol actualHalfLeaves t=originalRhoTimeHalf N (pointShift t) := rfl
theorem quarter_sample_source (t : Fin 13) : sampleSymbol actualQuarterLeaves t=originalRhoTimeQuarter N (pointShift t) := rfl

theorem half_sample_formula (t : Fin 13) (x : Phase) (physical : x∈originalPhysicalPhase) :
    sampleSymbol actualHalfLeaves t x=densityCorrection (partP 0 N (pointShift t)) x+
      densityCorrection (partP 1 N (pointShift t)) x := by
  rw [half_sample_source]
  have native : originalRhoTimeHalf N (pointShift t) x=
      nativeHalf (nativePart 0 N (pointShift t)) (fullCoordinates.symm x.1)+
      nativeHalf (nativePart 1 N (pointShift t)) (fullCoordinates.symm x.1) :=
    raw94_Qtime_half_extraction N (pointShift t) (actual_point_box t) ⟨_,physical⟩
  rw [native,nativeHalf_pullback _ _ _ (actual_point_box t) _ physical,
    nativeHalf_pullback _ _ _ (actual_point_box t) _ physical]

theorem quarter_sample_formula (t : Fin 13) (x : Phase) (physical : x∈originalPhysicalPhase) :
    sampleSymbol actualQuarterLeaves t x=weylCorrection (partP 0 N (pointShift t)) x+
      weylCorrection (partP 1 N (pointShift t)) x := by
  rw [quarter_sample_source]
  have native : originalRhoTimeQuarter N (pointShift t) x=
      nativeQuarter (nativePart 0 N (pointShift t)) (fullCoordinates.symm x.1)+
      nativeQuarter (nativePart 1 N (pointShift t)) (fullCoordinates.symm x.1) :=
    raw94_Qtime_quarter_extraction N (pointShift t) (actual_point_box t) ⟨_,physical⟩
  rw [native,nativeQuarter_pullback _ _ _ (actual_point_box t) _ physical,
    nativeQuarter_pullback _ _ _ (actual_point_box t) _ physical]

theorem half_sample_smooth (t : Fin 13) : SmoothSymbol (sampleSymbol actualHalfLeaves t) := by
  intro x hx
  have source := (densityCorrection_smooth _ (partP_smooth 0 N (pointShift t) (actual_point_box t))).add
    (densityCorrection_smooth _ (partP_smooth 1 N (pointShift t) (actual_point_box t)))
  have same : sampleSymbol actualHalfLeaves t=ᶠ[𝓝 x]
      (fun y => densityCorrection (partP 0 N (pointShift t)) y+densityCorrection (partP 1 N (pointShift t)) y) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact half_sample_formula t y hy.1.1
  exact (((source x hx).contDiffAt (poleDomain_open.mem_nhds hx)).congr_of_eventuallyEq same).contDiffWithinAt

theorem quarter_sample_smooth (t : Fin 13) : SmoothSymbol (sampleSymbol actualQuarterLeaves t) := by
  intro x hx
  have source := (weylCorrection_smooth _ (partP_smooth 0 N (pointShift t) (actual_point_box t))).add
    (weylCorrection_smooth _ (partP_smooth 1 N (pointShift t) (actual_point_box t)))
  have same : sampleSymbol actualQuarterLeaves t=ᶠ[𝓝 x]
      (fun y => weylCorrection (partP 0 N (pointShift t)) y+weylCorrection (partP 1 N (pointShift t)) y) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact quarter_sample_formula t y hy.1.1
  exact (((source x hx).contDiffAt (poleDomain_open.mem_nhds hx)).congr_of_eventuallyEq same).contDiffWithinAt

private theorem density_nonnegative (B : ArrayBound) (positive : ∀ m,0 ≤ B m) : ∀ m,0 ≤ densityArray B m := by
  have ell : ∀ m,0 ≤ ellArray m := fun m => by unfold ellArray; positivity
  have hess : ∀ m,0 ≤ logHArray m := fun m => by unfold logHArray; positivity
  have square := productArray_nonnegative B (powerArray ellArray 2) positive (powerArray_nonnegative ellArray ell 2)
  have drift := productArray_nonnegative (fun m => B (m+1)) ellArray (fun m => positive (m+1)) ell
  have derivative := productArray_nonnegative B logHArray positive hess
  intro m
  exact add_nonneg (add_nonneg (square m) (mul_nonneg (by positivity) (drift m)))
    (mul_nonneg (by positivity) (derivative m))

private theorem weyl_nonnegative (B : ArrayBound) (positive : ∀ m,0 ≤ B m) : ∀ m,0 ≤ weylArray B m :=
  fun m => mul_nonneg (by norm_num) (positive (m+2))

theorem original_density_nonnegative (m : ℕ) : 0 ≤ originalRhoDensityArray m :=
  add_nonneg (density_nonnegative (partArray 0) (partArray_nonnegative 0) m)
    (density_nonnegative (partArray 1) (partArray_nonnegative 1) m)

theorem original_weyl_nonnegative (m : ℕ) : 0 ≤ originalRhoWeylArray m :=
  add_nonneg (weyl_nonnegative (partArray 0) (partArray_nonnegative 0) m)
    (weyl_nonnegative (partArray 1) (partArray_nonnegative 1) m)

def originalHalfLeafArray (j : Fin 13) (m : ℕ) : ℝ := (originalRowFactors j : ℝ)*originalRhoDensityArray m
def originalQuarterLeafArray (j : Fin 13) (m : ℕ) : ℝ := (originalRowFactors j : ℝ)*originalRhoWeylArray m

theorem actual_half_leaf_budget (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x) (inputs : CoefficientInputs x (M+2)) (j : Fin 13) :
    FiniteBound (actualHalfLeaves j) M (originalHalfLeafArray j) x := by
  apply finite_reader_budget actualHalfLeaves half_sample_smooth originalRhoDensityArray original_density_nonnegative M x hx _ j
  intro t
  rw [half_sample_source]
  exact actual_rho_half_budget N (pointShift t) (actual_point_box t) M x hx box inputs

theorem actual_quarter_leaf_budget (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x) (inputs : CoefficientInputs x (M+2)) (j : Fin 13) :
    FiniteBound (actualQuarterLeaves j) M (originalQuarterLeafArray j) x := by
  apply finite_reader_budget actualQuarterLeaves quarter_sample_smooth originalRhoWeylArray original_weyl_nonnegative M x hx _ j
  intro t
  rw [quarter_sample_source]
  exact actual_rho_quarter_budget N (pointShift t) (actual_point_box t) M x hx box inputs

end LowEnergy.PreparationVacuumTimeReader
