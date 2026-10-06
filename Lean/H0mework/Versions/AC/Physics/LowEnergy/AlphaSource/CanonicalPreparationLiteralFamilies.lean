import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralBoundsMonotone

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLiteralAdmission
open PreparationVacuumCentralBudget PreparationVacuumPrincipalBudget PreparationVacuumReciprocalBudget
open PreparationVacuumLowerClassical PreparationVacuumRationalW PreparationVacuumLowerCorrections
open PreparationVacuumCoframeBudget PreparationVacuumTimeReader
open scoped BigOperators

-- All12 original broken/stabilizer matter generators have entry-ceiling
-- row/column norm1; CAR_MODES is the original504 in all_leaf_bounds.
def literalChargeSum : ℝ := 504*12

def literalScalarCurrent : ArrayBound := fun m =>
  3*productArray originalFArray (fun n => constantArray 1 n+productArray originalBArray originalUArray n) m
def literalScalarShift : ArrayBound := fun m => 3*productArray shiftArray literalUi m
def literalGaugeShift : ArrayBound := originalGaugeShiftArray
def literalScalarC : ArrayBound := fun m => literalScalarCurrent m*literalChargeSum+literalScalarShift m
def literalGaugeC : ArrayBound := fun m => originalUArray m*literalChargeSum+literalGaugeShift m

def literalScalarPotential : ArrayBound := fun m =>
  productArray (fun k => 2*volumeBudget k) (powerArray literalSigma 2) m+
    (9/2 : ℝ)*productArray metricArray (powerArray literalUi 2) m
def literalGaugePotential : ArrayBound := fun m =>
  54*productArray magneticMetricArray (powerArray magneticFieldArray 2) m

def literalScalarFirst : ArrayBound := productArray
  (productArray (productArray p94Array scalarFactorArray) scalarWArray) literalScalarC
def literalGaugeFirst : ArrayBound := productArray
  (productArray (productArray p94Array gaugeFactorArray) gaugeWArray) literalGaugeC
def literalScalarClassical : ArrayBound := fun m =>
  (1/2 : ℝ)*productArray scalarWArray (powerArray literalScalarC 2) m+literalScalarPotential m
def literalGaugeClassical : ArrayBound := fun m =>
  (1/2 : ℝ)*productArray gaugeWArray (powerArray literalGaugeC 2) m+literalGaugePotential m

def literalScalarZero : ArrayBound := fun m =>
  literalScalarClassical m+densityArray scalarPArray m+weylArray scalarPArray m
def literalGaugeZero : ArrayBound := fun m =>
  literalGaugeClassical m+densityArray gaugePArray m+weylArray gaugePArray m

theorem literal_F_nonnegative : Nonnegative originalFArray :=
  inverseBudget_nonnegative originalDArray _ (by positivity)
    (affine_nonnegative 98928 108 (by norm_num) (by norm_num))
theorem literal_U_nonnegative : Nonnegative originalUArray :=
  inverseBudget_nonnegative originalMArray _ (by positivity)
    (affine_nonnegative 14550 10 (by norm_num) (by norm_num))
theorem literal_B_nonnegative : Nonnegative originalBArray :=
  affine_nonnegative 32010 22 (by norm_num) (by norm_num)

theorem shift_nonnegative : Nonnegative shiftArray := fun _ => Nat.cast_nonneg _
theorem mixed_nonnegative : Nonnegative mixedArray := fun _ => Nat.cast_nonneg _
theorem metric_nonnegative : Nonnegative metricArray := fun _ => Nat.cast_nonneg _
theorem magneticMetric_nonnegative : Nonnegative magneticMetricArray := fun _ => Nat.cast_nonneg _
theorem volume_nonnegative : Nonnegative volumeBudget := fun _ => Nat.cast_nonneg _
theorem scalarW_nonnegative : Nonnegative scalarWArray := fun m =>
  mul_nonneg (by norm_num) (Nat.cast_nonneg _)
theorem gaugeW_nonnegative : Nonnegative gaugeWArray := fun m =>
  mul_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem literalScalarCurrent_nonnegative : Nonnegative literalScalarCurrent :=
  scale_nonnegative 3 (by norm_num) _ (product_nonnegative _ _ literal_F_nonnegative
    (add_nonnegative _ _ (constant_nonnegative 1 (by norm_num))
      (product_nonnegative _ _ literal_B_nonnegative literal_U_nonnegative)))

theorem literalScalarShift_nonnegative : Nonnegative literalScalarShift :=
  scale_nonnegative 3 (by norm_num) _ (product_nonnegative _ _ shift_nonnegative literalUi_nonnegative)

theorem literalGaugeShift_nonnegative : Nonnegative literalGaugeShift :=
  scale_nonnegative 108 (by norm_num) _ (product_nonnegative _ _ mixed_nonnegative magneticFieldArray_nonnegative)

theorem literalScalarC_nonnegative : Nonnegative literalScalarC := fun m =>
  _root_.add_nonneg (mul_nonneg (literalScalarCurrent_nonnegative m) (by norm_num [literalChargeSum]))
    (literalScalarShift_nonnegative m)
theorem literalGaugeC_nonnegative : Nonnegative literalGaugeC := fun m =>
  _root_.add_nonneg (mul_nonneg (literal_U_nonnegative m) (by norm_num [literalChargeSum]))
    (literalGaugeShift_nonnegative m)

theorem source_scalar_shift_admission : Dominates originalScalarShiftArray literalScalarShift :=
  scale_mono 3 (by norm_num) _ _ (product_mono _ _ _ _ shift_nonnegative UiArray_nonnegative
    (fun _ => le_rfl) source_Ui_admission)

theorem source_scalar_C_admission : Dominates originalScalarShiftArray literalScalarC := by
  intro m
  exact (source_scalar_shift_admission m).trans (le_add_of_nonneg_left
    (mul_nonneg (literalScalarCurrent_nonnegative m) (by norm_num [literalChargeSum])))

theorem source_gauge_C_admission : Dominates originalGaugeShiftArray literalGaugeC := by
  intro m
  exact le_add_of_nonneg_left (mul_nonneg (literal_U_nonnegative m) (by norm_num [literalChargeSum]))

theorem scalar_shift_nonnegative : Nonnegative originalScalarShiftArray :=
  scale_nonnegative 3 (by norm_num) _ (product_nonnegative _ _ shift_nonnegative UiArray_nonnegative)

theorem source_scalar_potential_admission : Dominates scalarClassicalArray literalScalarPotential := by
  apply add_mono
  · exact product_mono _ _ _ _ (scale_nonnegative 2 (by norm_num) _ volume_nonnegative)
      (power_nonnegative _ (affine_nonnegative 915 1 (by norm_num) (by norm_num)) 2)
      (fun _ => le_rfl) (power_mono _ _ (affine_nonnegative 915 1 (by norm_num) (by norm_num)) source_sigma_admission 2)
  · exact scale_mono (9/2 : ℝ) (by norm_num) _ _ (product_mono _ _ _ _ metric_nonnegative
      (power_nonnegative _ UiArray_nonnegative 2) (fun _ => le_rfl)
      (power_mono _ _ UiArray_nonnegative source_Ui_admission 2))

theorem source_scalar_classical_admission : Dominates originalScalarClassicalArray literalScalarClassical := by
  apply add_mono
  · exact scale_mono (1/2 : ℝ) (by norm_num) _ _ (product_mono _ _ _ _ scalarW_nonnegative
      (power_nonnegative _ scalar_shift_nonnegative 2) (fun _ => le_rfl)
      (power_mono _ _ scalar_shift_nonnegative source_scalar_C_admission 2))
  · exact source_scalar_potential_admission

theorem source_gauge_classical_admission : Dominates originalGaugeClassicalArray literalGaugeClassical := by
  apply add_mono
  · exact scale_mono (1/2 : ℝ) (by norm_num) _ _ (product_mono _ _ _ _ gaugeW_nonnegative
      (power_nonnegative _ literalGaugeShift_nonnegative 2) (fun _ => le_rfl)
      (power_mono _ _ literalGaugeShift_nonnegative source_gauge_C_admission 2))
  · exact fun _ => le_rfl

theorem scalar_first_left_nonnegative : Nonnegative
    (productArray (productArray p94Array scalarFactorArray) scalarWArray) :=
  product_nonnegative _ _ (product_nonnegative _ _ (affine_nonnegative 188 1 (by norm_num) (by norm_num))
    scalarFactor_nonnegative) scalarW_nonnegative
theorem gauge_first_left_nonnegative : Nonnegative
    (productArray (productArray p94Array gaugeFactorArray) gaugeWArray) :=
  product_nonnegative _ _ (product_nonnegative _ _ (affine_nonnegative 188 1 (by norm_num) (by norm_num))
    gaugeFactor_nonnegative) gaugeW_nonnegative

theorem source_scalar_first_admission : Dominates originalScalarFirstArray literalScalarFirst :=
  product_mono _ _ _ _ scalar_first_left_nonnegative scalar_shift_nonnegative
    (fun _ => le_rfl) source_scalar_C_admission
theorem source_gauge_first_admission : Dominates originalGaugeFirstArray literalGaugeFirst :=
  product_mono _ _ _ _ gauge_first_left_nonnegative literalGaugeShift_nonnegative
    (fun _ => le_rfl) source_gauge_C_admission

theorem source_first_admission : Dominates firstSampleArray (fun m => literalScalarFirst m+literalGaugeFirst m) := by
  intro m
  exact (original_first_admission m).trans
    (add_le_add (source_scalar_first_admission m) (source_gauge_first_admission m))

theorem source_classical_admission : Dominates classicalSampleArray
    (fun m => literalScalarClassical m+literalGaugeClassical m+6*volumeBudget m) := by
  intro m
  exact (original_classical_admission m).trans (add_le_add
    (add_le_add (source_scalar_classical_admission m) (source_gauge_classical_admission m)) (le_refl _))

theorem literalScalarPotential_nonnegative : Nonnegative literalScalarPotential :=
  add_nonnegative _ _ (product_nonnegative _ _ (scale_nonnegative 2 (by norm_num) _ volume_nonnegative)
    (power_nonnegative _ literalSigma_nonnegative 2))
    (scale_nonnegative (9/2 : ℝ) (by norm_num) _ (product_nonnegative _ _ metric_nonnegative
      (power_nonnegative _ literalUi_nonnegative 2)))
theorem literalGaugePotential_nonnegative : Nonnegative literalGaugePotential :=
  scale_nonnegative 54 (by norm_num) _ (product_nonnegative _ _ magneticMetric_nonnegative
    (power_nonnegative _ magneticFieldArray_nonnegative 2))
theorem literalScalarClassical_nonnegative : Nonnegative literalScalarClassical :=
  add_nonnegative _ _ (scale_nonnegative (1/2 : ℝ) (by norm_num) _ (product_nonnegative _ _ scalarW_nonnegative
    (power_nonnegative _ literalScalarC_nonnegative 2))) literalScalarPotential_nonnegative
theorem literalGaugeClassical_nonnegative : Nonnegative literalGaugeClassical :=
  add_nonnegative _ _ (scale_nonnegative (1/2 : ℝ) (by norm_num) _ (product_nonnegative _ _ gaugeW_nonnegative
    (power_nonnegative _ literalGaugeC_nonnegative 2))) literalGaugePotential_nonnegative
theorem literalScalarFirst_nonnegative : Nonnegative literalScalarFirst :=
  product_nonnegative _ _ scalar_first_left_nonnegative literalScalarC_nonnegative
theorem literalGaugeFirst_nonnegative : Nonnegative literalGaugeFirst :=
  product_nonnegative _ _ gauge_first_left_nonnegative literalGaugeC_nonnegative

theorem density_nonnegative (P : ArrayBound) (hp : Nonnegative P) : Nonnegative (densityArray P) := by
  have ell : Nonnegative PreparationVacuumDensityBudget.ellArray := fun m => by
    unfold PreparationVacuumDensityBudget.ellArray; positivity
  have logH : Nonnegative PreparationVacuumDensityBudget.logHArray := fun m => by
    unfold PreparationVacuumDensityBudget.logHArray; positivity
  exact add_nonnegative _ _ (add_nonnegative _ _
    (product_nonnegative _ _ hp (power_nonnegative _ ell 2))
    (scale_nonnegative (94^2 : ℝ) (by positivity) _ (product_nonnegative _ _ (fun m => hp (m+1)) ell)))
    (scale_nonnegative (94^2 : ℝ) (by positivity) _ (product_nonnegative _ _ hp logH))
theorem weyl_nonnegative (P : ArrayBound) (hp : Nonnegative P) : Nonnegative (weylArray P) :=
  fun m => mul_nonneg (by positivity) (hp (m+2))

theorem literalScalarZero_nonnegative : Nonnegative literalScalarZero :=
  add_nonnegative _ _ (add_nonnegative _ _ literalScalarClassical_nonnegative
    (density_nonnegative _ (partArray_nonnegative 0))) (weyl_nonnegative _ (partArray_nonnegative 0))
theorem literalGaugeZero_nonnegative : Nonnegative literalGaugeZero :=
  add_nonnegative _ _ (add_nonnegative _ _ literalGaugeClassical_nonnegative
    (density_nonnegative _ (partArray_nonnegative 1))) (weyl_nonnegative _ (partArray_nonnegative 1))

theorem source_zero_core_admission (m : ℕ) :
    classicalSampleArray m+originalRhoDensityArray m+originalRhoWeylArray m ≤
      literalScalarZero m+literalGaugeZero m+6*volumeBudget m := by
  have bound := source_classical_admission m
  unfold literalScalarZero literalGaugeZero originalRhoDensityArray originalRhoWeylArray
  linarith

end LowEnergy.PreparationVacuumLiteralAdmission
