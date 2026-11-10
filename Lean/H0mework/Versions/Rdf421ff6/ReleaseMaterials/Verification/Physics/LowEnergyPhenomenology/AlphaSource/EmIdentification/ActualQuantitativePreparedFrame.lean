import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldFullVertex
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationPreparedCurrentRead
import Mathlib.Algebra.Order.Ring.Pow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.FullYBinarySchedule

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.ActualQuantitativePreparedFrameOwn
open PreparationVacuumFullFieldRiesz PreparationVacuumSourcePreparedResponse
open PreparationVacuumSourcePreparedState PreparationVacuumFieldConstraintResponse
open PreparationVacuumMixedFieldReturn CanonicalPhysicalSpatial
open CanonicalGradedSpatialSource
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard PreparationScalarCoordinates GaussComposite.SourceGraph GaussCoreHilbert
open scoped InnerProductSpace BigOperators Topology
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

def localScale : ℝ := localBound (outerCutoff actualNativeLocalizer)
def legScale : ℝ := legBound * localScale
def actualLeg (epsilon : ℝ) (precision : 0 < epsilon) (addition : Bool) (a s : Fin 2) : H :=
  completedLeg addition a s (sourceProfile epsilon precision)
def actualPrepared (epsilon : ℝ) (precision : 0 < epsilon) : H :=
  prepared (sourceProfile epsilon precision)
def actualFullY (epsilon : ℝ) (precision : 0 < epsilon) : H :=
  GaussRadialDomain.closedY ⟨actualPrepared epsilon precision,
    (sourcePreparation epsilon precision).yukawaDomain⟩
def fullYError (n : ℕ) : ℝ :=
  (915 / 916 : ℝ) ^ (n + 1) * 916 * GaussYukawaCoefficient.bound

theorem localScale_nonnegative : 0 ≤ localScale := localBound_nonnegative _
theorem legScale_nonnegative : 0 ≤ legScale := by
  unfold legScale
  exact mul_nonneg (by norm_num [legBound]) localScale_nonnegative

theorem legScale_source_value : legScale = 3 * localScale := by
  simp only [legScale, legBound, seed_unit, mul_one]

theorem actualLeg_bound (epsilon : ℝ) (precision : 0 < epsilon)
    (addition : Bool) (a s : Fin 2) : ‖actualLeg epsilon precision addition a s‖ ≤ legScale :=
  (sourcePreparation epsilon precision).legs addition a s

theorem actualPrepared_norm (epsilon : ℝ) (precision : 0 < epsilon) :
    ‖actualPrepared epsilon precision‖ = 1 := (sourcePreparation epsilon precision).unit

theorem frameVector_bound (F : GaussUnitaryHistory.Index) (i : FrameIndex F) :
    ‖frameVector F i‖ ≤ 1 := by
  exact (NativeHistoryGrade.piece_bound i.1 _).trans (le_of_eq ((sourceBasis F).norm_eq_one i.2))

def actualMoment (epsilon : ℝ) (precision : 0 < epsilon) (F : GaussUnitaryHistory.Index)
    (addition : Bool) (a s : Fin 2) (i : FrameIndex F) : ℂ :=
  inner ℂ (frameVector F i) (actualLeg epsilon precision addition a s)

theorem actualMoment_bound (epsilon : ℝ) (precision : 0 < epsilon) (F : GaussUnitaryHistory.Index)
    (addition : Bool) (a s : Fin 2) (i : FrameIndex F) :
    ‖actualMoment epsilon precision F addition a s i‖ ≤ legScale := by
  exact (norm_inner_le_norm _ _).trans
    ((mul_le_mul (frameVector_bound F i) (actualLeg_bound epsilon precision addition a s)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))

theorem actual_projection_bound (epsilon : ℝ) (precision : 0 < epsilon)
    (F : GaussUnitaryHistory.Index) (addition : Bool) (a s : Fin 2) :
    ‖sourceApprox F (actualLeg epsilon precision addition a s)‖ ≤ legScale :=
  (PreparationVacuumPreparedCurrent.sourceApprox_contractive F _).trans
    (actualLeg_bound epsilon precision addition a s)

theorem frameMoment_mass (F : GaussUnitaryHistory.Index) (x : H) :
    ∑ i : FrameIndex F, ‖inner ℂ (frameVector F i) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have identity : inner ℂ x (sourceApprox F x) =
      ((∑ i : FrameIndex F, ‖inner ℂ (frameVector F i) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [sourceApprox_frame, inner_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right, ← inner_conj_symm x (frameVector F i)]
    exact RCLike.mul_conj _
  have nonnegative : 0 ≤ ∑ i : FrameIndex F, ‖inner ℂ (frameVector F i) x‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  calc
    _ = ‖inner ℂ x (sourceApprox F x)‖ := by
      rw [identity, Complex.norm_real, Real.norm_of_nonneg nonnegative]
    _ ≤ ‖x‖ * ‖sourceApprox F x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_left
      (PreparationVacuumPreparedCurrent.sourceApprox_contractive F x) (norm_nonneg _)
    _ = _ := by ring

theorem actualMoment_mass (epsilon : ℝ) (precision : 0 < epsilon)
    (F : GaussUnitaryHistory.Index) (addition : Bool) (a s : Fin 2) :
    ∑ i : FrameIndex F, ‖actualMoment epsilon precision F addition a s i‖ ^ 2 ≤
      9 * localScale ^ 2 := by
  have mass := frameMoment_mass F (actualLeg epsilon precision addition a s)
  have bound := pow_le_pow_left₀ (norm_nonneg _) (actualLeg_bound epsilon precision addition a s) 2
  have same : legScale ^ 2 = 9 * localScale ^ 2 := by rw [legScale_source_value]; ring
  exact (mass.trans bound).trans_eq same

-- The price is computed from the original field matrix (physicalAction + original Y).
def originalFormPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  finitePrice F (fieldMatrix f p F 0)

theorem originalFormPrice_nonnegative (f : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : 0 ≤ originalFormPrice f p F := finitePrice_nonnegative F _

theorem actual_pair_bound (epsilon : ℝ) (precision : 0 < epsilon)
    (A : H →L[ℂ] H) (P : ℝ) (price : ‖A‖ ≤ P)
    (left right : Bool) (a s b t : Fin 2) :
    ‖inner ℂ (actualLeg epsilon precision left a s)
      (A (actualLeg epsilon precision right b t))‖ ≤ legScale ^ 2 * P := by
  have hP : 0 ≤ P := (norm_nonneg A).trans price
  have leftB := actualLeg_bound epsilon precision left a s
  have rightB := actualLeg_bound epsilon precision right b t
  calc
    _ ≤ ‖actualLeg epsilon precision left a s‖ * P * ‖actualLeg epsilon precision right b t‖ :=
      vertex_pair_price A P price _ _
    _ ≤ legScale * P * legScale := mul_le_mul
      (mul_le_mul_of_nonneg_right leftB hP) rightB (norm_nonneg _)
      (mul_nonneg legScale_nonnegative hP)
    _ = _ := by ring

theorem actual_original_form_bound (epsilon : ℝ) (precision : 0 < epsilon)
    (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (left right : Bool) (a s b t : Fin 2) :
    ‖GaussFockPair.sourcePair
      (sourceTestApprox F (actualLeg epsilon precision left a s))
      ((physicalAction p + GaussYukawaOperator.originalAction)
        (sourceTestApprox F (actualLeg epsilon precision right b t)))‖ ≤
      legScale ^ 2 * originalFormPrice f p F := by
  rw [← formRestriction_original_pair f p F]
  exact actual_pair_bound epsilon precision _ _ (finiteRiesz_price F _) left right a s b t

theorem actual_original_form_power_moment (epsilon : ℝ) (precision : 0 < epsilon)
    (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (k : ℕ)
    (left right : Bool) (a s b t : Fin 2) :
    ‖inner ℂ (actualLeg epsilon precision left a s)
      (((formRestriction f p F 0) ^ k) (actualLeg epsilon precision right b t))‖ ≤
      legScale ^ 2 * (originalFormPrice f p F) ^ k := by
  cases k with
  | zero =>
    simpa only [pow_zero, one_apply_eq_self, ContinuousLinearMap.id_apply, mul_one] using
      actual_pair_bound epsilon precision (ContinuousLinearMap.id ℂ H) 1
        ContinuousLinearMap.norm_id_le left right a s b t
  | succ k =>
    exact actual_pair_bound epsilon precision _ _
      ((norm_pow_le' _ (Nat.succ_pos k)).trans (pow_le_pow_left₀ (norm_nonneg _)
        (finiteRiesz_price F _) (k + 1))) left right a s b t

theorem actualFullY_error (epsilon : ℝ) (precision : 0 < epsilon) (n : ℕ) :
    ‖actualFullY epsilon precision - FullYSourceCutoffVolterra.cutoff n
      (actualPrepared epsilon precision)‖ ≤ fullYError n :=
  (sourcePreparation epsilon precision).yukawaCutoff n

theorem fullYError_binary (bits : ℕ) :
    fullYError (916 * bits) ≤ 916 * GaussYukawaCoefficient.bound * (1 / 2 : ℝ) ^ bits := by
  unfold fullYError
  calc
    _ ≤ (1 / 2 : ℝ) ^ bits * 916 * GaussYukawaCoefficient.bound :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (fullY_binary_schedule bits) (by norm_num))
        GaussYukawaCoefficient.bound_nonneg
    _ = _ := by ring

theorem actualFullY_binary_error (epsilon : ℝ) (precision : 0 < epsilon) (bits : ℕ) :
    ‖actualFullY epsilon precision - FullYSourceCutoffVolterra.cutoff (916 * bits)
      (actualPrepared epsilon precision)‖ ≤
      916 * GaussYukawaCoefficient.bound * (1 / 2 : ℝ) ^ bits :=
  (actualFullY_error epsilon precision _).trans (fullYError_binary bits)

theorem actualFullY_projected_error (epsilon : ℝ) (precision : 0 < epsilon)
    (F : GaussUnitaryHistory.Index) (n : ℕ) :
    ‖sourceApprox F (actualFullY epsilon precision) - sourceApprox F
      (FullYSourceCutoffVolterra.cutoff n (actualPrepared epsilon precision))‖ ≤ fullYError n := by
  rw [← map_sub]
  exact (PreparationVacuumPreparedCurrent.sourceApprox_contractive F _).trans
    (actualFullY_error epsilon precision n)

theorem actualFullY_original_form_error (epsilon : ℝ) (precision : 0 < epsilon)
    (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (left : Bool) (a s : Fin 2) :
    ‖inner ℂ (actualLeg epsilon precision left a s)
        (formRestriction f p F 0 (actualFullY epsilon precision)) -
      inner ℂ (actualLeg epsilon precision left a s)
        (formRestriction f p F 0 (FullYSourceCutoffVolterra.cutoff n
          (actualPrepared epsilon precision)))‖ ≤
      legScale * originalFormPrice f p F * fullYError n := by
  rw [← inner_sub_right, ← map_sub]
  have hP := originalFormPrice_nonnegative f p F
  calc
    _ ≤ ‖actualLeg epsilon precision left a s‖ * originalFormPrice f p F *
        ‖actualFullY epsilon precision - FullYSourceCutoffVolterra.cutoff n
          (actualPrepared epsilon precision)‖ :=
      vertex_pair_price _ _ (finiteRiesz_price F _) _ _
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_right (actualLeg_bound epsilon precision left a s) hP)
      (actualFullY_error epsilon precision n) (norm_nonneg _)
      (mul_nonneg legScale_nonnegative hP)

theorem actualFullY_original_form_binary_error (epsilon : ℝ) (precision : 0 < epsilon)
    (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (bits : ℕ) (left : Bool) (a s : Fin 2) :
    ‖inner ℂ (actualLeg epsilon precision left a s)
        (formRestriction f p F 0 (actualFullY epsilon precision)) -
      inner ℂ (actualLeg epsilon precision left a s)
        (formRestriction f p F 0 (FullYSourceCutoffVolterra.cutoff (916 * bits)
          (actualPrepared epsilon precision)))‖ ≤
      2748 * localScale * originalFormPrice f p F * GaussYukawaCoefficient.bound *
        (1 / 2 : ℝ) ^ bits := by
  have h := (actualFullY_original_form_error epsilon precision f p F (916 * bits) left a s).trans
    (mul_le_mul_of_nonneg_left (fullYError_binary bits)
      (mul_nonneg legScale_nonnegative (originalFormPrice_nonnegative f p F)))
  rw [legScale_source_value] at h
  calc
    _ ≤ (3 * localScale) * originalFormPrice f p F *
        (916 * GaussYukawaCoefficient.bound * (1 / 2 : ℝ) ^ bits) := h
    _ = _ := by ring

end LowEnergy.ActualQuantitativePreparedFrameOwn
