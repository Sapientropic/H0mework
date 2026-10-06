import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMaterialResponseSuppression

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentRegularAnchor
open PreparationVacuumCurrentConstrainedInverse PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldConstraintResponse PreparationVacuumPhysicalTailPrice PreparationVacuumActionFieldLift
open PreparationVacuumRawJointFeedback
open scoped BigOperators Topology Matrix
attribute [local irreducible] sourceGreen sourceTemporalFirst sourceTemporalSecond originalJacobi sourceCurrentUpdateMatrix
  sourceRead factorialBudget rawReader sourceBaseGenerator sourceLaplaceCurrent sourceLaplaceInitial

private def nativeMatrix (A : Matrix (Fin 289) (Fin 289) ℂ) : SignalAmplitude→L[ℝ] SignalAmplitude:=
  ContinuousLinearMap.pi (fun i=>∑j : Fin 289,A i j • (ContinuousLinearMap.proj j : SignalAmplitude→L[ℝ] ℂ))

private theorem nativeMatrix_actual (A : Matrix (Fin 289) (Fin 289) ℂ) (a : SignalAmplitude) :
    nativeMatrix A a=A*ᵥa :=by
  ext i
  simp only [nativeMatrix,ContinuousLinearMap.pi_apply,sum_apply,smul_apply,ContinuousLinearMap.proj_apply,
    smul_eq_mul,Matrix.mulVec,dotProduct]

def sourceZeroTransfer (q : PhysicalResponsePoint) : PhysicalResponsePoint:={q with k:=0}

def sourceInitialBudget : ℝ:=‖nativeMatrix (sourceGreen generatedRegularPoint)‖*
  (‖nativeMatrix (sourceTemporalFirst 0)‖+6*‖nativeMatrix sourceTemporalSecond‖)

def sourceAnchorGap : ℝ:=1/(8*(1+sourceInitialBudget))

def sourceAnchorClock : ℂ:=((3-sourceAnchorGap : ℝ) : ℂ)

def sourceAnchorEta : ℝ:=sourceAnchorGap/16

theorem sourceInitialBudget_nonnegative : 0 ≤ sourceInitialBudget :=by
  unfold sourceInitialBudget
  positivity

theorem sourceAnchorGap_positive : 0<sourceAnchorGap :=by
  unfold sourceAnchorGap
  have source:=sourceInitialBudget_nonnegative
  positivity

theorem sourceAnchorGap_small : sourceAnchorGap ≤ 1/8 :=by
  unfold sourceAnchorGap
  have source:=sourceInitialBudget_nonnegative
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

theorem sourceAnchorClock_growth (q : PhysicalResponsePoint) :
    sourceClockGrowth (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourceZeroTransfer q).k) sourceAnchorClock)=3-sourceAnchorGap :=by
  change max 0 (3-sourceAnchorGap)=3-sourceAnchorGap
  exact max_eq_right (by have small:=sourceAnchorGap_small;linarith)

private theorem anchor_momentum (q : PhysicalResponsePoint) :
    fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourceZeroTransfer q).k) 3=regularPoint :=by
  ext mu
  refine Fin.cases ?_ (fun i=>?_) mu
  · rfl
  · simp only [sourceZeroTransfer,PreparationVacuumPhysicalFeedback.physicalSpatial,Pi.zero_apply,Complex.ofReal_zero,mul_zero,regularPoint,fullMomentum,Fin.cases_succ]

def sourceNativeAnchor (q : PhysicalResponsePoint) : physicalSpectralDomain (sourceZeroTransfer q).k:=
  ⟨3,by
    change fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourceZeroTransfer q).k) 3∈regularSource
    rw [anchor_momentum]
    exact generatedRegularPoint.property⟩

theorem sourceAnchorGap_read (q : PhysicalResponsePoint) :
    sourceReadGap (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourceZeroTransfer q).k) sourceAnchorClock) 3=sourceAnchorGap :=by
  rw [sourceReadGap,sourceAnchorClock_growth]
  norm_num

/-- Every coefficient is produced at the unchanged preparation tuple; only the Fourier transfer and analytic spectral labels are instantiated. -/
def sourceResponseBudget (q : PhysicalResponsePoint) : ℝ:=
  4*((4/sourceAnchorGap)*sourceWholeLinearBudget (sourceZeroTransfer q) sourceAnchorEta+
    sourceWholeConstantBudget (sourceZeroTransfer q) sourceAnchorEta)

def sourceAnchorExtra (q : PhysicalResponsePoint) : ℝ:=
  4*(1+‖nativeMatrix (sourceGreen generatedRegularPoint)‖*sourceResponseBudget q)

def sourceAnalyticPoint (q : PhysicalResponsePoint) : PhysicalResponsePoint:=
  sourceMaterialPoint (sourceZeroTransfer q) (sourceAnchorExtra q)


theorem sourceResponseBudget_nonnegative (q : PhysicalResponsePoint) : 0 ≤ sourceResponseBudget q :=by
  have eta : 0<sourceAnchorEta:=by unfold sourceAnchorEta;exact div_pos sourceAnchorGap_positive (by norm_num)
  have left:=factorialBudget_nonnegative (sourceZeroTransfer q).p (sourceZeroTransfer q).F sourceAnchorEta eta
  have right:=factorialBudget_nonnegative ((sourceZeroTransfer q).p+(sourceZeroTransfer q).k) (sourceZeroTransfer q).F sourceAnchorEta eta
  unfold sourceResponseBudget sourceWholeLinearBudget sourceWholeConstantBudget sourceLinearBudget sourceConstantBudget
  unfold sourceReaderBudget sourceMaterialSlopeBudget sourceContactBudget sourcePrimalCoefficient sourceDualCoefficient
  have gap:=sourceAnchorGap_positive
  positivity

theorem sourceAnchorExtra_positive (q : PhysicalResponsePoint) : 0<sourceAnchorExtra q :=by
  unfold sourceAnchorExtra
  have budget:=sourceResponseBudget_nonnegative q
  positivity

theorem sourceAnalyticPoint_read (q : PhysicalResponsePoint) : sourceRead (sourceAnalyticPoint q)=sourceRead q :=by
  rw [sourceAnalyticPoint,sourceMaterialPoint_read]
  unfold sourceRead PreparationVacuumPhysicalFeedback.responseLeft PreparationVacuumPhysicalFeedback.responseRight sourceZeroTransfer
  rfl

private theorem nativeMatrix_sum (A B : Matrix (Fin 289) (Fin 289) ℂ) : nativeMatrix (A+B)=nativeMatrix A+nativeMatrix B :=by
  ext a i
  simp only [nativeMatrix_actual,add_apply,Matrix.add_mulVec,Pi.add_apply]

private theorem nativeMatrix_smul (c : ℂ) (A : Matrix (Fin 289) (Fin 289) ℂ) : nativeMatrix (c • A)=c • nativeMatrix A :=by
  ext a i
  simp only [nativeMatrix_actual,smul_apply,Matrix.smul_mulVec]

private theorem nativeMatrix_price (c : ℂ) (A : Matrix (Fin 289) (Fin 289) ℂ) :
    ‖nativeMatrix (c • A)‖ ≤ ‖c‖*‖nativeMatrix A‖ :=by
  rw [nativeMatrix_smul]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg c) (norm_nonneg _))
  intro a
  rw [smul_apply,norm_smul]
  exact (mul_le_mul_of_nonneg_left ((nativeMatrix A).le_opNorm a) (norm_nonneg c)).trans_eq (mul_assoc _ _ _).symm

private theorem nativeMatrix_amplitude_price (c : ℂ) :
    ‖(c • ContinuousLinearMap.id ℝ SignalAmplitude : SignalAmplitude→L[ℝ] SignalAmplitude)‖ ≤ ‖c‖ :=by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
  intro a
  simp only [smul_apply,ContinuousLinearMap.id_apply,norm_smul]
  exact le_rfl

private theorem anchor_initial_matrix (q : PhysicalResponsePoint) :
    sourceLaplaceInitial (sourceAnalyticPoint q) sourceAnchorClock 3=
      (nativeMatrix (sourceTemporalFirst 0+(sourceAnchorClock+3) • sourceTemporalSecond)).comp
        ((3-sourceAnchorClock) • ContinuousLinearMap.id ℝ SignalAmplitude) :=by
  apply ContinuousLinearMap.ext
  intro field
  have off : sourceAnchorClock.re<3 :=by
    simp only [sourceAnchorClock,Complex.ofReal_re]
    have gap:=sourceAnchorGap_positive
    linarith
  rw [sourceLaplaceInitial_actual _ _ _ off,ContinuousLinearMap.comp_apply,nativeMatrix_actual,
    smul_apply,ContinuousLinearMap.id_apply]
  have spatialZero : PreparationVacuumPhysicalFeedback.physicalSpatial (sourceAnalyticPoint q).k=(0 : Fin 3→ℂ) :=by
    ext i
    simp [sourceAnalyticPoint,sourceMaterialPoint,sourceZeroTransfer,PreparationVacuumPhysicalFeedback.physicalSpatial]
  rw [spatialZero]

private theorem anchor_clock_norm : ‖sourceAnchorClock+3‖ ≤ 6 :=by
  have gap:=sourceAnchorGap_positive
  have small:=sourceAnchorGap_small
  have actual : sourceAnchorClock+3=((6-sourceAnchorGap : ℝ) : ℂ):=by
    unfold sourceAnchorClock
    push_cast
    ring
  rw [actual,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  linarith

private theorem anchor_difference_norm : ‖(3 : ℂ)-sourceAnchorClock‖=sourceAnchorGap :=by
  have actual : (3 : ℂ)-sourceAnchorClock=(sourceAnchorGap : ℂ):=by
    unfold sourceAnchorClock
    push_cast
    ring
  rw [actual,Complex.norm_real,Real.norm_eq_abs,abs_of_pos sourceAnchorGap_positive]

theorem sourceInitialOperator_anchor_price (q : PhysicalResponsePoint) :
    ‖sourceLaplaceInitial (sourceAnalyticPoint q) sourceAnchorClock 3‖ ≤
      (‖nativeMatrix (sourceTemporalFirst 0)‖+6*‖nativeMatrix sourceTemporalSecond‖)*sourceAnchorGap :=by
  rw [anchor_initial_matrix]
  have matrixPrice : ‖nativeMatrix (sourceTemporalFirst 0+(sourceAnchorClock+3) • sourceTemporalSecond)‖ ≤
      ‖nativeMatrix (sourceTemporalFirst 0)‖+6*‖nativeMatrix sourceTemporalSecond‖:=by
    rw [nativeMatrix_sum]
    exact (norm_add_le _ _).trans (add_le_add le_rfl
      ((nativeMatrix_price _ _).trans (mul_le_mul_of_nonneg_right anchor_clock_norm (norm_nonneg _))))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul matrixPrice ((nativeMatrix_amplitude_price _).trans_eq anchor_difference_norm) (norm_nonneg _) (by positivity))


def sourceAnalyticFrequency (q : PhysicalResponsePoint) : SourceCurrentFrequency (sourceAnalyticPoint q) sourceAnchorClock:=
  ⟨sourceNativeAnchor q,by
    change sourceClockGrowth (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourceZeroTransfer q).k) sourceAnchorClock)<(3 : ℂ).re
    rw [sourceAnchorClock_growth]
    norm_num
    exact sourceAnchorGap_positive⟩

private theorem analytic_gap (q : PhysicalResponsePoint) :
    sourceReadGap (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourceAnalyticPoint q).k) sourceAnchorClock) 3=sourceAnchorGap :=
  sourceAnchorGap_read q

private theorem analytic_eta (q : PhysicalResponsePoint) :
    sourceCausalEta (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourceAnalyticPoint q).k) sourceAnchorClock) 3=sourceAnchorEta :=by
  unfold sourceCausalEta sourceAnchorEta
  rw [analytic_gap]

private theorem anchor_current_normalization (q : PhysicalResponsePoint) :
    sourceLaplaceCurrentPrice (sourceAnalyticPoint q) sourceAnchorClock 3=
      4*((4/sourceAnchorGap)*sourceCurrentLinearCoefficient (sourceAnalyticPoint q) sourceAnchorEta+
        sourceCurrentConstantCoefficient (sourceAnalyticPoint q) sourceAnchorEta) :=by
  unfold sourceLaplaceCurrentPrice sourceCausalCoefficient
  rw [analytic_gap,analytic_eta,anchor_difference_norm]
  have gap:=sourceAnchorGap_positive
  field_simp
  ring

theorem sourceAnchorCurrent_price (q : PhysicalResponsePoint) :
    ‖sourceLaplaceCurrent (sourceAnalyticPoint q) sourceAnchorClock 3‖ ≤
      sourceResponseBudget q/(sourcePairRadius (sourceZeroTransfer q) (sourceAnchorExtra q))^2 :=by
  have eta : 0<sourceAnchorEta:=by unfold sourceAnchorEta;exact div_pos sourceAnchorGap_positive (by norm_num)
  have extra:=(sourceAnchorExtra_positive q).le
  have linear:=sourceWholeLinearBudget_materialPrice (sourceZeroTransfer q) (sourceAnchorExtra q) extra sourceAnchorEta eta
  have constant:=sourceWholeConstantBudget_materialPrice (sourceZeroTransfer q) (sourceAnchorExtra q) extra sourceAnchorEta eta
  have combined:=mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left linear (show (0 : ℝ) ≤ 4/sourceAnchorGap from (div_nonneg (by norm_num) sourceAnchorGap_positive.le))) constant)
    (show (0 : ℝ) ≤ 4 by norm_num)
  have off:=(sourceAnalyticFrequency q).property
  have source:=sourceLaplaceCurrent_price (sourceAnalyticPoint q) sourceAnchorClock 3 off
  apply source.trans
  rw [anchor_current_normalization]
  have normalized : 4*((4/sourceAnchorGap)*(sourceWholeLinearBudget (sourceZeroTransfer q) sourceAnchorEta/(sourcePairRadius (sourceZeroTransfer q) (sourceAnchorExtra q))^2)+
      sourceWholeConstantBudget (sourceZeroTransfer q) sourceAnchorEta/(sourcePairRadius (sourceZeroTransfer q) (sourceAnchorExtra q))^2)=
      sourceResponseBudget q/(sourcePairRadius (sourceZeroTransfer q) (sourceAnchorExtra q))^2:=by
    unfold sourceResponseBudget
    ring
  exact combined.trans_eq normalized

private theorem analytic_green (q : PhysicalResponsePoint) :
    sourceGreen ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourceAnalyticPoint q).k) (sourceAnalyticFrequency q).val.val,
      (sourceAnalyticFrequency q).val.property⟩=sourceGreen generatedRegularPoint :=by
  congr 1
  apply Subtype.ext
  exact anchor_momentum q

private theorem analytic_update_pointwise (q : PhysicalResponsePoint) (field : SignalAmplitude) :
    sourceCommonUpdateOperator (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q).val field=
      nativeMatrix (sourceGreen generatedRegularPoint)
        (sourceLaplaceCurrent (sourceAnalyticPoint q) sourceAnchorClock 3 field+
          sourceLaplaceInitial (sourceAnalyticPoint q) sourceAnchorClock 3 field) :=by
  rw [sourceCommonUpdateOperator_actual,nativeMatrix_actual,analytic_green]
  rfl

private theorem source_gamma_square (q : PhysicalResponsePoint) :
    ‖nativeMatrix (sourceGreen generatedRegularPoint)‖*sourceResponseBudget q/
      (sourcePairRadius (sourceZeroTransfer q) (sourceAnchorExtra q))^2 ≤ 1/16 :=by
  have budget:=sourceResponseBudget_nonnegative q
  have extra:=sourceAnchorExtra_positive q
  have radius : 4*(1+‖nativeMatrix (sourceGreen generatedRegularPoint)‖*sourceResponseBudget q) ≤
      sourcePairRadius (sourceZeroTransfer q) (sourceAnchorExtra q) :=by
    unfold sourcePairRadius sourceAnchorExtra
    have left:=norm_nonneg (sourceBaseGenerator ((sourceZeroTransfer q).p+(sourceZeroTransfer q).k) (sourceZeroTransfer q).F)
    have right:=norm_nonneg (sourceBaseGenerator (sourceZeroTransfer q).p (sourceZeroTransfer q).F)
    have product:=mul_nonneg (norm_nonneg (nativeMatrix (sourceGreen generatedRegularPoint))) budget
    nlinarith
  have positive:=sourcePairRadius_positive (sourceZeroTransfer q) (sourceAnchorExtra q) extra.le
  apply (div_le_iff₀ (sq_pos_of_pos positive)).mpr
  have n:=norm_nonneg (nativeMatrix (sourceGreen generatedRegularPoint))
  have product:=mul_nonneg n budget
  nlinarith [sq_nonneg (‖nativeMatrix (sourceGreen generatedRegularPoint)‖*sourceResponseBudget q),sq_nonneg (sourcePairRadius (sourceZeroTransfer q) (sourceAnchorExtra q)-4*(1+‖nativeMatrix (sourceGreen generatedRegularPoint)‖*sourceResponseBudget q))]

private theorem source_initial_small : sourceInitialBudget*sourceAnchorGap ≤ 1/8 :=by
  have source:=sourceInitialBudget_nonnegative
  unfold sourceAnchorGap
  have same : sourceInitialBudget*(1/(8*(1+sourceInitialBudget)))=(sourceInitialBudget/(1+sourceInitialBudget))/8:=by
    field_simp
  rw [same]
  apply (div_le_div_iff_of_pos_right (show (0 : ℝ)<8 by norm_num)).mpr
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

theorem sourceAnchorUpdate_price (q : PhysicalResponsePoint) :
    ‖sourceCommonUpdateOperator (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q).val‖ ≤ 3/16 :=by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro field
  rw [analytic_update_pointwise]
  have linear:=sourceAnchorCurrent_price q
  have initial:=sourceInitialOperator_anchor_price q
  have applied : ‖sourceLaplaceCurrent (sourceAnalyticPoint q) sourceAnchorClock 3 field+
      sourceLaplaceInitial (sourceAnalyticPoint q) sourceAnchorClock 3 field‖ ≤
      (sourceResponseBudget q/(sourcePairRadius (sourceZeroTransfer q) (sourceAnchorExtra q))^2+
        (‖nativeMatrix (sourceTemporalFirst 0)‖+6*‖nativeMatrix sourceTemporalSecond‖)*sourceAnchorGap)*‖field‖:=by
    have left:=((sourceLaplaceCurrent (sourceAnalyticPoint q) sourceAnchorClock 3).le_opNorm field).trans
      (mul_le_mul_of_nonneg_right linear (norm_nonneg field))
    have right:=((sourceLaplaceInitial (sourceAnalyticPoint q) sourceAnchorClock 3).le_opNorm field).trans
      (mul_le_mul_of_nonneg_right initial (norm_nonneg field))
    exact (norm_add_le _ _).trans ((add_le_add left right).trans_eq (by ring))
  have price:=((nativeMatrix (sourceGreen generatedRegularPoint)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left applied (norm_nonneg _))
  have scalar : ‖nativeMatrix (sourceGreen generatedRegularPoint)‖*
      (sourceResponseBudget q/(sourcePairRadius (sourceZeroTransfer q) (sourceAnchorExtra q))^2+
        (‖nativeMatrix (sourceTemporalFirst 0)‖+6*‖nativeMatrix sourceTemporalSecond‖)*sourceAnchorGap) ≤ 3/16 :=by
    have actual:=add_le_add (source_gamma_square q) source_initial_small
    unfold sourceInitialBudget at actual
    convert! actual using 1 <;> ring
  have bounded:=mul_le_mul_of_nonneg_right scalar (norm_nonneg field)
  exact price.trans ((by simpa only [mul_assoc] using bounded))


theorem sourceAnalyticDenominator_nonzero (q : PhysicalResponsePoint) :
    sourceFeedbackDenominator (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q)≠0 :=by
  have unit : IsUnit (sourceFeedbackMatrix (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q)):=by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro a b same
    have difference : sourceFeedbackMatrix (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q)*ᵥ(a-b)=0:=by
      rw [Matrix.mulVec_sub,same,sub_self]
    rw [sourceFeedbackMatrix_actual] at difference
    have fieldEquation : a-b=sourceCommonUpdateOperator (sourceAnalyticPoint q) sourceAnchorClock
        (sourceAnalyticFrequency q).val (a-b):=sub_eq_zero.mp difference
    have price:=(sourceCommonUpdateOperator (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q).val).le_opNorm (a-b)
    have controlled:=price.trans (mul_le_mul_of_nonneg_right (sourceAnchorUpdate_price q) (norm_nonneg (a-b)))
    rw [←fieldEquation] at controlled
    have vanishing : ‖a-b‖=0:=by nlinarith [norm_nonneg (a-b)]
    exact sub_eq_zero.mp (norm_eq_zero.mp vanishing)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp unit).ne_zero

def sourceAnalyticRegularPoint (q : PhysicalResponsePoint) : sourceCurrentRegularDomain (sourceAnalyticPoint q) sourceAnchorClock:=
  ⟨sourceAnalyticFrequency q,sourceAnalyticDenominator_nonzero q⟩

theorem sourceAnalyticRegularDomain_nonempty (q : PhysicalResponsePoint) :
    (sourceCurrentRegularDomain (sourceAnalyticPoint q) sourceAnchorClock).Nonempty:=
  ⟨sourceAnalyticFrequency q,sourceAnalyticDenominator_nonzero q⟩

theorem sourceAnalyticPreparedResponse (q : PhysicalResponsePoint) (external : SignalAmplitude) :
    sourceDressedField (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticRegularPoint q) external=
      sourceCommonFieldUpdate (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q).val external
        (sourceDressedField (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticRegularPoint q) external) :=
  sourceDressedField_generated _ _ _ _


theorem sourceAnalyticResolvent_price (q : PhysicalResponsePoint) (forcing : SignalAmplitude) :
    ‖sourceFeedbackResolvent (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q)*ᵥforcing‖ ≤
      (16/13 : ℝ)*‖forcing‖ :=by
  let field:=sourceFeedbackResolvent (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q)*ᵥforcing
  have equation:=sourceFeedbackResponse_generated (sourceAnalyticPoint q) sourceAnchorClock
    (sourceAnalyticRegularPoint q) forcing
  have update:=((sourceCommonUpdateOperator (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q).val).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right (sourceAnchorUpdate_price q) (norm_nonneg field))
  have fieldEquation : field=forcing+sourceCommonUpdateOperator (sourceAnalyticPoint q) sourceAnchorClock (sourceAnalyticFrequency q).val field:=equation
  have triangle : ‖field‖ ≤ ‖forcing‖+(3/16 : ℝ)*‖field‖:=
    (congrArg norm fieldEquation).trans_le ((norm_add_le _ _).trans (add_le_add le_rfl update))
  change ‖field‖ ≤ _
  nlinarith

end LowEnergy.PreparationVacuumCurrentRegularAnchor
