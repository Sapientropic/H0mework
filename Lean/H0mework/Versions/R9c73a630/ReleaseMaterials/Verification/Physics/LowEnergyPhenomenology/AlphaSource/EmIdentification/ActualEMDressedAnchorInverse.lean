import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedSourceAnchor

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedAnchorInverse
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumCurrentSignalOperator
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor MeasureTheory Filter Set
open scoped BigOperators Topology Interval Matrix
attribute [local irreducible] sourceGreen dressedWindowPolarization dressedSignalWeighted
  dressedSignalWindow materialWindowBudget anchorRadius anchorEvent anchorInput

private theorem matrix_field_price {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (v : Fin n→ℂ) :
    ‖M*ᵥv‖  ≤  (∑i : Fin m,∑j : Fin n,‖M i j‖)*‖v‖ := by
  have total : 0  ≤  ∑i : Fin m,∑j : Fin n,‖M i j‖ :=
    Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg total (norm_nonneg v))).mpr
  intro i
  change ‖∑j : Fin n,M i j*v j‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  have row : (∑j : Fin n,‖M i j*v j‖) ≤ ∑j : Fin n,‖M i j‖*‖v‖ := by
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
  refine row.trans ?_
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (Finset.mem_univ i))
      (norm_nonneg v)

/-- The same original finite Bochner operator pays the window factor in its own norm. -/
theorem anchor_window_operator_price (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1) :
    ‖dressedSignalWindow (anchorEvent event) 0 anchorInput 3 T‖  ≤
      (materialWindowBudget event/(anchorRadius event)^2)*T := by
  unfold dressedSignalWindow
  have price := intervalIntegral.norm_integral_le_of_norm_le_const
    (f:=dressedSignalWeighted (anchorEvent event) 0 anchorInput 3)
    (a:=0) (b:=T) (C:=materialWindowBudget event/(anchorRadius event)^2)
    (fun t member=>by
      rw [uIoc_of_le positive.le] at member
      exact anchor_weighted_price event t member.1.le (member.2.trans small))
  simpa only [sub_zero,abs_of_pos positive] using price

theorem anchor_polarization_price (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (a : SignalAmplitude) :
    ‖dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥa‖  ≤
      ((materialWindowBudget event/(anchorRadius event)^2)*T)*‖a‖ := by
  rw [←dressed_window_polarization_actual]
  exact ((dressedSignalWindow (anchorEvent event) 0 anchorInput 3 T).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (anchor_window_operator_price event T positive small) (norm_nonneg a))

/-- This is the actual coincident-clock quantum feedback, not a chosen scalar response. -/
def anchorFeedback (event : DressedEvent) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  1-(T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*
    dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T)

theorem anchor_update_price (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (a : SignalAmplitude) :
    ‖(T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥ
      (dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥa))‖  ≤  (1/16:ℝ)*‖a‖ := by
  have field := matrix_field_price (sourceGreen generatedRegularPoint)
    (dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥa)
  change ‖sourceGreen generatedRegularPoint*ᵥ
    (dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥa)‖ ≤ anchorGreenPrice*‖_‖ at field
  have gnonnegative : 0 ≤ anchorGreenPrice :=
    Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  have full := field.trans (mul_le_mul_of_nonneg_left
    (anchor_polarization_price event T positive small a) gnonnegative)
  calc
    _=T⁻¹*‖sourceGreen generatedRegularPoint*ᵥ
        (dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥa)‖ := by
      rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    _ ≤ T⁻¹*(anchorGreenPrice*(((materialWindowBudget event/(anchorRadius event)^2)*T)*‖a‖)) :=
      mul_le_mul_of_nonneg_left full (inv_nonneg.mpr positive.le)
    _=(anchorGreenPrice*materialWindowBudget event/(anchorRadius event)^2)*‖a‖ := by
      calc
        _=(T⁻¹*T)*((anchorGreenPrice*materialWindowBudget event/(anchorRadius event)^2)*‖a‖) := by ring
        _=_ := by rw [inv_mul_cancel₀ positive.ne',one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (anchor_feedback_coefficient event) (norm_nonneg a)

/-- Source-generated material and window prices prove invertibility; an inverse is not a premise. -/
theorem anchor_feedback_unit (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1) :
    IsUnit (anchorFeedback event T) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro a b same
  have difference : anchorFeedback event T*ᵥ(a-b)=0 := by rw [Matrix.mulVec_sub,same,sub_self]
  have equation : a-b=(T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥ
      (dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥ(a-b))) := by
    rw [anchorFeedback,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,←Matrix.mulVec_mulVec] at difference
    exact sub_eq_zero.mp difference
  have price:=anchor_update_price event T positive small (a-b)
  rw [←equation] at price
  have zero : ‖a-b‖=0 := by nlinarith [norm_nonneg (a-b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp zero)

def anchorFeedbackResolvent (event : DressedEvent) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  (anchorFeedback event T)⁻¹

theorem anchor_inverse_generated (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1) :
    anchorFeedback event T*anchorFeedbackResolvent event T=1 ∧
      anchorFeedbackResolvent event T*anchorFeedback event T=1 := by
  have unit := (Matrix.isUnit_iff_isUnit_det _).mp (anchor_feedback_unit event T positive small)
  exact ⟨Matrix.mul_nonsing_inv _ unit,Matrix.nonsing_inv_mul _ unit⟩

theorem anchor_feedback_response (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (forcing : SignalAmplitude) :
    anchorFeedbackResolvent event T*ᵥforcing=forcing+(T:ℂ)⁻¹ •
      (sourceGreen generatedRegularPoint*ᵥ(dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥ
        (anchorFeedbackResolvent event T*ᵥforcing))) := by
  have equation := congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A*ᵥforcing)
    (anchor_inverse_generated event T positive small).1
  rw [←Matrix.mulVec_mulVec,Matrix.one_mulVec,anchorFeedback,Matrix.sub_mulVec,
    Matrix.one_mulVec,Matrix.smul_mulVec,←Matrix.mulVec_mulVec] at equation
  exact sub_eq_iff_eq_add.mp equation

theorem anchor_inverse_price (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (forcing : SignalAmplitude) :
    ‖anchorFeedbackResolvent event T*ᵥforcing‖  ≤  (16/15:ℝ)*‖forcing‖ := by
  have equation:=anchor_feedback_response event T positive small forcing
  have update:=anchor_update_price event T positive small (anchorFeedbackResolvent event T*ᵥforcing)
  have normed:=congrArg norm equation
  have bound:=(norm_add_le forcing ((T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥ
    (dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥ
      (anchorFeedbackResolvent event T*ᵥforcing))))).trans (add_le_add_right update _)
  rw [←normed] at bound
  nlinarith

/-- The generated positive original source window is an inhabitant of this actual inverse domain. -/
theorem anchor_actual_window_inverse (event : DressedEvent) (input : SignalAmplitude) :
    IsUnit (anchorFeedback event (anchorWindow event input)) :=
  anchor_feedback_unit event _ (anchor_window_source event input).1 (anchor_window_source event input).2.1

end LowEnergy.GaussComposite.ActualEMDressedAnchorInverse
