import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Window
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource OriginalPaPhysicalGreen FixedWindowFourierReaction
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing
local notation "q" => (1/4:ℝ)
local notation "T" => burnolRechartedTruncatedFourierOperator
local notation "P" => FixedWindowFourierReaction.p
local notation "S" => centeredOperator

theorem quarter_state_Q (state : BurnolQuarterMeanZeroCarrier) :
    Q (quarterChart (state:BurnolQuarterIntervalL2))=quarterChart (state:BurnolQuarterIntervalL2) := by
  rw [← quarter_projection_chart]
  exact congrArg quarterChart (Submodule.starProjection_eq_self_iff.mpr state.property)

private theorem actual_window_split (state : H) (qualified : Q state=state)
    (radius : ℝ) (positive : 0<radius) :
    T radius state=S radius state+((1/2:ℂ)*inner ℂ (P radius) state)•e := by
  have actualMean : inner ℂ e (T radius state)=inner ℂ (P radius) state := by
    rw [recharted_constant_pair radius positive]
    have projection:=Q_symmetric (T radius e) state
    change inner ℂ (Q (T radius e)) state=inner ℂ (T radius e) (Q state) at projection
    rw [qualified] at projection
    exact projection.symm
  unfold centeredOperator
  simp only [ContinuousLinearMap.comp_apply]
  rw [qualified,Q_read,InnerProductSpace.rankOne_apply,actualMean,smul_smul]
  module

private theorem centered_Q (radius : ℝ) (state : H) : Q (S radius state)=S radius state := by
  unfold centeredOperator
  simp only [ContinuousLinearMap.comp_apply]
  exact congrArg (fun operator:H→L[ℂ] H=>operator (T radius (Q state))) Q_idempotent

theorem actual_mixed_window_drive (state : BurnolQuarterMeanZeroCarrier)
    (left right : ℝ) (rightPositive : 0<right) :
    Q (T left (T right (quarterChart (state:BurnolQuarterIntervalL2))))=
      S left (S right (quarterChart (state:BurnolQuarterIntervalL2)))+
        ((1/2:ℂ)*inner ℂ (P right) (quarterChart (state:BurnolQuarterIntervalL2)))•P left := by
  rw [actual_window_split _ (quarter_state_Q state) right rightPositive,map_add,map_smul,map_add,map_smul]
  have centered : S left (S right (quarterChart (state:BurnolQuarterIntervalL2)))=
      Q (T left (S right (quarterChart (state:BurnolQuarterIntervalL2)))) := by
    change Q (T left (Q (S right (quarterChart (state:BurnolQuarterIntervalL2)))))=_
    rw [centered_Q]
  rw [← centered]
  rfl

def lowerWindowMean (state : BurnolQuarterMeanZeroCarrier) (h : ℝ) : H :=
  ((1/2:ℂ)*inner ℂ (P (upperRadius h)) (quarterChart (state:BurnolQuarterIntervalL2)))•P q-
    ((1/2:ℂ)*inner ℂ (P q) (quarterChart (state:BurnolQuarterIntervalL2)))•P (lowerRadius h)
def upperWindowMean (state : BurnolQuarterMeanZeroCarrier) (h : ℝ) : H :=
  ((1/2:ℂ)*inner ℂ (P q) (quarterChart (state:BurnolQuarterIntervalL2)))•P (upperRadius h)-
    ((1/2:ℂ)*inner ℂ (P (lowerRadius h)) (quarterChart (state:BurnolQuarterIntervalL2)))•P q

theorem source_lower_window_complete (state : BurnolQuarterMeanZeroCarrier) (h : ℝ) :
    quarterChart (windowKernelColumn state h (-h/2) (h/2):BurnolQuarterIntervalL2)=
      S q (S (upperRadius h) (quarterChart (state:BurnolQuarterIntervalL2)))-
        S (lowerRadius h) (S q (quarterChart (state:BurnolQuarterIntervalL2)))+
      lowerWindowMean state h := by
  have lowerPositive : 0<lowerRadius h := by unfold lowerRadius FixedWindowFourierReaction.actualRadius; positivity
  have upperPositive : 0<upperRadius h := by unfold upperRadius FixedWindowFourierReaction.actualRadius; positivity
  rw [source_window_kernel_lower,map_sub,
    actual_mixed_window_drive state q (upperRadius h) upperPositive,
    actual_mixed_window_drive state (lowerRadius h) q (by norm_num)]
  unfold lowerWindowMean
  abel

theorem source_upper_window_complete (state : BurnolQuarterMeanZeroCarrier) (h : ℝ) :
    quarterChart (windowKernelColumn state h (h/2) (-h/2):BurnolQuarterIntervalL2)=
      S (upperRadius h) (S q (quarterChart (state:BurnolQuarterIntervalL2)))-
        S q (S (lowerRadius h) (quarterChart (state:BurnolQuarterIntervalL2)))+
      upperWindowMean state h := by
  have lowerPositive : 0<lowerRadius h := by unfold lowerRadius FixedWindowFourierReaction.actualRadius; positivity
  have upperPositive : 0<upperRadius h := by unfold upperRadius FixedWindowFourierReaction.actualRadius; positivity
  rw [source_window_kernel_upper,map_sub,
    actual_mixed_window_drive state (upperRadius h) q (by norm_num),
    actual_mixed_window_drive state q (lowerRadius h) lowerPositive]
  unfold upperWindowMean
  abel

private theorem source_centered_adjoint (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0<radius) (field : H) :
    inner ℂ (originalB coordinate) (S radius field)=inner ℂ (S radius (originalB coordinate)) field := by
  have source:=congrArg (starRingEnd ℂ) (centered_even_pair radius positive field (originalB coordinate)
    (original_source_even coordinate))
  simpa only [inner_conj_symm] using source

def originalJointWindowMeanPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  inner ℂ (originalB coordinate)
    (lowerWindowMean (burnolRieszSingleFourierSource coordinate) h+
      upperWindowMean (burnolRieszSingleFourierSource coordinate) h)

theorem original_joint_window_reaction_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (originalB coordinate)
      (quarterChart (windowKernelColumn (burnolRieszSingleFourierSource coordinate) h (-h/2) (h/2):BurnolQuarterIntervalL2)+
       quarterChart (windowKernelColumn (burnolRieszSingleFourierSource coordinate) h (h/2) (-h/2):BurnolQuarterIntervalL2))=
    mixedReactionPrice coordinate (upperRadius h)-mixedReactionPrice coordinate (lowerRadius h)+
      originalJointWindowMeanPrice coordinate h := by
  have lowerPositive : 0<lowerRadius h := by unfold lowerRadius FixedWindowFourierReaction.actualRadius; positivity
  have upperPositive : 0<upperRadius h := by unfold upperRadius FixedWindowFourierReaction.actualRadius; positivity
  have plusPrice:=original_mixed_finite_price coordinate (upperRadius h) upperPositive
  have minusPrice:=original_mixed_finite_price coordinate (lowerRadius h) lowerPositive
  have plusPair:=source_centered_adjoint coordinate (upperRadius h) upperPositive (originalW coordinate)
  have minusPair:=source_centered_adjoint coordinate (lowerRadius h) lowerPositive (originalW coordinate)
  have quarterPlus:=source_centered_adjoint coordinate q (by norm_num) (S (upperRadius h) (originalB coordinate))
  have quarterMinus:=source_centered_adjoint coordinate q (by norm_num) (S (lowerRadius h) (originalB coordinate))
  change inner ℂ (originalB coordinate) (S (upperRadius h) (originalW coordinate))=
    inner ℂ (S (upperRadius h) (originalB coordinate)) (originalW coordinate) at plusPair
  change inner ℂ (originalB coordinate) (S (lowerRadius h) (originalW coordinate))=
    inner ℂ (S (lowerRadius h) (originalB coordinate)) (originalW coordinate) at minusPair
  change inner ℂ (originalB coordinate) (S q (S (upperRadius h) (originalB coordinate)))=
    inner ℂ (originalW coordinate) (S (upperRadius h) (originalB coordinate)) at quarterPlus
  change inner ℂ (originalB coordinate) (S q (S (lowerRadius h) (originalB coordinate)))=
    inner ℂ (originalW coordinate) (S (lowerRadius h) (originalB coordinate)) at quarterMinus
  rw [source_lower_window_complete,source_upper_window_complete]
  change inner ℂ (originalB coordinate)
    ((S q (S (upperRadius h) (originalB coordinate))-S (lowerRadius h) (originalW coordinate)+
       lowerWindowMean (burnolRieszSingleFourierSource coordinate) h)+
     (S (upperRadius h) (originalW coordinate)-S q (S (lowerRadius h) (originalB coordinate))+
       upperWindowMean (burnolRieszSingleFourierSource coordinate) h))=_
  simp only [inner_add_right,inner_sub_right]
  unfold originalJointWindowMeanPrice
  rw [inner_add_right]
  linear_combination plusPrice-minusPrice+plusPair-minusPair+quarterPlus-quarterMinus

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
