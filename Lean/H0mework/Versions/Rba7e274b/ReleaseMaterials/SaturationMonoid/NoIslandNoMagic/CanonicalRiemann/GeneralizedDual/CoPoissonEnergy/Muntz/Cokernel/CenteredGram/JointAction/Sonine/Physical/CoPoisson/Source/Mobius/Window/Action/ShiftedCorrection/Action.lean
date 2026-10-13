import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalInverseReturnActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource
local notation "q" => (1/4:ℝ)

def firstFourierMean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient (burnolTruncatedFourier (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2))

theorem original_first_fourier_mean (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.actualMean (fourierL2 (OriginalColumnMomentSource.originalB coordinate))=firstFourierMean coordinate := by
  change (‖intervalConstant q‖^2:ℂ)⁻¹*inner ℂ (intervalConstant q)
    (burnolRadiusRestriction q (fourierL2 (burnolRadiusZeroExtension q (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2))))=firstFourierMean coordinate
  unfold firstFourierMean burnolQuarterMeanCoefficient
  simp only [div_eq_mul_inv,Complex.ofReal_pow]
  change (‖intervalConstant q‖^2:ℂ)⁻¹*inner ℂ (intervalConstant q) (burnolTruncatedFourier (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2))=
    inner ℂ (intervalConstant q) (burnolTruncatedFourier (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2))*(‖intervalConstant q‖^2:ℂ)⁻¹
  ring

def fullReturnMobiusProfile (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  (symmetricInterval 4).indicator (fun x=>∑ n∈burnolCenteredMobiusCutoffFinset 4,
    Paid.coefficient n*burnolRieszReturnRaw coordinate (x/(n:ℕ)))

theorem original_full_return_word (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.M (fourierL2 (OriginalColumnMomentSource.originalB coordinate)):ℝ→ℂ)=ᵐ[volume] fullReturnMobiusProfile coordinate := by
  have source:=actual_full_window_profile _ _ _ (OriginalFourierMobiusReturnSource.actual_fourier_source_read coordinate)
    (original_first_fourier_mean coordinate)
  apply source.trans
  exact Filter.EventuallyEq.of_eq (by
    funext x
    unfold fullReturnMobiusProfile
    congr 1
)

def exteriorReturnWord (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Paid.M (fourierL2 (OriginalColumnMomentSource.originalB coordinate))-Paid.M (wholeReturn coordinate)
def exteriorReturnProfile (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  (symmetricInterval 4).indicator (fun x=>∑ n∈burnolCenteredMobiusCutoffFinset 4,
    Paid.coefficient n*(burnolRieszReturnRaw coordinate (x/(n:ℕ))-returnWindowProfile coordinate (x/(n:ℕ))))

theorem original_exterior_return_word (coordinate : BurnolCompletedMellinCoordinate) :
    (exteriorReturnWord coordinate:ℝ→ℂ)=ᵐ[volume] exteriorReturnProfile coordinate := by
  filter_upwards [Lp.coeFn_sub (Paid.M (fourierL2 (OriginalColumnMomentSource.originalB coordinate))) (Paid.M (wholeReturn coordinate)),
    original_full_return_word coordinate,original_M_return_raw coordinate] with x difference full compact
  change (Paid.M (fourierL2 (OriginalColumnMomentSource.originalB coordinate))-Paid.M (wholeReturn coordinate):BurnolL2) x=_
  rw [difference]
  change Paid.M (fourierL2 (OriginalColumnMomentSource.originalB coordinate)) x-Paid.M (wholeReturn coordinate) x=_
  rw [full,compact]
  unfold fullReturnMobiusProfile returnMobiusProfile exteriorReturnProfile
  by_cases inside : x∈symmetricInterval 4
  · simp only [indicator_of_mem inside]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  · simp only [indicator_of_notMem inside,sub_self]

def tateExteriorReturnProfile (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  burnolTateReciprocalRaw (exteriorReturnProfile coordinate)

theorem original_tate_exterior_word (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolTateReciprocalL2 (exteriorReturnWord coordinate):ℝ→ℂ)=ᵐ[volume] tateExteriorReturnProfile coordinate := by
  have raw:=original_exterior_return_word coordinate
  have moved:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (exteriorReturnWord coordinate))
    ((Lp.memLp (exteriorReturnWord coordinate)).ae_eq raw) raw
  exact (burnolTateReciprocalL2_coeFn _).trans moved

-- Same original b/r finite action: the compact return cancels only its own matching quarter component.
theorem original_coupled_return_action (coordinate : BurnolCompletedMellinCoordinate) :
    burnolTateReciprocalL2 (Paid.M (OriginalContactFeedbackSource.sourceField coordinate))+
      Paid.D (OriginalReturnResponseSource.correctedReturn coordinate)=
    Paid.M (fourierL2 (wholeReturn coordinate))+
      burnolTateReciprocalL2 (exteriorReturnWord coordinate)+
      burnolRieszReturnRaw coordinate q • Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)+
      Kernel.beta coordinate • burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))-
      burnolRieszReturnRaw coordinate q • burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)) := by
  rw [original_return_defect_four_feet]
  unfold OriginalContactFeedbackSource.sourceField exteriorReturnWord
  simp only [map_add,map_sub,map_smul]
  module

def coupledReturnProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  inverseMobiusProfile coordinate x+tateExteriorReturnProfile coordinate x+
    burnolRieszReturnRaw coordinate q*OriginalFourierPrimitiveActionSource.fullMobiusFourierProfile coordinate x+
    Kernel.beta coordinate*OriginalFourierPrimitiveActionSource.tateMobiusFourierProfile coordinate x-
    burnolRieszReturnRaw coordinate q*OriginalFourierPrimitiveActionSource.tateMobiusPrimitiveProfile coordinate x

theorem original_coupled_return_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolTateReciprocalL2 (Paid.M (OriginalContactFeedbackSource.sourceField coordinate))+
      Paid.D (OriginalReturnResponseSource.correctedReturn coordinate):BurnolL2)=ᵐ[volume] coupledReturnProfile coordinate := by
  rw [original_coupled_return_action]
  have inverse:=original_inverse_M_return_raw coordinate
  have exterior:=original_tate_exterior_word coordinate
  have fp:=OriginalFourierPrimitiveActionSource.original_MFP_profile coordinate
  have tfp:=OriginalFourierPrimitiveActionSource.original_TMFP_profile coordinate
  have tp:=OriginalFourierPrimitiveActionSource.original_TMP_profile coordinate
  filter_upwards [Lp.coeFn_sub
      (Paid.M (fourierL2 (wholeReturn coordinate))+burnolTateReciprocalL2 (exteriorReturnWord coordinate)+
        burnolRieszReturnRaw coordinate q • Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)+
        Kernel.beta coordinate • burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)))
      (burnolRieszReturnRaw coordinate q • burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))),
    Lp.coeFn_add
      (Paid.M (fourierL2 (wholeReturn coordinate))+burnolTateReciprocalL2 (exteriorReturnWord coordinate)+
        burnolRieszReturnRaw coordinate q • Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))
      (Kernel.beta coordinate • burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))),
    Lp.coeFn_add (Paid.M (fourierL2 (wholeReturn coordinate))+burnolTateReciprocalL2 (exteriorReturnWord coordinate))
      (burnolRieszReturnRaw coordinate q • Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)),
    Lp.coeFn_add (Paid.M (fourierL2 (wholeReturn coordinate))) (burnolTateReciprocalL2 (exteriorReturnWord coordinate)),
    Lp.coeFn_smul (burnolRieszReturnRaw coordinate q) (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)),
    Lp.coeFn_smul (Kernel.beta coordinate) (burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))),
    Lp.coeFn_smul (burnolRieszReturnRaw coordinate q) (burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))),
    inverse,exterior,fp,tfp,tp] with x difference add3 add2 add1 scalar1 scalar2 scalar3 inverse exterior fp tfp tp
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at difference add3 add2 add1 scalar1 scalar2 scalar3
  rw [difference,add3,add2,add1,scalar1,scalar2,scalar3,inverse,exterior,fp,tfp,tp]
  rfl
end OriginalInverseReturnActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
