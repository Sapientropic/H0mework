import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.Window
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

def returnDefectProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  inverseMobiusProfile coordinate x-tateReturnMobiusProfile coordinate x+
    burnolRieszReturnRaw coordinate q*(OriginalFourierPrimitiveActionSource.fullMobiusFourierProfile coordinate x-
      OriginalFourierPrimitiveActionSource.tateMobiusPrimitiveProfile coordinate x)

theorem original_return_defect_four_feet (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.D (OriginalReturnResponseSource.correctedReturn coordinate)=
      (Paid.M (fourierL2 (wholeReturn coordinate))-burnolTateReciprocalL2 (Paid.M (wholeReturn coordinate)))+
      burnolRieszReturnRaw coordinate q •
        (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)-
          burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))) := by
  unfold OriginalReturnResponseSource.correctedReturn
  simp only [map_add,map_smul]
  unfold Paid.D
  simp only [sub_apply,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
  change (Paid.M (fourierL2 (wholeReturn coordinate))-burnolTateReciprocalL2 (Paid.M (wholeReturn coordinate)))+
    burnolRieszReturnRaw coordinate q •
      (Paid.M (fourierL2 (OriginalRieszFiniteSource.edgePrimitive coordinate))-
        burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)))=_
  rfl

theorem original_return_defect_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.D (OriginalReturnResponseSource.correctedReturn coordinate):ℝ→ℂ)=ᵐ[volume] returnDefectProfile coordinate := by
  rw [original_return_defect_four_feet]
  filter_upwards [Lp.coeFn_add
      (Paid.M (fourierL2 (wholeReturn coordinate))-burnolTateReciprocalL2 (Paid.M (wholeReturn coordinate)))
      (burnolRieszReturnRaw coordinate q • (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)-
        burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)))),
    Lp.coeFn_sub (Paid.M (fourierL2 (wholeReturn coordinate))) (burnolTateReciprocalL2 (Paid.M (wholeReturn coordinate))),
    Lp.coeFn_smul (burnolRieszReturnRaw coordinate q) (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)-
      burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))),
    Lp.coeFn_sub (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))
      (burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))),
    original_inverse_M_return_raw coordinate,original_TM_return_raw coordinate,
    OriginalFourierPrimitiveActionSource.original_MFP_profile coordinate,
    OriginalFourierPrimitiveActionSource.original_TMP_profile coordinate]
      with x add difference scalar primitiveDifference inverse tateReturn fourierPrimitive tatePrimitive
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at add difference scalar primitiveDifference
  rw [add,difference,scalar]
  change Paid.M (fourierL2 (wholeReturn coordinate)) x-burnolTateReciprocalL2 (Paid.M (wholeReturn coordinate)) x+
    burnolRieszReturnRaw coordinate q*((Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)-
      burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))):BurnolL2) x=_
  rw [primitiveDifference]
  change Paid.M (fourierL2 (wholeReturn coordinate)) x-burnolTateReciprocalL2 (Paid.M (wholeReturn coordinate)) x+
    burnolRieszReturnRaw coordinate q*(Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate) x-
      burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)) x)=_
  rw [inverse,tateReturn,fourierPrimitive,tatePrimitive]
  rfl

def returnSourcePrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫ x : ℝ in OriginalColumnMomentSource.outerBand h,
    -(Real.exp (-h/2):ℂ)*star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x))*returnDefectProfile coordinate x

theorem original_return_source_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
      (Paid.D (OriginalReturnResponseSource.correctedReturn coordinate))=returnSourcePrice coordinate h := by
  rw [OriginalColumnMomentSource.original_paired_sample_positive coordinate h nonnegative,L2.inner_def]
  have raw : (fun x:ℝ=>inner ℂ
      (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 x)
      (Paid.D (OriginalReturnResponseSource.correctedReturn coordinate) x))=ᵐ[volume]
    (OriginalColumnMomentSource.outerBand h).indicator (fun x=>-(Real.exp (-h/2):ℂ)*
      star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x))*returnDefectProfile coordinate x) := by
    filter_upwards [OriginalColumnMomentSource.original_positive_sample_raw coordinate h nonnegative bounded,
      original_return_defect_raw coordinate] with x column source
    by_cases inside : x∈OriginalColumnMomentSource.outerBand h
    · rw [column,source]
      simp only [indicator_of_mem inside]
      rw [RCLike.inner_apply]
      simp only [map_mul,map_neg,Complex.conj_ofReal]
      change returnDefectProfile coordinate x*(-(Real.exp (-h/2):ℂ)*star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x)))=_
      ring
    · rw [column,indicator_of_notMem inside,inner_zero_left,indicator_of_notMem inside]
  rw [integral_congr_ae raw,integral_indicator (OriginalColumnMomentSource.measurable_outerBand h)]
  rfl
end OriginalInverseReturnActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
