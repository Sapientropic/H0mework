import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.Action
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

def coupledReturnSourcePrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫ x : ℝ in OriginalColumnMomentSource.outerBand h,
    -(Real.exp (-h/2):ℂ)*star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x))*coupledReturnProfile coordinate x

theorem original_coupled_return_source_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
      (burnolTateReciprocalL2 (Paid.M (OriginalContactFeedbackSource.sourceField coordinate)))+
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
      (Paid.D (OriginalReturnResponseSource.correctedReturn coordinate))=coupledReturnSourcePrice coordinate h := by
  rw [← inner_add_right,OriginalColumnMomentSource.original_paired_sample_positive coordinate h nonnegative,L2.inner_def]
  have raw : (fun x:ℝ=>inner ℂ
      (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 x)
      ((burnolTateReciprocalL2 (Paid.M (OriginalContactFeedbackSource.sourceField coordinate))+
        Paid.D (OriginalReturnResponseSource.correctedReturn coordinate):BurnolL2) x))=ᵐ[volume]
    (OriginalColumnMomentSource.outerBand h).indicator (fun x=>-(Real.exp (-h/2):ℂ)*
      star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x))*coupledReturnProfile coordinate x) := by
    filter_upwards [OriginalColumnMomentSource.original_positive_sample_raw coordinate h nonnegative bounded,
      original_coupled_return_raw coordinate] with x column source
    by_cases inside : x∈OriginalColumnMomentSource.outerBand h
    · rw [column,source]
      simp only [indicator_of_mem inside]
      rw [RCLike.inner_apply]
      simp only [map_mul,map_neg,Complex.conj_ofReal]
      change coupledReturnProfile coordinate x*(-(Real.exp (-h/2):ℂ)*star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x)))=_
      ring
    · rw [column,indicator_of_notMem inside,inner_zero_left,indicator_of_notMem inside]
  rw [integral_congr_ae raw,integral_indicator (OriginalColumnMomentSource.measurable_outerBand h)]
  rfl
end OriginalInverseReturnActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
