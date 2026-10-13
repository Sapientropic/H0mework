import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierPrimitiveAction.Contact
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierPrimitiveActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource

def sourceContactPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫ x : ℝ in OriginalColumnMomentSource.outerBand h,
    -(Real.exp (-h/2):ℂ)*star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x))*contactDefectProfile coordinate x

-- Actual paired columns consume the source-generated q anchor/Edge profile in all four finite/Tate feet.
theorem original_contact_source_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn coordinate h)
      (Paid.D (FiniteMobiusResolventFlux.S.contactCorrection coordinate))=sourceContactPrice coordinate h := by
  rw [OriginalColumnMomentSource.original_paired_sample_positive coordinate h nonnegative,L2.inner_def]
  have raw : (fun x:ℝ=>inner ℂ
      (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 x)
      (Paid.D (FiniteMobiusResolventFlux.S.contactCorrection coordinate) x))=ᵐ[volume]
    (OriginalColumnMomentSource.outerBand h).indicator (fun x=>-(Real.exp (-h/2):ℂ)*
      star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x))*contactDefectProfile coordinate x) := by
    filter_upwards [OriginalColumnMomentSource.original_positive_sample_raw coordinate h nonnegative bounded,
      original_contact_defect_profile coordinate] with x column source
    by_cases inside : x∈OriginalColumnMomentSource.outerBand h
    · rw [column,source]
      simp only [indicator_of_mem inside]
      rw [RCLike.inner_apply]
      simp only [map_mul,map_neg,Complex.conj_ofReal]
      change contactDefectProfile coordinate x*(-(Real.exp (-h/2):ℂ)*star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x)))=_
      ring
    · rw [column,indicator_of_notMem inside,inner_zero_left,indicator_of_notMem inside]
  rw [integral_congr_ae raw,integral_indicator (OriginalColumnMomentSource.measurable_outerBand h)]
  rfl
end OriginalFourierPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
