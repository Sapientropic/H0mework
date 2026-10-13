import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveAction.Action
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ContactFeedback.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

def primitiveReturnPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫ x : ℝ in OriginalColumnMomentSource.outerBand h,
    -(Real.exp (-h/2):ℂ)*star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x))*primitiveReturnRaw coordinate x

-- Actual source-supported price, not an additional field admission or R readout alias.
theorem original_primitive_Rplus_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn coordinate h)
      (OriginalContactFeedbackSource.retainedPrimitiveReturn coordinate)=primitiveReturnPrice coordinate h := by
  unfold OriginalContactFeedbackSource.retainedPrimitiveReturn
  rw [OriginalColumnMomentSource.original_paired_sample_positive coordinate h nonnegative,L2.inner_def]
  have raw : (fun x : ℝ=>inner ℂ
      (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 x)
      (Paid.Rplus (star coordinate.value/2) (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)) x))=ᵐ[volume]
    (OriginalColumnMomentSource.outerBand h).indicator (fun x=>-(Real.exp (-h/2):ℂ)*
      star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x))*primitiveReturnRaw coordinate x) := by
    filter_upwards [OriginalColumnMomentSource.original_positive_sample_raw coordinate h nonnegative bounded,
      original_primitive_Rplus_read coordinate] with x column source
    by_cases inside : x∈OriginalColumnMomentSource.outerBand h
    · rw [column,source]
      simp only [indicator_of_mem inside]
      rw [RCLike.inner_apply]
      simp only [map_mul,map_neg,Complex.conj_ofReal]
      change primitiveReturnRaw coordinate x*(-(Real.exp (-h/2):ℂ)*star (OriginalColumnMomentSource.originalB coordinate (Real.exp (-h)*x)))=_
      ring
    · rw [column,indicator_of_notMem inside,inner_zero_left,indicator_of_notMem inside]
  rw [integral_congr_ae raw,integral_indicator (OriginalColumnMomentSource.measurable_outerBand h)]
  rfl
end OriginalPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
