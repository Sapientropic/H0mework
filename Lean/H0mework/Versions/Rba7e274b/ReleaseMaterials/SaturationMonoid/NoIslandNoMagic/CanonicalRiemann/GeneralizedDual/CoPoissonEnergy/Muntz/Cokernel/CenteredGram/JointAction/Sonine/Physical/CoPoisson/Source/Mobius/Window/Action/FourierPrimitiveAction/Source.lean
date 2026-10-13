import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.Cotest
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
namespace Paid
export OriginalContactFeedbackSource (primitiveScale original_primitive_gap_source original_primitive_even)
export FiniteMobiusResolventFlux (M D coefficient actualMean cutoff cutoff_read)
end Paid

def primitiveFourierRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  Paid.primitiveScale coordinate*Translator.ForcingWhole.raw coordinate x

theorem original_FP_source (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalRieszFiniteSource.fourierPrimitive coordinate=
      Paid.primitiveScale coordinate • Translator.ForcingWhole.whole coordinate := by
  unfold OriginalRieszFiniteSource.fourierPrimitive
  rw [Paid.original_primitive_gap_source,map_smul]
  rfl

theorem original_FP_read (coordinate : BurnolCompletedMellinCoordinate) :
    (OriginalRieszFiniteSource.fourierPrimitive coordinate:ℝ→ℂ)=ᵐ[volume] primitiveFourierRaw coordinate := by
  rw [original_FP_source]
  filter_upwards [Lp.coeFn_smul (Paid.primitiveScale coordinate) (Translator.ForcingWhole.whole coordinate),Translator.ForcingWhole.whole_read coordinate] with x scaled source
  rw [scaled]
  change Paid.primitiveScale coordinate*Translator.ForcingWhole.whole coordinate x=_
  rw [source]
  rfl

 theorem source_primitive_normalization (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.primitiveScale coordinate*Translator.ForcingWhole.coefficient coordinate= -1 := by
  have meanNonzero : GapEuler.gapMean (1/4:ℝ) coordinate≠0 := by
    intro zero
    have source := GapEuler.gapMean_primitive (1/4:ℝ) (by norm_num) coordinate
    rw [zero,mul_zero] at source
    exact (mul_ne_zero (by norm_num : (1/2:ℂ)≠0) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))) source.symm
  have scalarNonzero : star coordinate.value≠0 := by
    have real : 0<(star coordinate.value).re := by simp only [Complex.star_def,Complex.conj_re];linarith [coordinate.rightHalf]
    exact ne_of_apply_ne Complex.re real.ne'
  unfold Paid.primitiveScale Translator.ForcingWhole.coefficient
  have nonzero : star coordinate.value*GapEuler.gapMean (1/4:ℝ) coordinate≠0 := mul_ne_zero scalarNonzero meanNonzero
  rw [show -star coordinate.value*GapEuler.gapMean (1/4:ℝ) coordinate= -(star coordinate.value*GapEuler.gapMean (1/4:ℝ) coordinate) by ring,inv_neg]
  rw [neg_mul,inv_mul_cancel₀ nonzero]

 theorem original_FP_weighted_derivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x≠0) :
    HasDerivAt (fun y:ℝ=>(y:ℂ)*primitiveFourierRaw coordinate y)
      (star coordinate.value*primitiveFourierRaw coordinate x-Edge.raw (1/4:ℝ) x) x := by
  have source := (OriginalRieszSourceGreen.forcing_weighted_hasDerivAt coordinate x nonzero).const_mul (Paid.primitiveScale coordinate)
  convert! source using 1
  · funext y
    unfold primitiveFourierRaw
    ring
  · unfold primitiveFourierRaw
    have normalization := source_primitive_normalization coordinate
    linear_combination -(Edge.raw (1/4:ℝ) x)*normalization

 theorem original_FP_ordinary_derivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x≠0) :
    HasDerivAt (primitiveFourierRaw coordinate)
      (((star coordinate.value-1)*primitiveFourierRaw coordinate x-Edge.raw (1/4:ℝ) x)/(x:ℂ)) x := by
  have source := (OriginalRieszSourceGreen.forcing_raw_hasDerivAt coordinate x nonzero).const_mul (Paid.primitiveScale coordinate)
  change HasDerivAt (primitiveFourierRaw coordinate) _ x at source
  convert! source using 1
  unfold primitiveFourierRaw
  have normalization := source_primitive_normalization coordinate
  rw [← mul_div_assoc]
  apply congrArg (fun value : ℂ=>value/(x:ℂ))
  linear_combination -(Edge.raw (1/4:ℝ) x)*normalization

 theorem original_FP_raw_continuous (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x≠0) :
    ContinuousAt (primitiveFourierRaw coordinate) x := (original_FP_ordinary_derivative coordinate x nonzero).continuousAt

 theorem original_FP_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    primitiveFourierRaw coordinate (-x)=primitiveFourierRaw coordinate x := by
  unfold primitiveFourierRaw
  rw [Translator.ForcingWhole.raw_even]
end OriginalFourierPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
