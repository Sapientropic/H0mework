import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierMellin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Mellin.EvenGaussian
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.GammaMellin
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierTail OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierMellin
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
open scoped Topology InnerProductSpace
open private mellin_source_ae from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "Eq"=>burnolQuarterZeroExtension

theorem actual_inverse_extension_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (Eq (sourceInverse c zero:Hq):ℝ→ℂ)=ᵐ[volume]compactRaw (inverseRaw c zero):=by
  have localRead:∀ᵐ x:ℝ ∂volume,x∈symmetricInterval q→(sourceInverse c zero:Hq) x=inverseRaw c zero x:=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (actual_inverse_raw c zero)
  filter_upwards [burnolRadiusZeroExtension_coe (sourceInverse c zero:Hq),localRead] with x extended raw
  change (burnolRadiusZeroExtension q (sourceInverse c zero:Hq):BurnolL2) x=_
  rw [extended]
  by_cases inside:x∈symmetricInterval q
  · rw [compactRaw,indicator_of_mem inside,indicator_of_mem inside,raw inside]
  · rw [compactRaw,indicator_of_notMem inside,indicator_of_notMem inside]

theorem actual_inverse_extension_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (positive:0<w.re):
    HasMellin (Eq (sourceInverse c zero:Hq):ℝ→ℂ) w
      (mellin (compactRaw (inverseRaw c zero)) w):=
  mellin_source_ae _ _ _ _ (ae_restrict_of_ae (actual_inverse_extension_raw c zero))
    ⟨actual_compact_mellin _ (actual_inverse_continuous c zero) w positive,rfl⟩

private theorem actual_compact_inverse_read (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (w:ℂ):
    mellin (compactRaw (inverseRaw c zero)) (1-w)=
      ∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-w)*inverseRaw c zero x:=by
  unfold mellin
  simp only [smul_eq_mul,show (1-w)-1= -w by ring]
  have cut:EqOn (fun x:ℝ=>(x:ℂ)^(-w)*compactRaw (inverseRaw c zero) x)
      ((Ioc (0:ℝ) q).indicator (fun x:ℝ=>(x:ℂ)^(-w)*inverseRaw c zero x)) (Ioi 0):=by
    intro x positive
    change 0<x at positive
    dsimp only
    by_cases below:x≤q
    · rw [compactRaw,indicator_of_mem (show x∈symmetricInterval q from ⟨by linarith,below⟩),
        indicator_of_mem (show x∈Ioc (0:ℝ) q from ⟨positive,below⟩)]
    · rw [compactRaw,indicator_of_notMem (show x∉symmetricInterval q from fun hx=>below hx.2),mul_zero,
        indicator_of_notMem (show x∉Ioc (0:ℝ) q from fun hx=>below hx.2)]
  rw [setIntegral_congr_fun measurableSet_Ioi cut,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr Ioc_subset_Ioi_self,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]

/-- The original a_H pays both Gaussian/Fubini domains and its actual complementary compact integral. -/
theorem actual_inverse_gamma_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (positive:0<w.re) (below:w.re<1):
    HasMellin (fourierL2 (Eq (sourceInverse c zero:Hq)):ℝ→ℂ) w
      ((Gammaℝ w/Gammaℝ (1-w))*(∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-w)*inverseRaw c zero x)):=by
  have complementPositive:0<(1-w).re:=by simp only [sub_re,one_re];linarith
  have position:=actual_inverse_extension_mellin c zero (1-w) complementPositive
  have frequency:=actual_inverse_fourier_hasMellin c zero w positive below
  have even:reflectL2 (Eq (sourceInverse c zero:Hq))=Eq (sourceInverse c zero:Hq):=by
    rw [show Eq=burnolRadiusZeroExtension q from rfl,burnolRadiusZeroExtension_reflect,
      actual_inverse_reflection c zero]
  have generated:=OriginalKElementaryArithmeticAction.PeriodicPower.Mellin.EvenGaussian.actual_fourier_mellin
    (Eq (sourceInverse c zero:Hq)) even w positive below position.1 frequency.1
  refine ⟨frequency.1,?_⟩
  rw [generated,position.2,actual_compact_inverse_read]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.GammaMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
