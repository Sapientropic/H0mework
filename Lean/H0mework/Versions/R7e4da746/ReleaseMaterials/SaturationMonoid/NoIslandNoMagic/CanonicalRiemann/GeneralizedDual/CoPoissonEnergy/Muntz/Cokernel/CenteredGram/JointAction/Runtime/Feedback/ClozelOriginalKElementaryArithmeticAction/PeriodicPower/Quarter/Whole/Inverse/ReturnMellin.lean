import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativePowerPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open scoped Topology InnerProductSpace
open private log_top_bound logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private mellin_source_ae from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "S"=>burnolMeanZeroTruncatedFourier
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def compactRaw (raw:ℝ→ℂ):ℝ→ℂ:=(symmetricInterval q).indicator raw

private theorem compact_bound (raw:ℝ→ℂ) (regular:Continuous raw):
    ∃B:ℝ,0≤B∧∀x:ℝ,‖compactRaw raw x‖≤B:=by
  obtain ⟨B,bound⟩:=isCompact_Icc.exists_bound_of_continuousOn regular.continuousOn
  refine ⟨max 0 B,le_max_left _ _,fun x=>?_⟩
  by_cases inside:x∈symmetricInterval q
  · rw [compactRaw,indicator_of_mem inside]
    exact (bound x inside).trans (le_max_right _ _)
  · rw [compactRaw,indicator_of_notMem inside,norm_zero]
    exact le_max_left _ _

private theorem compact_memLp (raw:ℝ→ℂ) (regular:Continuous raw):
    MemLp (compactRaw raw) 2 volume:=by
  obtain ⟨B,_,bound⟩:=compact_bound raw regular
  apply (memLp_indicator_iff_restrict (measurableSet_symmetricInterval q)).mpr
  apply MemLp.of_bound regular.aestronglyMeasurable.restrict B
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  simpa only [compactRaw,indicator_of_mem inside] using bound x

private theorem compact_origin (raw:ℝ→ℂ) (regular:Continuous raw):
    compactRaw raw=O[𝓝[>] 0](fun x:ℝ=>x^(-(0:ℝ))):=by
  obtain ⟨B,_,bound⟩:=compact_bound raw regular
  apply Asymptotics.IsBigO.of_bound B
  filter_upwards with x
  simpa only [neg_zero,Real.rpow_zero,norm_one,mul_one] using bound x

private theorem compact_log_origin (raw:ℝ→ℂ) (regular:Continuous raw)
    (j:ℕ) (b:ℝ) (positive:0<b):
    logSource (compactRaw raw) j=O[𝓝[>] 0](fun x:ℝ=>x^(-b)):=by
  have logarithm:(fun x:ℝ=>(Real.log x)^j)=O[𝓝[>] 0](fun x:ℝ=>x^(-b)):=by
    apply Asymptotics.IsBigO.of_norm_left
    simpa only [Real.norm_eq_abs,abs_pow,Real.rpow_natCast] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (j:ℝ) (by linarith:-b<0)).isBigO
  have product:=logarithm.smul (compact_origin raw regular)
  apply product.congr' (EventuallyEq.refl _ _)
  filter_upwards with x
  change x^(-b)*x^(-(0:ℝ))=x^(-b)
  simp

/-- A continuous raw source, actually cut to the original quarter, supplies every logarithmic Mellin integral. -/
theorem actual_compact_log_mellin (raw:ℝ→ℂ) (regular:Continuous raw)
    (j:ℕ) (w:ℂ) (positive:0<w.re):
    MellinConvergent (logSource (compactRaw raw) j) w:=by
  have logarithm:ContinuousOn (fun x:ℝ=>(Real.log x)^j) (Ioi 0):=by
    intro x hx
    exact ((Real.continuousAt_log hx.ne').pow j).continuousWithinAt
  have localSource:LocallyIntegrableOn (logSource (compactRaw raw) j) (Ioi 0):=
    LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (((compact_memLp raw regular).locallyIntegrable (by norm_num)).locallyIntegrableOn _) logarithm
  have outside:∀x:ℝ, q < |x| → compactRaw raw x=0:=by
    intro x beyond
    exact indicator_of_notMem (s:=symmetricInterval q)
      (fun inside=>not_le_of_gt beyond (abs_le.mpr inside)) raw
  exact mellinConvergent_of_isBigO_rpow localSource (log_top_bound _ q outside j (w.re+1))
    (by linarith) (compact_log_origin raw regular j (w.re/2) (by linarith)) (by linarith)

theorem actual_compact_mellin (raw:ℝ→ℂ) (regular:Continuous raw)
    (w:ℂ) (positive:0<w.re):MellinConvergent (compactRaw raw) w:=by
  simpa only [logSource_zero] using actual_compact_log_mellin raw regular 0 w positive

def returnRaw (state:M):ℝ→ℂ:=compactRaw (burnolMeanZeroFourierRaw state)

theorem actual_return_raw (state:M):
    (burnolQuarterZeroExtension (S state:Hq):ℝ→ℂ)=ᵐ[volume]returnRaw state:=
  burnolZeroExtensionMeanZeroFourier_ae_raw state

/-- The return keeps its genuine Fourier mean inside the compact raw source. -/
theorem actual_return_log_mellin (state:M) (j:ℕ) (w:ℂ) (positive:0<w.re):
    MellinConvergent (logSource (returnRaw state) j) w:=by
  exact actual_compact_log_mellin _
    ((burnolRadiusTruncatedFourierRaw_continuous (state:Hq)).sub continuous_const) j w positive

theorem actual_return_mellin (state:M) (w:ℂ) (positive:0<w.re):
    HasMellin (burnolQuarterZeroExtension (S state:Hq):ℝ→ℂ) w (mellin (returnRaw state) w):=by
  apply mellin_source_ae _ _ _ _ (ae_restrict_of_ae (actual_return_raw state))
  exact ⟨by simpa only [logSource_zero] using actual_return_log_mellin state 0 w positive,rfl⟩

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
