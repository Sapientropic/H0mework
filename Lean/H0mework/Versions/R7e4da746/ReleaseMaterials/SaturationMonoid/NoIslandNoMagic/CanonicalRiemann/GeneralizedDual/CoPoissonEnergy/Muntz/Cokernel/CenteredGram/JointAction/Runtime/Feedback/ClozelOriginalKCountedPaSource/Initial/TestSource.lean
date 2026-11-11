import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.Whole
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.Weighted
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.RemainderCompact

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial
open Complex Filter MeasureTheory Set
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped BigOperators Topology InnerProductSpace
local notation "q" => (1/4:ℝ)

/-- One derivative inventory generates both original Fourier parities. -/
def sourceDerivative (g:burnolCompactAnnulusSource) : ℝ→ℂ := deriv g.1

private theorem derivative_continuous (g:burnolCompactAnnulusSource) :
    Continuous (sourceDerivative g) := (SchwartzMap.derivCLM ℂ ℂ g.1).continuous

private theorem derivative_read (g:burnolCompactAnnulusSource) (u:ℝ) :
    HasDerivAt g.1 (sourceDerivative g u) u := g.1.hasDerivAt u

private theorem source_abs (g:burnolCompactAnnulusSource) (x:ℝ) : g.1 |x|=g.1 x := by
  by_cases h:0≤x
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h),g.2.1]

private theorem weighted_source_raw (g:burnolCompactAnnulusSource) (x:ℝ) :
    g.1 (|x|⁻¹)*burnolReciprocalStepSourceRaw q 4 x=burnolCompactAdditiveSource g x := by
  by_cases zero:x=0
  · subst x
    simp [burnolReciprocalStepSourceRaw,burnolCompactAdditiveSource]
  have input:g.1 (|x|⁻¹)=g.1 x⁻¹ := by rw [←abs_inv,source_abs]
  unfold burnolReciprocalStepSourceRaw
  by_cases active:q≤|x|⁻¹ ∧ |x|⁻¹<4
  · rw [if_pos active,burnolCompactAdditiveSource,if_neg zero,input,mul_comm]
  · have gone:g.1 (|x|⁻¹)=0 := by
      by_cases low:|x|⁻¹≤q
      · exact g.2.2.1 _ (by simpa only [abs_inv,abs_abs] using low)
      · exact g.2.2.2 _ (by
          rw [abs_of_nonneg (inv_nonneg.mpr (abs_nonneg x))]
          exact le_of_not_gt (fun top=>active ⟨(lt_of_not_ge low).le,top⟩))
    rw [if_neg active,mul_zero,burnolCompactAdditiveSource,if_neg zero,←input,gone,mul_zero]

/-- The source is the actual reciprocal source of this same compact generator. -/
theorem weighted_source (g:burnolCompactAnnulusSource) :
    burnolWeightedReciprocalStepSource q 4 g.1 (sourceDerivative g)=
      burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState g) := by
  apply ext_inner_left ℂ
  intro test
  rw [burnolWeightedReciprocalStepSource_pairing q 4 g.1 (sourceDerivative g)
    (by norm_num) (by norm_num) (fun u _=>derivative_read g u)
    (derivative_continuous g).continuousOn (derivative_continuous g).measurable,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolMobiusSourceExtension_compact_coeFn g] with x sourceRead
  change _=inner ℂ (test x) (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState g) x)
  change burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState g) x=burnolCompactAdditiveSource g x at sourceRead
  rw [sourceRead,weighted_source_raw]

/-- Head and mean belong to the source; realization identifies its unchanged Pa landing. -/
theorem weighted_landing (g:burnolCompactAnnulusSource) :
    burnolWeightedReciprocalStepWave q 4 g.1 (sourceDerivative g)=
      (burnolCompactAdditivePhysicalState g:BurnolL2) := by
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F:=ℂ) (μ:=volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    (burnolWeightedReciprocalStepWave q 4 g.1 (sourceDerivative g))) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolCompactAdditivePhysicalState g:BurnolL2)) test
  rw [←burnolWeightedReciprocalStepSource_realizes q 4 g.1 (sourceDerivative g)
    (by norm_num) (by norm_num) le_rfl (derivative_continuous g).continuousOn,
    weighted_source,burnolRemainderSourceRead_compact,
    Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [burnolCompactAdditiveL2_coeFn g] with x landingRead
  change test x*burnolCompactAdditiveCoSum g x=test x*burnolCompactAdditiveL2 g x
  rw [landingRead]

private theorem wave_upper_continuous :
    ContinuousOn (fun u:ℝ=>burnolReciprocalStepNativeWave u 4) (Icc q 4) := by
  exact continuousOn_const.sub ((burnolSourceScalePrimitive_continuous burnolUnitCountingPrimitiveL2).mono
    (fun _ inside=>lt_of_lt_of_le (by norm_num) inside.1))

theorem source_fields_integrable (g:burnolCompactAnnulusSource) (p:Fin 2) :
    IntegrableOn (fun u:ℝ=>sourceDerivative g u • testField p u 4) (Ioc q 4) := by
  have regular:ContinuousOn (fun u:ℝ=>testField p u 4) (Icc q 4) := by
    by_cases zero:p=0
    · simpa only [testField,if_pos zero] using wave_upper_continuous
    · simpa only [testField,if_neg zero,Function.comp_def] using
        fourierL2.continuous.comp_continuousOn wave_upper_continuous
  exact ((derivative_continuous g).continuousOn.smul regular).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The upper-endpoint anchoring consumes the full f(4) term through FTC. -/
theorem upper_anchor (g:burnolCompactAnnulusSource) :
    burnolWeightedReciprocalStepWave q 4 g.1 (sourceDerivative g)=
      ∫ u:ℝ in Ioc q 4,sourceDerivative g u • burnolReciprocalStepNativeWave u 4 := by
  have derivativeIntegral:IntegrableOn (sourceDerivative g) (Ioc q 4) :=
    (derivative_continuous g).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have sourceIntegral:IntegrableOn (fun u:ℝ=>sourceDerivative g u • burnolReciprocalStepNativeWave u 4) (Ioc q 4) := by
    simpa only [testField,ite_true] using source_fields_integrable g 0
  have step (u:ℝ):burnolReciprocalStepNativeWave q u=
      burnolReciprocalStepNativeWave q 4-burnolReciprocalStepNativeWave u 4 := by
    unfold burnolReciprocalStepNativeWave
    abel
  have integralRead:(∫u:ℝ in Ioc q 4,sourceDerivative g u) =g.1 4-g.1 q := by
    rw [←intervalIntegral.integral_of_le (by norm_num : q≤4)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _=>derivative_read g u)
      ((derivative_continuous g).intervalIntegrable q 4)
  have complete:(∫u:ℝ in Ioc q 4,sourceDerivative g u • burnolReciprocalStepNativeWave q u)=
      (g.1 4-g.1 q) • burnolReciprocalStepNativeWave q 4-
        ∫u:ℝ in Ioc q 4,sourceDerivative g u • burnolReciprocalStepNativeWave u 4 := by
    calc
      _ = ∫u:ℝ in Ioc q 4,sourceDerivative g u • burnolReciprocalStepNativeWave q 4-
          sourceDerivative g u • burnolReciprocalStepNativeWave u 4 := by
        apply integral_congr_ae
        filter_upwards with u
        rw [step u,smul_sub]
      _ = _ := by
        rw [integral_sub (derivativeIntegral.smul_const _) sourceIntegral,integral_smul_const,integralRead]
  unfold burnolWeightedReciprocalStepWave
  rw [complete,g.2.2.1 q (by norm_num),sub_zero]
  abel

theorem generator_fields (g:burnolCompactAnnulusSource) (p:Fin 2) :
    (burnolCompactCoPoissonGenerator (g,p):BurnolL2)=
      ∫u:ℝ in Ioc q 4,sourceDerivative g u • testField p u 4 := by
  have base: (burnolCompactAdditivePhysicalState g:BurnolL2)=
      ∫u:ℝ in Ioc q 4,sourceDerivative g u • burnolReciprocalStepNativeWave u 4 :=
    (weighted_landing g).symm.trans (upper_anchor g)
  by_cases zero:p=0
  · simpa only [burnolCompactCoPoissonGenerator,testField,if_pos zero] using base
  · simp only [burnolCompactCoPoissonGenerator,if_neg zero]
    change fourierL2 (burnolCompactAdditivePhysicalState g:BurnolL2)=_
    rw [base]
    calc
      _ = ∫u:ℝ in Ioc q 4,fourierL2 (sourceDerivative g u • burnolReciprocalStepNativeWave u 4) :=
        (fourierL2.toLinearIsometry.integral_comp_comm _).symm
      _ = _ := by simp only [map_smul,testField,if_neg zero]

/-- Source-linear arithmetic data: the generator is in the second inner slot. -/
def baseBill (g:burnolCompactAnnulusSource) (p:Fin 2) (b:ℝ) : ℂ :=
  2*(∫u:ℝ in Ioc q 4,sourceDerivative g u * star (arithmeticKernel p u 4 b))

theorem baseBill_read (g:burnolCompactAnnulusSource) (p:Fin 2) (b:ℝ) (hb:0<b) :
    baseBill g p b=inner ℂ
      (ContinuousChannels.channel 1 b (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))))
      (burnolCompactCoPoissonGenerator (g,p):BurnolL2) := by
  have square (u:ℝ) (inside:u∈Ioc q 4) :
      sourceDerivative g u * star (arithmeticKernel p u 4 b)=
        inner ℂ (ContinuousChannels.channel 1 b (fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))))
          (sourceDerivative g u • testField p u 4) := by
    rw [arithmeticKernel_read p u 4 b inside.1 inside.2 le_rfl hb,←starRingEnd_apply,inner_conj_symm,inner_smul_right]
  have integralRead: (∫u:ℝ in Ioc q 4,sourceDerivative g u * star (arithmeticKernel p u 4 b))=
      inner ℂ (ContinuousChannels.channel 1 b (fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))))
        (burnolCompactCoPoissonGenerator (g,p):BurnolL2) := by
    rw [generator_fields]
    exact (setIntegral_congr_fun measurableSet_Ioc square).trans
      (integral_inner (source_fields_integrable g p) _)
  rw [baseBill,integralRead]
  simp only [two_smul,ContinuousChannels.channel,map_add,smul_add,inner_add_left]
  ring

end CountedPaInitial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
