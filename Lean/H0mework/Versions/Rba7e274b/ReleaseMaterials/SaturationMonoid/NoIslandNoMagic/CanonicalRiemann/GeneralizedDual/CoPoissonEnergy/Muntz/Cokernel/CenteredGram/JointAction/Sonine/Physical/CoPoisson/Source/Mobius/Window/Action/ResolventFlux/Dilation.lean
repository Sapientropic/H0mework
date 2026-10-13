import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Lower
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory Set
open scoped ArithmeticFunction BigOperators InnerProductSpace

def cutoff (radius : ℝ) : BurnolL2 →L[ℂ] BurnolL2 := (burnolRadiusZeroExtension radius).comp (burnolRadiusRestriction radius)
def box (radius : ℝ) : BurnolL2 := burnolRadiusZeroExtension radius (intervalConstant radius)
def fullPullback (n : ℕ+) : BurnolL2 →L[ℂ] BurnolL2 :=
  (Real.exp (Real.log (n:ℕ)/2):ℂ) • (burnolMultiplicativeDilation (-Real.log (n:ℕ))).toLinearIsometry.toContinuousLinearMap

def tailFlux (shift : ℝ) (value : BurnolL2) : BurnolL2 :=
  ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,coefficient n •
    (cutoff 4 (fullPullback n (burnolMultiplicativeDilation shift value))-
      cutoff (4*Real.exp (-shift)) (fullPullback n (burnolMultiplicativeDilation shift value)))
def meanFlux (shift : ℝ) (value : BurnolL2) : BurnolL2 :=
  ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,coefficient n •
    (-(actualMean (burnolMultiplicativeDilation shift value)) • box 4+
      ((Real.exp (shift/2):ℂ)*actualMean value) • box (4*Real.exp (-shift)))

theorem lower_source_cutoff (value : BurnolL2) : M value =
    ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,coefficient n •
      (cutoff 4 (fullPullback n value)-actualMean value • box 4) := by
  unfold M lowerWindow
  simp only [ContinuousLinearMap.comp_apply,sum_apply,smul_apply,map_sum,map_smul,lowerPullback,sub_apply,map_sub,
    ContinuousLinearMap.toSpanSingleton_apply]
  unfold cutoff fullPullback box burnolWindowScalePullback
  simp only [ContinuousLinearMap.comp_apply,smul_apply,map_smul]
  rfl

theorem full_pullback_action (n : ℕ+) (shift : ℝ) (value : BurnolL2) :
    burnolMultiplicativeDilation shift (fullPullback n value)=fullPullback n (burnolMultiplicativeDilation shift value) := by
  unfold fullPullback
  simp only [smul_apply,map_smul,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
  rw [burnolMultiplicativeDilation_add,burnolMultiplicativeDilation_add,add_comm shift]

theorem cutoff_read (radius : ℝ) (value : BurnolL2) : (cutoff radius value : ℝ→ℂ) =ᵐ[volume]
    (symmetricInterval radius).indicator (value : ℝ→ℂ) := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) value)
  filter_upwards [burnolRadiusZeroExtension_coe (burnolRadiusRestriction radius value),localRead] with x extended read
  rw [cutoff,ContinuousLinearMap.comp_apply,extended]
  by_cases inside : x∈symmetricInterval radius
  · rw [indicator_of_mem inside,indicator_of_mem inside]
    exact read inside
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

theorem box_read (radius : ℝ) : (box radius : ℝ→ℂ) =ᵐ[volume] (symmetricInterval radius).indicator (fun _ => (1:ℂ)) := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp (intervalConstant_coeFn radius)
  filter_upwards [burnolRadiusZeroExtension_coe (intervalConstant radius),localRead] with x extended read
  rw [box,extended]
  by_cases inside : x∈symmetricInterval radius
  · rw [indicator_of_mem inside,indicator_of_mem inside,read inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

theorem action_cutoff (radius : ℝ) (_nonnegative : 0≤radius) (shift : ℝ) (value : BurnolL2) :
    burnolMultiplicativeDilation shift (cutoff radius value) = cutoff (radius*Real.exp (-shift)) (burnolMultiplicativeDilation shift value) := by
  let scale := Real.exp shift
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => scale*x) volume volume := by
    have source : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift • x) (volume : Measure ℝ) volume :=
      Measure.quasiMeasurePreserving_smul (μ:=(volume : Measure ℝ)) (r:=Real.exp shift) (Real.exp_ne_zero shift)
    change Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift*x) volume volume at source
    exact source
  have scaled := qmp.ae_eq (cutoff_read radius value)
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn shift (cutoff radius value),scaled,
    cutoff_read (radius*Real.exp (-shift)) (burnolMultiplicativeDilation shift value),
    burnolMultiplicativeDilation_coeFn shift value] with x moved source fixed direct
  have membership : scale*x∈symmetricInterval radius ↔ x∈symmetricInterval (radius*Real.exp (-shift)) := by
    simp only [symmetricInterval,mem_Icc]
    have pos : 0<scale := Real.exp_pos shift
    have radiusEq : radius*Real.exp (-shift)=radius/scale := by simp only [scale,Real.exp_neg,div_eq_mul_inv]
    rw [radiusEq,← neg_div]
    constructor
    · rintro ⟨lower,upper⟩
      exact ⟨(div_le_iff₀ pos).mpr (by simpa only [mul_comm] using lower),(le_div_iff₀ pos).mpr (by simpa only [mul_comm] using upper)⟩
    · rintro ⟨lower,upper⟩
      exact ⟨by simpa only [mul_comm] using (div_le_iff₀ pos).mp lower,by simpa only [mul_comm] using (le_div_iff₀ pos).mp upper⟩
  rw [moved]
  unfold burnolL2RawNormalizedDilation
  change (Real.exp (shift/2):ℂ)*(cutoff radius value : ℝ→ℂ) (scale*x)=_
  simp only [Function.comp_def] at source
  rw [source,fixed]
  by_cases inside : x∈symmetricInterval (radius*Real.exp (-shift))
  · rw [indicator_of_mem inside,indicator_of_mem (membership.mpr inside),direct]
    rfl
  · rw [indicator_of_notMem inside,indicator_of_notMem (fun h=>inside (membership.mp h)),mul_zero]

theorem action_box (radius : ℝ) (_nonnegative : 0≤radius) (shift : ℝ) :
    burnolMultiplicativeDilation shift (box radius)=(Real.exp (shift/2):ℂ) • box (radius*Real.exp (-shift)) := by
  let scale := Real.exp shift
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => scale*x) volume volume := by
    have source : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift • x) (volume : Measure ℝ) volume :=
      Measure.quasiMeasurePreserving_smul (μ:=(volume : Measure ℝ)) (r:=Real.exp shift) (Real.exp_ne_zero shift)
    change Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift*x) volume volume at source
    exact source
  have scaled := qmp.ae_eq (box_read radius)
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn shift (box radius),scaled,
    box_read (radius*Real.exp (-shift)),Lp.coeFn_smul (Real.exp (shift/2):ℂ) (box (radius*Real.exp (-shift)))] with x moved source fixed scalar
  have membership : scale*x∈symmetricInterval radius ↔ x∈symmetricInterval (radius*Real.exp (-shift)) := by
    simp only [symmetricInterval,mem_Icc]
    have pos : 0<scale := Real.exp_pos shift
    have radiusEq : radius*Real.exp (-shift)=radius/scale := by simp only [scale,Real.exp_neg,div_eq_mul_inv]
    rw [radiusEq,← neg_div]
    constructor
    · rintro ⟨lower,upper⟩
      exact ⟨(div_le_iff₀ pos).mpr (by simpa only [mul_comm] using lower),(le_div_iff₀ pos).mpr (by simpa only [mul_comm] using upper)⟩
    · rintro ⟨lower,upper⟩
      exact ⟨by simpa only [mul_comm] using (div_le_iff₀ pos).mp lower,by simpa only [mul_comm] using (le_div_iff₀ pos).mp upper⟩
  rw [moved,scalar]
  unfold burnolL2RawNormalizedDilation
  change (Real.exp (shift/2):ℂ)*(box radius : ℝ→ℂ) (scale*x)=(Real.exp (shift/2):ℂ)*(box (radius*Real.exp (-shift)) : ℝ→ℂ) x
  simp only [Function.comp_def] at source
  rw [source,fixed]
  by_cases inside : x∈symmetricInterval (radius*Real.exp (-shift))
  · rw [indicator_of_mem inside,indicator_of_mem (membership.mpr inside)]
  · rw [indicator_of_notMem inside,indicator_of_notMem (fun h=>inside (membership.mp h))]

-- The finite action generates every moving outer-window flux and the actual mean response.
theorem finite_source_dilation (shift : ℝ) (value : BurnolL2) :
    M (burnolMultiplicativeDilation shift value)-burnolMultiplicativeDilation shift (M value)=
      tailFlux shift value+meanFlux shift value := by
  rw [lower_source_cutoff,lower_source_cutoff]
  simp only [map_sum,map_smul,map_sub,action_cutoff 4 (by norm_num),action_box 4 (by norm_num),full_pullback_action]
  unfold tailFlux meanFlux
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [smul_sub,smul_add,smul_smul]
  module

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
