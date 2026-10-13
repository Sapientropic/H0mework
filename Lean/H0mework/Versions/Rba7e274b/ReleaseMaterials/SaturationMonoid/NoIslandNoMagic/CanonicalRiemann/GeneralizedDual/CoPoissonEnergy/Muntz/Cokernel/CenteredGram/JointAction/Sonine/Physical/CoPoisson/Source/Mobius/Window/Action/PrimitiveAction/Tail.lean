import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

def powerWindow (coordinate : BurnolCompletedMellinCoordinate) (lower : ℝ) : ℂ :=
  ((4:ℂ)^(1-2*star coordinate.value)-(lower:ℂ)^(1-2*star coordinate.value))/(1-2*star coordinate.value)
def constantWindow (coordinate : BurnolCompletedMellinCoordinate) (lower : ℝ) : ℂ :=
  ((4:ℂ)^(1-star coordinate.value)-(lower:ℂ)^(1-star coordinate.value))/(1-star coordinate.value)
def tailWord (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∑ n∈burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*
    (sourcePower coordinate n*powerWindow coordinate (max x (sourceRadius n))-
      Paid.primitiveMean coordinate*constantWindow coordinate (max x (sourceRadius n)))

theorem source_power_parameters (coordinate : BurnolCompletedMellinCoordinate) :
    1-2*star coordinate.value≠0 ∧ 1-star coordinate.value≠0 := by
  constructor
  · intro zero
    have real := congrArg Complex.re zero
    norm_num [Complex.star_def] at real
    linarith [coordinate.rightHalf]
  · intro zero
    have real := congrArg Complex.re zero
    norm_num [Complex.star_def] at real
    linarith [coordinate.belowOne]

theorem weighted_source_integrable (coordinate : BurnolCompletedMellinCoordinate) (lower : ℝ) (positive : 0<lower) :
    IntegrableOn (fun x : ℝ=>(x:ℂ)^(-star coordinate.value)*
      (if x≤4 then sourceWord coordinate x else 0)) (Ioi lower) := by
  apply (burnolRadiusMellinWeight_integrableOn_tail lower positive (star coordinate.value)
    (by simpa [Complex.star_def] using coordinate.rightHalf)
    (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))).congr
  filter_upwards [ae_restrict_of_ae (original_finite_positive_word coordinate),ae_restrict_mem measurableSet_Ioi] with x source outside
  rw [source (positive.trans outside)]

theorem primitive_tail_source (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) (bounded : x≤4) :
    burnolRadiusMellinTailEvaluator x positive (star coordinate.value)
      (by simpa [Complex.star_def] using coordinate.rightHalf)
      (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))=tailWord coordinate x := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  have sourceRead := original_finite_positive_word coordinate
  have toFinite : (∫ t : ℝ in Ioi x,(t:ℂ)^(-star coordinate.value)*
      Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate) t)=
      ∫ t : ℝ in Ioc x 4,(t:ℂ)^(-star coordinate.value)*sourceWord coordinate t := by
    rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [sourceRead] with t source
    by_cases lower : x<t
    · have tPositive : 0<t := positive.trans lower
      rw [indicator_of_mem (show t∈Ioi x from lower),source tPositive]
      by_cases upper : t≤4
      · rw [if_pos upper,indicator_of_mem (show t∈Ioc x 4 from ⟨lower,upper⟩)]
      · rw [if_neg upper,mul_zero,indicator_of_notMem (show t∉Ioc x 4 from fun h=>upper h.2)]
    · rw [indicator_of_notMem (show t∉Ioi x from lower),indicator_of_notMem (show t∉Ioc x 4 from fun h=>lower h.1)]
  rw [toFinite]
  unfold sourceWord tailWord
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n actual
    have radiusPositive := source_radius_positive n
    have radiusBound := source_radius_bounded n actual
    have lowerPositive : 0<max x (sourceRadius n) := lt_of_lt_of_le positive (le_max_left _ _)
    have lowerBound : max x (sourceRadius n)≤4 := max_le bounded radiusBound.le
    have cell : (∫ t : ℝ in Ioc x 4,(t:ℂ)^(-star coordinate.value)*
        (Paid.coefficient n*(if sourceRadius n<t then sourcePower coordinate n*(t:ℂ)^(-star coordinate.value)-Paid.primitiveMean coordinate else 0)))=
        Paid.coefficient n*(∫ t : ℝ in max x (sourceRadius n)..4,
          sourcePower coordinate n*(t:ℂ)^(-2*star coordinate.value)-Paid.primitiveMean coordinate*(t:ℂ)^(-star coordinate.value)) := by
      rw [intervalIntegral.integral_of_le lowerBound,← integral_const_mul]
      rw [← integral_indicator measurableSet_Ioc,← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases lower : x<t
      · by_cases radial : sourceRadius n<t
        · by_cases top : t≤4
          · rw [indicator_of_mem (show t∈Ioc x 4 from ⟨lower,top⟩),if_pos radial,indicator_of_mem (show t∈Ioc (max x (sourceRadius n)) 4 from ⟨max_lt_iff.mpr ⟨lower,radial⟩,top⟩)]
            have tPositive : 0<t := positive.trans lower
            have power : (t:ℂ)^(-star coordinate.value)*(t:ℂ)^(-star coordinate.value)=(t:ℂ)^(-2*star coordinate.value) := by
              rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr tPositive.ne')]
              congr 1
              ring
            linear_combination Paid.coefficient n*sourcePower coordinate n*power
          · simp only [indicator_of_notMem (show t∉Ioc x 4 from fun h=>top h.2),indicator_of_notMem (show t∉Ioc (max x (sourceRadius n)) 4 from fun h=>top h.2)]
        · by_cases top : t≤4
          · simp only [indicator_of_mem (show t∈Ioc x 4 from ⟨lower,top⟩),if_neg radial,mul_zero,
              indicator_of_notMem (show t∉Ioc (max x (sourceRadius n)) 4 from fun h=>radial ((le_max_right _ _).trans_lt h.1))]
          · simp only [indicator_of_notMem (show t∉Ioc x 4 from fun h=>top h.2),indicator_of_notMem (show t∉Ioc (max x (sourceRadius n)) 4 from fun h=>top h.2)]
      · simp only [indicator_of_notMem (show t∉Ioc x 4 from fun h=>lower h.1),indicator_of_notMem (show t∉Ioc (max x (sourceRadius n)) 4 from fun h=>lower ((le_max_left _ _).trans_lt h.1))]
    rw [cell]
    have powerIntegrable := intervalIntegral.intervalIntegrable_cpow (a:=max x (sourceRadius n)) (b:=4) (r:=-2*star coordinate.value) (μ:=volume) (Or.inr (by rw [uIcc_of_le lowerBound];intro h;exact not_le_of_gt lowerPositive h.1))
    have meanIntegrable := intervalIntegral.intervalIntegrable_cpow (a:=max x (sourceRadius n)) (b:=4) (r:=-star coordinate.value) (μ:=volume) (Or.inr (by rw [uIcc_of_le lowerBound];intro h;exact not_le_of_gt lowerPositive h.1))
    rw [intervalIntegral.integral_sub (powerIntegrable.const_mul _) (meanIntegrable.const_mul _),intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
    rw [integral_cpow (Or.inr ⟨by intro bad;have real := congrArg Complex.re bad;norm_num [Complex.star_def] at real;linarith [coordinate.rightHalf],by rw [uIcc_of_le lowerBound];intro h;exact not_le_of_gt lowerPositive h.1⟩),integral_cpow (Or.inr ⟨by intro bad;have real := congrArg Complex.re bad;norm_num [Complex.star_def] at real;linarith [coordinate.belowOne],by rw [uIcc_of_le lowerBound];intro h;exact not_le_of_gt lowerPositive h.1⟩)]
    unfold powerWindow constantWindow
    norm_num only [Complex.ofReal_ofNat]
    congr 2 <;> congr 1 <;> ring
  · intro n actual
    have integrable : IntegrableOn (fun t:ℝ=>(t:ℂ)^(-star coordinate.value)) (Ioc x 4) := by
      exact (intervalIntegral.intervalIntegrable_cpow (a:=x) (b:=4) (r:=-star coordinate.value) (μ:=volume) (Or.inr (by rw [uIcc_of_le bounded];intro h;exact not_le_of_gt positive h.1))).1
    have twice : IntegrableOn (fun t:ℝ=>(t:ℂ)^(-2*star coordinate.value)) (Ioc x 4) := by
      exact (intervalIntegral.intervalIntegrable_cpow (a:=x) (b:=4) (r:=-2*star coordinate.value) (μ:=volume) (Or.inr (by rw [uIcc_of_le bounded];intro h;exact not_le_of_gt positive h.1))).1
    have keep := ((twice.const_mul (Paid.coefficient n*sourcePower coordinate n)).sub
      (integrable.const_mul (Paid.coefficient n*Paid.primitiveMean coordinate))).indicator (measurableSet_Ioi : MeasurableSet (Ioi (sourceRadius n)))
    apply keep.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
    have tPositive : 0<t := positive.trans inside.1
    by_cases active : sourceRadius n<t
    · simp only [indicator_of_mem (show t∈Ioi (sourceRadius n) from active),Pi.sub_apply,if_pos active]
      have power : (t:ℂ)^(-star coordinate.value)*(t:ℂ)^(-star coordinate.value)=(t:ℂ)^(-2*star coordinate.value) := by
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr tPositive.ne')]
        congr 1
        ring
      linear_combination -Paid.coefficient n*sourcePower coordinate n*power
    · simp only [indicator_of_notMem (show t∉Ioi (sourceRadius n) from active),if_neg active,mul_zero]
end OriginalPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
