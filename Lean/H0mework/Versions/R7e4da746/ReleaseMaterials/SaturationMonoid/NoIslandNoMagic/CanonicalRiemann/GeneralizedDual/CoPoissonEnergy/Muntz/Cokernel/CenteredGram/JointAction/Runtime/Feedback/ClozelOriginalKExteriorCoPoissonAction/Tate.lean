import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RieszEulerDomain
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.FullUnit

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorCoPoissonAction.Tate
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKExteriorCoPoissonAction
open scoped Topology InnerProductSpace BigOperators
open private weight_regular_band weight_derivative_band from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Source
local notation "q"=>(1/4:ℝ)
local notation "J"=>burnolTateReciprocalL2

/-- The reciprocal weight is generated from the literal original exterior programme. -/
def dualWeight (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) (t:ℝ) : ℂ :=
  (t:ℂ)⁻¹*positiveWeight c h i t⁻¹
private def dualSlope (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) (t:ℝ) : ℂ :=
  (-1/(t:ℂ)^2)*positiveWeight c h i t⁻¹+
    (t:ℂ)⁻¹*((-1/t^2:ℝ) • deriv (positiveWeight c h i) t⁻¹)
private theorem dual_derivative (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2)
    (t:ℝ) (positive:0<t) : HasDerivAt (dualWeight c h i) (dualSlope c h i t) t := by
  have inverse : HasDerivAt (fun x:ℝ=>x⁻¹) (-1/t^2) t := (hasDerivAt_id t).inv positive.ne'
  have complexInverse : HasDerivAt (fun x:ℝ=>(x:ℂ)⁻¹) (-1/(t:ℂ)^2) t :=
    (Complex.ofRealCLM.hasDerivAt).inv (Complex.ofReal_ne_zero.mpr positive.ne')
  exact complexInverse.mul ((positiveWeight_hasDerivAt c h i t⁻¹ (inv_pos.mpr positive)).scomp t inverse)
private theorem dual_regular (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) :
    ContinuousOn (deriv (dualWeight c h i)) (Ioi 0) := by
  have regular : ContinuousOn (dualSlope c h i) (Ioi 0) := by
    intro t positive
    have invMap : ContinuousAt (fun x:ℝ=>x⁻¹) t := continuousAt_id.inv₀ positive.ne'
    have f := (positiveWeight_hasDerivAt c h i t⁻¹ (inv_pos.mpr positive)).continuousAt.comp invMap
    have df := ((positiveWeight_deriv_continuousOn c h i).continuousAt
      (Ioi_mem_nhds (inv_pos.mpr positive))).comp invMap
    have castNe : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
    exact (((continuousAt_const.div (Complex.continuous_ofReal.continuousAt.pow 2) (pow_ne_zero _ castNe)).mul f).add
      ((Complex.continuous_ofReal.continuousAt.inv₀ castNe).mul
        ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero _ positive.ne')).smul df))).continuousWithinAt
  exact regular.congr (fun t positive=>(dual_derivative c h i t positive).deriv)
private theorem dual_measurable (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) :
    Measurable (dualWeight c h i) :=
  Complex.measurable_ofReal.inv.mul ((positiveWeight_measurable c h i).comp measurable_inv)
private theorem dual_order (h:ℝ) (nonnegative:0≤h) : q≤q*Real.exp h :=
  le_mul_of_one_le_right (by norm_num) (Real.one_le_exp_iff.mpr nonnegative)
private theorem dual_upper (h:ℝ) (bounded:h≤Real.log 2) : q*Real.exp h≤4 := by
  have exp := Real.exp_le_exp.mpr bounded
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at exp
  linarith
private theorem dual_derivative_band (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) :
    ∀t∈Icc q (q*Real.exp h),HasDerivAt (dualWeight c h i) (deriv (dualWeight c h i) t) t := by
  intro t inside
  exact (dual_derivative c h i t (lt_of_lt_of_le (by norm_num) inside.1)).differentiableAt.hasDerivAt
private theorem dual_regular_band (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) :
    ContinuousOn (deriv (dualWeight c h i)) (Icc q (q*Real.exp h)) :=
  (dual_regular c h i).mono (fun t inside=>lt_of_lt_of_le (by norm_num) inside.1)

def dualSource (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) : BurnolL2 :=
  burnolWeightedReciprocalStepSource q (q*Real.exp h) (dualWeight c h i) (deriv (dualWeight c h i))
def dualWave (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) : BurnolL2 :=
  burnolWeightedReciprocalStepWave q (q*Real.exp h) (dualWeight c h i) (deriv (dualWeight c h i))

private theorem original_tate_raw (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (i:Fin 2) :
    (J (exteriorSource c h i):ℝ→ℂ)=ᵐ[volume]
      fun x=>if bandLower h≤|x| ∧ |x|<4 then positiveWeight c h i |x| else 0 := by
  have source := weighted_source_coeFn (bandLower h) 4 (positiveWeight c h i) (deriv (positiveWeight c h i))
    (bandLower_pos h) (bandLower_le_four h nn) (weight_derivative_band c h i)
    (weight_regular_band c h i) (measurable_deriv _)
  change (exteriorSource c h i:ℝ→ℂ)=ᵐ[volume] _ at source
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (exteriorSource c h i))
    ((Lp.memLp (exteriorSource c h i)).ae_eq source) source
  filter_upwards [burnolTateReciprocalL2_coeFn (exteriorSource c h i),pulled,volume.ae_ne (0:ℝ)] with x read pull nonzero
  rw [read,pull]
  simp only [burnolTateReciprocalRaw,burnolReciprocalStepSourceRaw,abs_inv,inv_inv,Complex.ofReal_inv]
  by_cases active : bandLower h≤|x| ∧ |x|<4
  · rw [if_pos active,if_pos active]
    field_simp [Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)]
  · rw [if_neg active,if_neg active,mul_zero,mul_zero]
private theorem avoid_absolute (a:ℝ) : ∀ᵐx:ℝ ∂volume,|x|≠a := by
  filter_upwards [volume.ae_ne a,volume.ae_ne (-a)] with x direct reflected
  rcases le_total 0 x with positive|negative
  · rwa [abs_of_nonneg positive]
  · rw [abs_of_nonpos negative]
    intro same
    apply reflected
    linarith

/-- The same original source supplies its Tate face, including both actual endpoints. -/
theorem source_tate (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (i:Fin 2) :
    dualSource c h i=J (exteriorSource c h i) := by
  have generated:=weighted_source_coeFn q (q*Real.exp h) (dualWeight c h i) (deriv (dualWeight c h i))
    (by norm_num) (dual_order h nn) (dual_derivative_band c h i) (dual_regular_band c h i) (measurable_deriv _)
  apply Lp.ext
  filter_upwards [generated,original_tate_raw c h nn i,avoid_absolute (bandLower h),avoid_absolute 4,
    volume.ae_ne (0:ℝ)] with x generatedAt originalAt lowerNe upperNe nonzero
  change dualSource c h i x=_ at generatedAt
  rw [generatedAt,originalAt]
  have absolute : 0< |x| := abs_pos.mpr nonzero
  have reciprocal : (q*Real.exp h)⁻¹=bandLower h := by
    unfold bandLower
    rw [Real.exp_neg]
    field_simp
  have incidence : q≤|x|⁻¹ ∧ |x|⁻¹<q*Real.exp h ↔ bandLower h≤|x| ∧ |x|<4 := by
    have first : q≤|x|⁻¹ ↔ |x|≤4 := by
      simpa using (inv_le_inv₀ (by norm_num : (0:ℝ)<4) absolute)
    have second : |x|⁻¹<q*Real.exp h ↔ bandLower h< |x| := by
      have actual:=inv_lt_inv₀ absolute (bandLower_pos h)
      rw [←reciprocal,inv_inv] at actual
      simpa only [reciprocal] using actual
    rw [first,second]
    constructor
    · rintro ⟨upper,lower⟩
      exact ⟨lower.le,lt_of_le_of_ne upper upperNe⟩
    · rintro ⟨lower,upper⟩
      exact ⟨upper.le,lt_of_le_of_ne lower lowerNe.symm⟩
  unfold burnolReciprocalStepSourceRaw
  by_cases active : bandLower h≤|x| ∧ |x|<4
  · rw [if_pos (incidence.mpr active),if_pos active]
    unfold dualWeight
    simp only [inv_inv,Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr absolute.ne']
  · rw [if_neg (fun hx=>active (incidence.mp hx)),if_neg active,mul_zero]

/-- Fourier acts after the generated source, without replacing either source occurrence. -/
theorem wave_fourier (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) (i:Fin 2) :
    dualWave c h i=fourierL2 (exteriorWave c h i) := by
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F:=ℂ) (μ:=volume))
  ext test
  have original:=burnolRemainderRealization_fourier (exteriorSource c h i) (exteriorWave c h i)
    (fun test=>by rw [actual_exterior_source c h nn i];exact exterior_wave_realizes c h nn i test) test
  have generated:=burnolWeightedReciprocalStepSource_realizes q (q*Real.exp h) (dualWeight c h i)
    (deriv (dualWeight c h i)) (by norm_num) (dual_order h nn) (dual_upper h bounded) (dual_regular_band c h i) test
  change burnolRemainderSourceRead (dualSource c h i) test=(dualWave c h i:TemperedDistribution ℝ ℂ) test at generated
  rw [source_tate c h nn i] at generated
  exact generated.symm.trans original

private theorem same_N_tate (N:ℕ) (value:BurnolL2) :
    J (DualSource.source N value)=FiniteForcing.source N (J value) := by
  have channel (a:ℝ) : J (ContinuousChannels.channel 1 a value)=ContinuousChannels.channel (-1) a (J value) := by
    unfold ContinuousChannels.channel
    rw [map_smul,one_mul,neg_one_mul]
    congr 1
    simpa only [neg_neg] using (burnolTateReciprocalL2_dilation_inverse (-Real.log a) value).symm
  unfold DualSource.source FiniteForcing.source ContinuousChannels.normalization
  rw [map_sub,map_sum,←burnolTateReciprocalL2.integral_comp_comm (ContinuousChannels.channel_integrable 1 N value)]
  simp_rw [channel]
  simp only [ContinuousChannels.channel,Channels.sourceChannel,neg_one_mul]

/-- Both independent strong sequences meet through their actual same-N action. -/
theorem actual_fourier_reverse (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) (i:Fin 2) :
    fourierL2 (exteriorWave c h i)=J (FullUnit.exteriorReverse c h i) := by
  have direct:=weightedPrefix_tendsto q (q*Real.exp h) (dualWeight c h i) (deriv (dualWeight c h i))
    (by norm_num) (dual_regular_band c h i)
  have reverse:=(burnolTateReciprocalL2.continuous.tendsto _).comp (FullUnit.exterior_reverse_tendsto c h nn i)
  have same : (fun N:ℕ=>weightedPrefix q (q*Real.exp h) (dualWeight c h i) (deriv (dualWeight c h i)) N)=
      (fun N:ℕ=>J (DualSource.source N (exteriorSource c h i))) := by
    funext N
    rw [weighted_prefix_eq_finite_sub_continuous _ _ _ _ N (by norm_num) (dual_order h nn)
      (dual_derivative_band c h i) (dual_regular_band c h i) (measurable_deriv _) (dual_measurable c h i)]
    change FiniteForcing.source N (dualSource c h i)=_
    rw [source_tate c h nn i, same_N_tate]
  have converted:=direct.congr' (Eventually.of_forall (fun N=>congrFun same N))
  have identified:=tendsto_nhds_unique converted reverse
  change dualWave c h i=J (FullUnit.exteriorReverse c h i) at identified
  rw [wave_fourier c h nn bounded i] at identified
  exact identified

/-- The full original centering mean is transported with the same two complete sources. -/
theorem actual_full_fourier_reverse (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) (i:Fin 2) :
    fourierL2 (FullUnit.fullForward c h i)=J (FullUnit.fullReverse c h i) := by
  rw [FullUnit.fullForward,FullUnit.fullReverse,map_add,map_smul,map_add,map_smul,
    actual_fourier_reverse c h nn bounded i,ConstantFourier.original_square,ConstantFourier.reciprocal_value]

end OriginalKExteriorCoPoissonAction.Tate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
