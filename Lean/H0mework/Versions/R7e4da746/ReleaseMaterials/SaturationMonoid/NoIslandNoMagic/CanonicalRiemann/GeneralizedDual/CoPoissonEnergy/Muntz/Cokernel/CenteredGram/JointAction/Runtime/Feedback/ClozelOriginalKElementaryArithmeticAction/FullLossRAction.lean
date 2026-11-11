import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.RVolterra
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalFullLossRAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction OriginalKSourceResolventReconstruction
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKExteriorCoPoissonAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R" => burnolDirectRightResolventCLM
local notation "T" => burnolTateReciprocalL2

open private gamma conjugate_zero unitCurrent FT boxProgram boxProgram_actual boxProgram_R unitTailProgram
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram

private def SBWeight (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  (Real.exp (-h/2):ℂ)*burnolRieszReturnRaw c (Real.exp (-h)*x)
private def SBSlope (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  (Real.exp (-h/2):ℂ)*((Real.exp (-h):ℝ) • burnolRieszReturnRawDerivative c (Real.exp (-h)*x))

private theorem SB_derivative (c:BurnolCompletedMellinCoordinate) (h x:ℝ) :
    HasDerivAt (SBWeight c h) (SBSlope c h x) x := by
  have moved:HasDerivAt (fun x:ℝ=>Real.exp (-h)*x) (Real.exp (-h)) x := by
    convert! (hasDerivAt_id x).const_mul (Real.exp (-h)) using 1
    simp
  exact ((burnolRieszReturnRaw_hasDerivAt c _).scomp x moved).const_mul (Real.exp (-h/2):ℂ)

private theorem SB_regular (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    Continuous (SBSlope c h) := by
  unfold SBSlope
  simp only [Complex.real_smul]
  exact (((burnolRieszReturnRawDerivative_continuous c).comp
    (show Continuous (fun x:ℝ=>Real.exp (-h)*x) by fun_prop)).const_mul
      (Real.exp (-h):ℂ)).const_mul (Real.exp (-h/2):ℂ)

private theorem SB_measurable (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    Measurable (SBWeight c h) := by
  unfold SBWeight
  exact (((burnolRieszReturnRaw_continuous c).comp
    (show Continuous (fun x:ℝ=>Real.exp (-h)*x) by fun_prop)).const_mul _).measurable

private def SBSeed (c:BurnolCompletedMellinCoordinate) (h:ℝ) : BurnolL2 :=
  burnolWeightedReciprocalStepSource q (q*Real.exp h) (SBWeight c h) (SBSlope c h)

private theorem SB_source (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    exteriorSource c h 1=T (SBSeed c h) := by
  have positive:(0:ℝ)<q*Real.exp h := mul_pos (by norm_num) (Real.exp_pos _)
  have ordered:q≤q*Real.exp h := by nlinarith [Real.one_le_exp_iff.mpr nn]
  have raw:=weighted_source_coeFn q (q*Real.exp h) (SBWeight c h) (SBSlope c h)
    (by norm_num) ordered (fun x _=>SB_derivative c h x) (SB_regular c h).continuousOn
    (SB_regular c h).measurable
  change (SBSeed c h:ℝ→ℂ)=ᵐ[volume] _ at raw
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (SBSeed c h))
    ((Lp.memLp (SBSeed c h)).ae_eq raw) raw
  apply Lp.ext
  filter_upwards [OriginalKExteriorRVolterra.actual_source_raw c h nn 1,
    burnolTateReciprocalL2_coeFn (SBSeed c h),pulled,volume.ae_ne (0:ℝ),
    volume.ae_ne q,volume.ae_ne (-q),volume.ae_ne (q*Real.exp h),volume.ae_ne (-(q*Real.exp h))]
    with x source tate pull nonzero notLo notNegLo notHi notNegHi
  rw [source,tate,pull]
  have notLower:|x|≠q := by
    intro same
    rcases (abs_eq (by norm_num : (0:ℝ)≤q)).mp same with a|a
    · exact notLo a
    · exact notNegLo a
  have notUpper:|x|≠q*Real.exp h := by
    intro same
    rcases (abs_eq positive.le).mp same with a|a
    · exact notHi a
    · exact notNegHi a
  have incidence:(q < |x| ∧ |x| ≤ q*Real.exp h) ↔ (q ≤ |x| ∧ |x| < q*Real.exp h) := by
    constructor
    · intro inside
      exact ⟨inside.1.le,lt_of_le_of_ne inside.2 notUpper⟩
    · intro inside
      exact ⟨lt_of_le_of_ne inside.1 notLower.symm,inside.2.le⟩
  simp only [burnolTateReciprocalRaw,burnolReciprocalStepSourceRaw,abs_inv,inv_inv,Complex.ofReal_inv]
  unfold OriginalKExteriorRVolterra.shellRaw
  by_cases active:q ≤ |x| ∧ |x| < q*Real.exp h
  · rw [if_pos (incidence.mpr active),if_pos active]
    change (Real.exp (-h/2):ℂ)*burnolRieszReturnRaw c (Real.exp (-h)*|x|)=_
    unfold SBWeight
    field_simp [Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)]
  · rw [if_neg (fun inside=>active (incidence.mp inside)),if_neg active,mul_zero,mul_zero]

private theorem dual_tate (N:ℕ) (v:BurnolL2) :
    DualSource.source N (T v)=T (FiniteForcing.source N v) := by
  have channel (a:ℝ) : ContinuousChannels.channel 1 a (T v)=
      T (ContinuousChannels.channel (-1) a v) := by
    simp only [ContinuousChannels.channel,one_mul,neg_one_mul,map_smul]
    rw [burnolTateReciprocalL2_dilation_inverse]
  have integer (n:ℕ) : ContinuousChannels.channel 1 n (T v)=T (Channels.sourceChannel n v) := by
    simpa only [ContinuousChannels.channel,Channels.sourceChannel,neg_one_mul] using channel n
  unfold DualSource.source FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer,channel]
  rw [map_sub,map_sum]
  congr 1
  exact burnolTateReciprocalL2.integral_comp_comm (ContinuousChannels.channel_integrable (-1) N v)

private theorem SB_finite (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (N:ℕ) :
    DualSource.source N (exteriorSource c h 1)=
      T (weightedPrefix q (q*Real.exp h) (SBWeight c h) (SBSlope c h) N) := by
  rw [SB_source c h nn,dual_tate]
  congr 1
  symm
  exact weighted_prefix_eq_finite_sub_continuous q (q*Real.exp h) (SBWeight c h) (SBSlope c h) N
    (by norm_num) (by nlinarith [Real.one_le_exp_iff.mpr nn])
    (fun x _=>SB_derivative c h x) (SB_regular c h).continuousOn
    (SB_regular c h).measurable (SB_measurable c h)

private theorem SB_reverse_actual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    FullUnit.fullReverse c h 1=
      boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) ConstantDual.value+
        centeringMean c h 1 • ConstantDual.value := by
  have generated:=(burnolTateReciprocalL2.continuous.tendsto _).comp
    (weightedPrefix_tendsto q (q*Real.exp h) (SBWeight c h) (SBSlope c h)
      (by norm_num) (SB_regular c h).continuousOn)
  have actual:=generated.congr' (Eventually.of_forall (fun N=>(SB_finite c h nn N).symm))
  have same:=tendsto_nhds_unique (FullUnit.exterior_reverse_tendsto c h nn 1) actual
  rw [FullUnit.fullReverse,same]
  congr 1
  exact boxProgram_actual _ _ _ _ (by norm_num) (SB_regular c h).continuousOn

/-- The original opposite finite count consumes the actual SB source and its complete unit mean. -/
theorem full_reverse_SB_R (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) :
    R c (FullUnit.fullReverse c h 1)=
      boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) (unitCurrent c zero)+
        centeringMean c h 1 • unitCurrent c zero := by
  rw [SB_reverse_actual c h nn,map_add,map_smul,
    boxProgram_R c _ _ _ _ (by norm_num) (SB_regular c h).continuousOn,
    actual_unit_R]

/-- This complete fixed-source effect contains neither of the old opaque R-loss fields. -/
def completeCoreRCurrent (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) : BurnolL2 :=
  (2*gamma c) • OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h
      (elementaryReverseSource (barC c) (conjugate_zero c zero))-
    (2*gamma (barC c)) • OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h
      (elementaryReverseSource c zero)-
    (((c.value-star c.value)*gamma (barC c))*(1/2:ℂ)) •
      (boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) (unitCurrent c zero)+
          centeringMean c h 1 • unitCurrent c zero-
        FT (boxProgram (bandLower h) 4 (positiveWeight c h 0) (deriv (positiveWeight c h 0))
          (unitCurrent c zero)+centeringMean c h 0 • unitTailProgram (unitCurrent c zero)))

open private reverseCoreRCurrent
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail

private theorem complete_actual (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) : reverseCoreRCurrent c zero h=completeCoreRCurrent c zero h := by
  unfold reverseCoreRCurrent completeCoreRCurrent
  rw [full_reverse_SB_R c zero h nn,full_forward_F_R c zero h 0]
  rfl

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h0" => Real.log stageZeroSonineQ

/-- The original fixed-h core consumes both computed full loss actions at its original parameter. -/
theorem original_core_R_update :
    (((c).value-star (c).value)*gamma (barC c)) •
      R c (coreReverseSource c observation.mathlibZero h0)=
        completeCoreRCurrent c observation.mathlibZero h0 := by
  have nn:0≤h0 := Real.log_nonneg (by norm_num [stageZeroSonineQ])
  exact (OriginalReverseSourceRTail.original_fixed_reverse_R_update observation nontrivial half).trans
    (complete_actual c observation.mathlibZero h0 nn)

/-- The same original finite reverse programme generates the complete effect without an R-loss oracle. -/
theorem original_source_R_programme :
    Tendsto (fun N:Nat=>(((c).value-star (c).value)*gamma (barC c)) •
      R c (DualSource.source N (OriginalKCoefficientBFiniteAction.sourceCore c h0))) atTop
      (𝓝 (completeCoreRCurrent c observation.mathlibZero h0)) := by
  have nn:0≤h0 := Real.log_nonneg (by norm_num [stageZeroSonineQ])
  have generated:=OriginalReverseSourceRTail.original_fixed_source_R_programme observation nontrivial half
  change Tendsto (fun N:Nat=>(((c).value-star (c).value)*gamma (barC c)) •
    R c (DualSource.source N (OriginalKCoefficientBFiniteAction.sourceCore c h0))) atTop
    (𝓝 (reverseCoreRCurrent c observation.mathlibZero h0)) at generated
  rw [complete_actual c observation.mathlibZero h0 nn] at generated
  exact generated

end OriginalFullLossRAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
