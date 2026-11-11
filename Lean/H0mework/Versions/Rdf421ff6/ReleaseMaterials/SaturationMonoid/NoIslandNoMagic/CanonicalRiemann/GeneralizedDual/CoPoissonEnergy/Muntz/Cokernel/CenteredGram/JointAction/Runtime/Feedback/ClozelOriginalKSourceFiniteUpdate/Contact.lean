import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceGramAction.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Box
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SingularCounting
import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.ColumnIntegral
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Algebra

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalPrimitiveRankBalance
open scoped Topology InnerProductSpace
noncomputable section
local notation "q" => (1/4 : ℝ)

private def contactScale : ℝ := Real.log 4 + Real.log 4

private theorem contact_scale_exp : Real.exp contactScale = 16 := by
  norm_num [contactScale,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)]
private theorem contact_scale_half : Real.exp (contactScale/2) = 4 := by
  rw [show contactScale/2=Real.log 4 by unfold contactScale;ring]
  exact Real.exp_log (by norm_num)
private theorem contact_star_sub_one (c : BurnolCompletedMellinCoordinate) : star c.value-1≠0 := by
  intro zero
  have real := congrArg Complex.re zero
  simp only [Complex.sub_re,Complex.star_def,Complex.conj_re,Complex.one_re,Complex.zero_re] at real
  linarith [c.belowOne]

/-- This zero-boundary compact power is generated before any R or finite target is read. -/
def contactPrimitive (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (star c.value-1)⁻¹ • (ConstantDual.seed -
    (4:ℂ)^(star c.value-1) • burnolQuarterZeroExtension (SingularCounting.powerL2 c))

private theorem contact_box_scale :
    burnolMultiplicativeDilation contactScale (FiniteMobiusResolventFlux.box 4) =
      (4:ℂ) • ConstantDual.seed := by
  rw [FiniteMobiusResolventFlux.action_box 4 (by norm_num),contact_scale_half,Real.exp_neg,contact_scale_exp]
  norm_num
  rfl

private theorem contact_power_scale (s : ℂ) :
    (4:ℂ)^(1-s)*(16:ℂ)^(s-1)=(4:ℂ)^(s-1) := by
  have sixteen : (16:ℂ)^(s-1)=(4:ℂ)^(s-1)*(4:ℂ)^(s-1) := by
    have native := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤4) (by norm_num : (0:ℝ)≤4) (s-1)
    norm_num only [Complex.ofReal_ofNat,show (4:ℂ)*4=16 by norm_num] at native
    exact native
  have cancel : (4:ℂ)^(1-s)*(4:ℂ)^(s-1)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num),show (1-s)+(s-1)=0 by ring,Complex.cpow_zero]
  rw [sixteen,←mul_assoc,cancel,one_mul]

/-- The actual paid box source is restricted by its source dilation, including the power normalization. -/
theorem contactPrimitive_scaled_box (c : BurnolCompletedMellinCoordinate) :
    contactPrimitive c =
      (-1/8:ℂ) • burnolMultiplicativeDilation contactScale (boxSource (conjugateCoordinate c)) := by
  let source := boxSource (conjugateCoordinate c)
  have qmp : Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp contactScale*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ:=(volume:Measure ℝ)) (r:=Real.exp contactScale) (Real.exp_ne_zero _)
  have scaled := qmp.ae_eq (box_source_read (conjugateCoordinate c))
  have power := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (SingularCounting.power_coeFn c)
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul ((star c.value-1)⁻¹)
      (ConstantDual.seed-(4:ℂ)^(star c.value-1) • burnolQuarterZeroExtension (SingularCounting.powerL2 c)),
    Lp.coeFn_sub ConstantDual.seed ((4:ℂ)^(star c.value-1) • burnolQuarterZeroExtension (SingularCounting.powerL2 c)),
    Lp.coeFn_smul ((4:ℂ)^(star c.value-1)) (burnolQuarterZeroExtension (SingularCounting.powerL2 c)),
    ConstantDual.seed_coeFn,burnolQuarterZeroExtension_coe (SingularCounting.powerL2 c),power,
    Lp.coeFn_smul (-1/8:ℂ) (burnolMultiplicativeDilation contactScale source),
    burnolMultiplicativeDilation_coeFn contactScale source,scaled,
    volume.ae_ne (q:ℝ),volume.ae_ne (-q:ℝ)]
      with x outer difference scalar constant extension raw actual dilation sourceRead notQ notNegQ
  change contactPrimitive c x=((-1/8:ℂ) • burnolMultiplicativeDilation contactScale source : BurnolL2) x
  change (((star c.value-1)⁻¹) •
      (ConstantDual.seed-(4:ℂ)^(star c.value-1) • burnolQuarterZeroExtension (SingularCounting.powerL2 c)) : BurnolL2) x=_
  rw [outer,actual]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [dilation]
  change (star c.value-1)⁻¹ * (ConstantDual.seed-
    (4:ℂ)^(star c.value-1) • burnolQuarterZeroExtension (SingularCounting.powerL2 c) : BurnolL2) x=
    (-1/8:ℂ)*burnolL2RawNormalizedDilation contactScale source x
  rw [difference]
  simp only [Pi.sub_apply]
  rw [scalar]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [constant,extension]
  change (star c.value-1)⁻¹ * (ConstantDual.seedRaw x-
    (4:ℂ)^(star c.value-1)*(symmetricInterval q).indicator (SingularCounting.powerL2 c : ℝ→ℂ) x)=_
  unfold burnolL2RawNormalizedDilation
  rw [contact_scale_half]
  change _=(-1/8:ℂ)*(4*(source : ℝ→ℂ) (Real.exp contactScale*x))
  change (source : ℝ→ℂ) (Real.exp contactScale*x) =
    (if |Real.exp contactScale*x|<4 then 2/(1-star c.value)-
      (2*(4:ℂ)^(1-star c.value)/(1-star c.value))*
        ((|Real.exp contactScale*x|:ℝ):ℂ)^(star c.value-1) else 0) at sourceRead
  rw [sourceRead,contact_scale_exp]
  by_cases inside : |x|<q
  · have member : x∈symmetricInterval q := abs_le.mp inside.le
    have moved : |(16:ℝ)*x|<4 := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<16)];linarith
    rw [ConstantDual.seedRaw,if_pos inside.le,indicator_of_mem member,raw member,
      SingularCounting.powerRaw,if_pos moved,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<16),
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤16) (abs_nonneg x)]
    norm_num only [Complex.ofReal_ofNat]
    have normalized := contact_power_scale (star c.value)
    rw [show (2*(4:ℂ)^(1-star c.value)/(1-star c.value))*
        ((16:ℂ)^(star c.value-1)*((|x|:ℝ):ℂ)^(star c.value-1)) =
      (2/(1-star c.value))*
        ((4:ℂ)^(1-star c.value)*(16:ℂ)^(star c.value-1))*
          ((|x|:ℝ):ℂ)^(star c.value-1) by ring,
      normalized,show 1-star c.value=-(star c.value-1) by ring]
    simp only [div_eq_mul_inv,inv_neg]
    ring
  · have notInside : x∉symmetricInterval q := by
      intro member
      have same : |x|=q := le_antisymm (abs_le.mpr member) (le_of_not_gt inside)
      rcases eq_or_eq_neg_of_abs_eq same with same|same
      · exact notQ same
      · exact notNegQ same
    have moved : ¬ |(16:ℝ)*x|<4 := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<16)];linarith [le_of_not_gt inside]
    rw [ConstantDual.seedRaw,if_neg (fun h=>notInside (abs_le.mp h)),indicator_of_notMem notInside,if_neg moved]
    ring

private theorem Rplus_source_dilation (z : ℂ) (right : 1/4<z.re) (h : ℝ) (value : BurnolL2) :
    FiniteMobiusResolventFlux.Rplus z (burnolMultiplicativeDilation h value) =
      burnolMultiplicativeDilation h (FiniteMobiusResolventFlux.Rplus z value) := by
  have move := burnolTateReciprocalL2_dilation_inverse (-h) value
  simp only [neg_neg] at move
  rw [FiniteMobiusResolventFlux.Rplus_tate z right,FiniteMobiusResolventFlux.Rplus_tate z right,
    ←move,burnolDirectRightResolvent_dilation,←burnolTateReciprocalL2_dilation_inverse h]

/-- Box source generation, not a new inverse premise, supplies the complete compact primitive. -/
theorem contactPrimitive_actual (c : BurnolCompletedMellinCoordinate) :
    contactPrimitive c = -(1/2:ℂ) • FiniteMobiusResolventFlux.Rplus (star c.value/2) ConstantDual.seed := by
  have right : 1/4<(star c.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  have source := congrArg (burnolMultiplicativeDilation contactScale)
    (box_Rplus_source (conjugateCoordinate c))
  change burnolMultiplicativeDilation contactScale
      (FiniteMobiusResolventFlux.Rplus (star c.value/2) (FiniteMobiusResolventFlux.box 4)) =
    burnolMultiplicativeDilation contactScale (boxSource (conjugateCoordinate c)) at source
  rw [←Rplus_source_dilation _ right,contact_box_scale,
    FiniteMobiusResolventFlux.Rplus_smul _ _ right] at source
  rw [contactPrimitive_scaled_box,←source,smul_smul]
  norm_num

private theorem contact_seed_even : reflectL2 ConstantDual.seed=ConstantDual.seed := by
  change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=_
  rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
  rfl

theorem contactPrimitive_even (c : BurnolCompletedMellinCoordinate) :
    reflectL2 (contactPrimitive c)=contactPrimitive c := by
  rw [contactPrimitive_actual,map_smul]
  exact congrArg (fun v:BurnolL2=>-(1/2:ℂ) • v)
    (FiniteMobiusResolventFlux.Rplus_even (conjugateCoordinate c) ConstantDual.seed contact_seed_even)

theorem contactPrimitive_fourier_resolvent (c : BurnolCompletedMellinCoordinate) :
    fourierL2 (contactPrimitive c)=-(1/2:ℂ) • sourceResolvent c (fourierL2 ConstantDual.seed) := by
  have right : 1/4<(star c.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  apply fourierL2.injective
  rw [fourierL2_fourierL2,contactPrimitive_even,map_smul]
  change contactPrimitive c=-(1/2:ℂ) •
    fourierL2 (burnolDirectRightResolvent (star c.value/2) (fourierL2 ConstantDual.seed))
  rw [FiniteMobiusResolventFlux.fourier_R _ right,fourierL2_fourierL2,contact_seed_even]
  exact contactPrimitive_actual c

/-- The full weak Euler source of the zero-boundary power has no endpoint delta. -/
theorem contactPrimitive_fourier_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (fourierL2 (contactPrimitive c) : TemperedDistribution ℝ ℂ) +
      sourceRate c • (fourierL2 (contactPrimitive c) : TemperedDistribution ℝ ℂ) =
        (fourierL2 ConstantDual.seed : TemperedDistribution ℝ ℂ) := by
  have generated := sourceResolvent_euler c (fourierL2 ConstantDual.seed)
  rw [contactPrimitive_fourier_resolvent]
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
    (-(1/2:ℂ) • sourceResolvent c (fourierL2 ConstantDual.seed))) +
    sourceRate c • Lp.toTemperedDistributionCLM ℂ volume 2
      (-(1/2:ℂ) • sourceResolvent c (fourierL2 ConstantDual.seed))=_
  simp only [map_smul,Lp.toTemperedDistributionCLM_apply]
  linear_combination (norm := module) -(1/2:ℂ) • generated

def contactEndpointSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation h (fourierL2 (contactPrimitive c)) -
    Complex.exp (-sourceRate c*(h:ℂ)) • fourierL2 (contactPrimitive c)

/-- Both signs of the actual FC primitive are generated by the compact power endpoints. -/
theorem contact_primitive_endpoint (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    nativeIntegral (sourceRate c) (fourierL2 ConstantDual.seed) h = contactEndpointSource c h := by
  have action := OriginalRieszFinitePairing.ColumnIntegral.action_of_euler c
    (fourierL2 (contactPrimitive c)) (fourierL2 ConstantDual.seed) (contactPrimitive_fourier_euler c) h
  have character : fullMellinTranslationCharacter (star c.value) h =
      Complex.exp (-sourceRate c*(h:ℂ)) := by
    unfold fullMellinTranslationCharacter sourceRate
    congr 1
    ring
  rw [character] at action
  exact eq_sub_of_add_eq' action.symm

end
end OriginalKSourceFiniteUpdate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

