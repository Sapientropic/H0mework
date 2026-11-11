import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingCompactPrice

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PaCut
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.UnitCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual
open scoped Topology InnerProductSpace
open private native_zero_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.UnitCounting
open private dual_tate from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
local notation "T"=>burnolTateReciprocalL2
local notation "D"=>burnolMultiplicativeDilation
local notation "ν"=>burnolMobiusSourceL2
local notation "q"=>(1/4:ℝ)
local notation "AN"=>FiniteForcing.source
local notation "DN"=>DualSource.source
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private def radiusShift (r:ℝ):ℝ:=Real.log (4/r)
private def radiusScale (c:BurnolCompletedMellinCoordinate) (r:ℝ):ℂ:=
  (fullMellinTranslationCharacter c.value (radiusShift r))⁻¹

private theorem radius_identity (r:ℝ) (positive:0<r):4*Real.exp (-radiusShift r)=r:=by
  rw [radiusShift,Real.exp_neg,Real.exp_log (div_pos (by norm_num) positive)]
  field_simp

private theorem radius_source (c:BurnolCompletedMellinCoordinate) (r:ℝ) (positive:0<r):
    burnolRadiusNormalizedUnitTail c r positive=
      radiusScale c r • D (radiusShift r) (burnolNormalizedFirstSourceUnitTail c):=by
  have source:=burnolRadiusNormalizedUnitTail_dilation c 4 (by norm_num) (radiusShift r)
  simp only [radius_identity r positive] at source
  change D (radiusShift r) (burnolNormalizedFirstSourceUnitTail c)=
    fullMellinTranslationCharacter c.value (radiusShift r) • burnolRadiusNormalizedUnitTail c r positive at source
  rw [source,smul_smul,radiusScale,inv_mul_cancel₀ (show fullMellinTranslationCharacter c.value (radiusShift r)≠0 from Complex.exp_ne_zero _),one_smul]

private theorem radius_value (c:BurnolCompletedMellinCoordinate) (r:ℝ) (admitted:r∈Icc q 4):
    burnolUnitTailResponse c r=radiusScale c r • D (radiusShift r) (burnolUnitTailResponse c 4):=by
  have positive:0<r:=by linarith [admitted.1]
  have bound:r⁻¹≤4:=by
    rw [show (4:ℝ)=(q:ℝ)⁻¹ by norm_num,inv_le_inv₀ positive (by norm_num)]
    exact admitted.1
  have value:=burnolUnitTailResponse_radius_dilation c 4 (by norm_num) (by norm_num)
    (radiusShift r) (by simpa only [radius_identity r positive] using bound)
  rw [radius_identity r positive] at value
  rw [value,smul_smul,radiusScale,inv_mul_cancel₀ (show fullMellinTranslationCharacter c.value (radiusShift r)≠0 from Complex.exp_ne_zero _),one_smul]

private theorem radius_finite (c:BurnolCompletedMellinCoordinate) (r:ℝ) (positive:0<r) (N:ℕ):
    AN N (burnolRadiusNormalizedUnitTail c r positive)=
      radiusScale c r • D (radiusShift r) (AN N (burnolNormalizedFirstSourceUnitTail c)):=by
  rw [radius_source]
  change CountingDual.sourceCLM N (_ • _)=_
  rw [map_smul]
  exact congrArg (fun v:BurnolL2=>radiusScale c r • v) (SeedCounting.source_dilation N _ _)

/-- The actual counted Unit programme generates the whole closed radius family. -/
theorem actual_radius_forward (c:BurnolCompletedMellinCoordinate) (r:ℝ) (admitted:r∈Icc q 4):
    Tendsto (fun N:ℕ=>AN N (burnolRadiusNormalizedUnitTail c r (by linarith [admitted.1]))) atTop
      (𝓝 (burnolUnitTailResponse c r)):=by
  have base:=actual_native_unit_zero_forward c
  rw [native_zero_source] at base
  have generated:=(((D (radiusShift r)).continuous.tendsto _).comp base).const_smul (radiusScale c r)
  rw [←radius_value c r admitted] at generated
  exact generated.congr' (Eventually.of_forall (fun N=>(radius_finite c r (by linarith [admitted.1]) N).symm))

private theorem radius_scale_bound (c:BurnolCompletedMellinCoordinate):
    ∃B:ℝ,0≤B∧∀r∈Icc q 4,‖radiusScale c r‖≤B:=by
  have logContinuous:ContinuousOn radiusShift (Icc q 4):=by
    apply ContinuousOn.log
    · exact continuousOn_const.div continuousOn_id (fun r hr=>(by linarith [hr.1]:r≠0))
    · intro r hr
      exact div_ne_zero (by norm_num) (by linarith [hr.1]:r≠0)
  have scaleContinuous:ContinuousOn (radiusScale c) (Icc q 4):=by
    apply ContinuousOn.inv₀
    · exact Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn logContinuous))
    · intro r _
      exact Complex.exp_ne_zero _
  obtain ⟨B,bounds⟩:=isCompact_Icc.exists_bound_of_continuousOn scaleContinuous
  exact ⟨max B 0,le_max_right _ _,fun r hr=>(bounds r hr).trans (le_max_left _ _)⟩

private theorem radius_forward_bound (c:BurnolCompletedMellinCoordinate):
    ∃B:ℝ,0≤B∧∀(r:ℝ)(hr:r∈Icc q 4),∀N:ℕ,
      ‖AN N (burnolRadiusNormalizedUnitTail c r (by linarith [hr.1]))‖≤B:=by
  have base:=actual_native_unit_zero_forward c
  rw [native_zero_source] at base
  obtain ⟨M,bounds⟩:=(Metric.isBounded_range_of_tendsto _ base).exists_norm_le
  obtain ⟨B,nonnegative,scaleBound⟩:=radius_scale_bound c
  refine ⟨B*max M 0,mul_nonneg nonnegative (le_max_right _ _),?_⟩
  intro r hr N
  rw [radius_finite,norm_smul,(D (radiusShift r)).norm_map]
  exact mul_le_mul (scaleBound r hr) ((bounds _ (mem_range_self N)).trans (le_max_left _ _))
    (norm_nonneg _) nonnegative

private theorem shell_source (c:BurnolCompletedMellinCoordinate) (u:ℝ) (inside:u∈Icc q 4):
    ν (volterraPhysicalShell c u)=
      -(burnolRadiusNormalizedUnitTail c u⁻¹ (by
        have h:=volterraShell_reciprocal_admitted u inside
        linarith [h.1])-burnolNormalizedFirstSourceUnitTail c):=by
  rw [volterraPhysicalShell,dif_pos inside,map_neg,closedShellState_source]

/-- Each actual Pa shell has its own full reverse counting graph, including the complete Unit difference. -/
theorem actual_shell_reverse (c:BurnolCompletedMellinCoordinate) (u:ℝ) (inside:u∈Icc q 4):
    Tendsto (fun N:ℕ=>DN N (T (ν (volterraPhysicalShell c u)))) atTop
      (𝓝 (T (volterraPhysicalShell c u:BurnolL2))):=by
  have radius:=actual_radius_forward c u⁻¹ (volterraShell_reciprocal_admitted u inside)
  have base:=actual_native_unit_zero_forward c
  rw [native_zero_source] at base
  have forward:=((burnolTateReciprocalL2.continuous.tendsto _).comp ((radius.sub base).neg))
  have same:(volterraPhysicalShell c u:BurnolL2)=
      -(burnolUnitTailResponse c u⁻¹-burnolUnitTailResponse c 4):=by
    rw [volterraPhysicalShell,dif_pos inside,Submodule.coe_neg,closedShellState_eq_tail_sub]
  rw [←same] at forward
  apply forward.congr'
  apply Eventually.of_forall
  intro N
  change T (-(AN N (burnolRadiusNormalizedUnitTail c u⁻¹ _) - AN N (burnolNormalizedFirstSourceUnitTail c)))=
    DN N (T (ν (volterraPhysicalShell c u)))
  rw [dual_tate,shell_source c u inside]
  simp only [←CountingDual.sourceCLM_apply,map_neg,map_sub]

private theorem norm_tate (v:BurnolL2):‖T v‖=‖v‖:=burnolTateReciprocalValue_norm v

private theorem shell_reverse_bound (c:BurnolCompletedMellinCoordinate):
    ∃B:ℝ,0≤B∧∀u∈Icc q 4,∀N:ℕ,‖DN N (T (ν (volterraPhysicalShell c u)))‖≤B:=by
  obtain ⟨B,nonnegative,bound⟩:=radius_forward_bound c
  refine ⟨2*B,by positivity,?_⟩
  intro u inside N
  rw [dual_tate,norm_tate,shell_source c u inside]
  change ‖CountingDual.sourceCLM N (-(_-_))‖≤_
  rw [map_neg,map_sub,norm_neg]
  have first:=bound u⁻¹ (volterraShell_reciprocal_admitted u inside) N
  have second:=bound 4 (by norm_num) N
  change ‖CountingDual.sourceCLM N (burnolRadiusNormalizedUnitTail c u⁻¹ _)‖≤B at first
  change ‖CountingDual.sourceCLM N (burnolNormalizedFirstSourceUnitTail c)‖≤B at second
  exact (norm_sub_le _ _).trans (by linarith)

private def sourceMap:BurnolPaAmbientCarrier →L[ℂ] BurnolL2:=
  burnolTateReciprocalL2.comp burnolMobiusSourceL2
private def valueMap:BurnolPaAmbientCarrier →L[ℂ] BurnolL2:=
  burnolTateReciprocalL2.comp
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL

/-- The actual shell synthesis supplies the sharp reverse graph of its generated Pa state. -/
theorem actual_volterra_reverse (c:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    Tendsto (fun N:ℕ=>DN N (T (ν (sourceVolterraPhysical c value)))) atTop
      (𝓝 (T (sourceVolterraPhysical c value:BurnolL2))):=by
  obtain ⟨B,nonnegative,bound⟩:=shell_reverse_bound c
  have integrable:=sourceVolterraPhysical_integrable c value
  have weighted:IntegrableOn (fun u:ℝ=>‖volterraSourceDensity c value u‖*B) (Icc q 4):=
    (volterraSourceDensity_integrableOn c value).norm.mul_const B
  have measurable (N:ℕ):AEStronglyMeasurable
      (fun u:ℝ=>volterraSourceDensity c value u • DN N (T (ν (volterraPhysicalShell c u))))
      (volume.restrict (Icc q 4)):=by
    have native:=(((CountingDual.sourceCLM N).adjoint.comp sourceMap).integrable_comp integrable).aestronglyMeasurable
    simpa only [sourceMap,ContinuousLinearMap.comp_apply,map_smul,←CountingDual.dual_eq_adjoint] using native
  have limits:∀ᵐu:ℝ ∂volume.restrict (Icc q 4),
      Tendsto (fun N:ℕ=>volterraSourceDensity c value u • DN N (T (ν (volterraPhysicalShell c u)))) atTop
        (𝓝 (volterraSourceDensity c value u • T (volterraPhysicalShell c u:BurnolL2))):=by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u inside
    exact (actual_shell_reverse c u inside).const_smul _
  have bounded (N:ℕ):∀ᵐu:ℝ ∂volume.restrict (Icc q 4),
      ‖volterraSourceDensity c value u • DN N (T (ν (volterraPhysicalShell c u)))‖≤
        ‖volterraSourceDensity c value u‖*B:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u inside
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (bound u inside N) (norm_nonneg _)
  have generated:=tendsto_integral_of_dominated_convergence
    (fun u:ℝ=>‖volterraSourceDensity c value u‖*B) measurable weighted bounded limits
  have finite (N:ℕ):DN N (T (ν (sourceVolterraPhysical c value)))=
      ∫u:ℝ in Icc q 4,volterraSourceDensity c value u • DN N (T (ν (volterraPhysicalShell c u))):=by
    simp only [CountingDual.dual_eq_adjoint]
    change ((CountingDual.sourceCLM N).adjoint.comp sourceMap)
      (∫u:ℝ in Icc q 4,volterraSourceDensity c value u • volterraPhysicalShell c u)=_
    rw [←((CountingDual.sourceCLM N).adjoint.comp sourceMap).integral_comp_comm integrable]
    apply integral_congr_ae
    filter_upwards with u
    simp only [sourceMap,ContinuousLinearMap.comp_apply,map_smul]
  have target:T (sourceVolterraPhysical c value:BurnolL2)=
      ∫u:ℝ in Icc q 4,volterraSourceDensity c value u • T (volterraPhysicalShell c u:BurnolL2):=by
    change valueMap (∫u:ℝ in Icc q 4,volterraSourceDensity c value u • volterraPhysicalShell c u)=_
    rw [←valueMap.integral_comp_comm integrable]
    apply integral_congr_ae
    filter_upwards with u
    simp only [valueMap,ContinuousLinearMap.comp_apply,map_smul,Submodule.subtypeL_apply]
  rw [←target] at generated
  exact generated.congr' (Eventually.of_forall (fun N=>(finite N).symm))

/-- The whole original annulus at every positive order has a generated strong graph and its full Pa value. -/
theorem actual_joint_annulus_reverse (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    Tendsto (fun N:ℕ=>DN N (sourceAnnulusCut (tateSource c (j+1)))) atTop
      (𝓝 (T (enrichedPa c j:BurnolL2))):=by
  have second:=(actual_shell_reverse (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4 (by norm_num)).const_smul
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate.forcingCoefficient c j)
  have first:=actual_volterra_reverse (OriginalPrimitiveRankBalance.conjugateCoordinate c) (tateSource c j)
  change Tendsto (fun N:ℕ=>DN N (T (ν (actualPa c j)))) atTop
    (𝓝 (T (actualPa c j:BurnolL2))) at first
  have generated:=first.add second
  have finite (N:ℕ):DN N (sourceAnnulusCut (tateSource c (j+1)))=
      DN N (T (ν (actualPa c j)))+
        OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate.forcingCoefficient c j •
          DN N (T (ν (volterraPhysicalShell (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4))):=by
    rw [←actual_enriched_pa_source,enrichedPa,map_add,map_smul,map_add,map_smul]
    simp only [CountingDual.dual_eq_adjoint]
    rw [map_add,map_smul]
  have target:T (enrichedPa c j:BurnolL2)=T (actualPa c j:BurnolL2)+
      OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate.forcingCoefficient c j •
        T (volterraPhysicalShell (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4:BurnolL2):=by
    rw [enrichedPa,Submodule.coe_add,Submodule.coe_smul,map_add,map_smul]
  rw [←target] at generated
  exact generated.congr' (Eventually.of_forall (fun N=>(finite N).symm))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PaCut
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
