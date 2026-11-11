import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalReentrySourceAction.Physical
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
open Complex MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Pa" => burnolCompactCoPoissonClosedRange.toSubmodule
local instance logPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance logPaComplete : CompleteSpace ↥Pa := by
  apply IsComplete.completeSpace_coe
  exact burnolCompactCoPoissonClosedRange.isClosed.isComplete

/-- The finite source weight is defined before either correction or r action is read. -/
def sourceLogWeight (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (-(4:ℂ)*(x:ℂ)^(-c.value)*(Real.log (x/q):ℂ))
private theorem sourceLogWeight_continuousOn (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (sourceLogWeight c) (Icc q 4) := by
  intro x inside
  have positive : 0<x := by linarith [inside.1]
  have power := Complex.continuousAt_ofReal_cpow_const x (-c.value) (Or.inr positive.ne')
  have divided : ContinuousAt (fun t : ℝ=>t/q) x := continuousAt_id.div_const q
  have logAt : ContinuousAt Real.log (x/q) := Real.continuousAt_log (div_ne_zero positive.ne' (by norm_num))
  have logarithm : ContinuousAt (fun t : ℝ=>Real.log (t/q)) x := ContinuousAt.comp (f:=fun t : ℝ=>t/q) (x:=x) logAt divided
  have complexLog : ContinuousAt (fun t : ℝ=>(Real.log (t/q):ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp logarithm
  exact (((continuousAt_const.mul power).mul complexLog).star).continuousWithinAt
private theorem sourceLogWeight_memLp (c : BurnolCompletedMellinCoordinate) :
    MemLp ((Icc q 4).indicator (sourceLogWeight c)) 2 volume := by
  have measured : Measurable (sourceLogWeight c) := by unfold sourceLogWeight;fun_prop
  obtain ⟨bound,bounds⟩ := isCompact_Icc.exists_bound_of_continuousOn (sourceLogWeight_continuousOn c)
  apply (memLp_indicator_iff_restrict measurableSet_Icc).mpr
  apply MemLp.of_bound measured.aestronglyMeasurable bound
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact bounds x inside

def sourceLogKernel (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (sourceLogWeight_memLp c).toLp ((Icc q 4).indicator (sourceLogWeight c))
def sourceLogCoefficient (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  (innerSL ℂ (sourceLogKernel c)).comp (burnolTateReciprocalL2.comp burnolMobiusSourceL2)
def sourceLogRiesz (c : BurnolCompletedMellinCoordinate) : ↥Pa :=
  (InnerProductSpace.toDual ℂ ↥Pa).symm
    ((sourceLogCoefficient c).comp burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL)
/-- The actual shell source gives the logarithm with both original source endpoints. -/
theorem volterra_shell_source_coefficient (c : BurnolCompletedMellinCoordinate)
    (u : ℝ) (inside : u∈Icc q 4) :
    burnolPaResolventSourceCoefficient c (volterraPhysicalShell c u)=2*(Real.log (u/q):ℂ) := by
  change (2:ℂ)*burnolMellinTailEvaluator c.value c.rightHalf
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 (volterraPhysicalShell c u)))=_
  rw [burnolMellinTailEvaluator_eq_integral]
  change (2:ℂ)*(∫ t : ℝ in Ioi q, (t:ℂ)^(-c.value)*burnolTateReciprocalL2
    (burnolMobiusSourceL2 (volterraPhysicalShell c u)) t)=_
  have native := volterraPhysicalShell_tate_source_raw c u inside
  have profile : (fun t : ℝ => (t:ℂ)^(-c.value)*
      burnolTateReciprocalL2 (burnolMobiusSourceL2 (volterraPhysicalShell c u)) t)
      =ᵐ[volume.restrict (Ioi q)] (Iic u).indicator (fun t : ℝ => (t:ℂ)⁻¹) := by
    filter_upwards [ae_restrict_of_ae native,ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (volume.ae_ne u)] with t sourceRead after notUpper
    have positive : 0<t := lt_trans (by norm_num : (0:ℝ)<q) after
    rw [sourceRead,abs_of_pos positive]
    by_cases upper : t≤u
    · rw [if_pos ⟨after.le,lt_of_le_of_ne upper notUpper⟩,indicator_of_mem (show t∈Iic u from upper)]
      rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),
        show -c.value+(c.value-1)=(-1:ℂ) by ring,Complex.cpow_neg_one]
    · rw [if_neg (fun h=>upper h.2.le),indicator_of_notMem (show t∉Iic u from upper),mul_zero]
  rw [integral_congr_ae profile,integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have domain : Iic u∩Ioi q=Ioc q u := by ext t;simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc];exact and_comm
  rw [domain,←intervalIntegral.integral_of_le inside.1]
  simp_rw [←Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal,integral_inv_of_pos (by norm_num : (0:ℝ)<q) (by linarith [inside.1])]

private theorem sourceLogKernel_read (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (sourceLogKernel c) value=
      ∫ t : ℝ in Icc q 4, (-(4:ℂ)*(t:ℂ)^(-c.value)*(Real.log (t/q):ℂ))*value t := by
  rw [L2.inner_def]
  have raw := (sourceLogWeight_memLp c).coeFn_toLp
  have same : (fun t : ℝ => inner ℂ (sourceLogKernel c t) (value t))=ᵐ[volume]
      (Icc q 4).indicator (fun t : ℝ => (-(4:ℂ)*(t:ℂ)^(-c.value)*(Real.log (t/q):ℂ))*value t) := by
    filter_upwards [raw] with t read
    change sourceLogKernel c t=_ at read
    rw [read]
    by_cases inside : t∈Icc q 4
    · rw [indicator_of_mem inside,indicator_of_mem inside]
      simp only [sourceLogWeight,RCLike.inner_apply,starRingEnd_apply,star_star]
      ring
    · rw [indicator_of_notMem inside,indicator_of_notMem inside,inner_zero_left]
  rw [integral_congr_ae same,integral_indicator measurableSet_Icc]

/-- This is the complete source action, from the paid Bochner shell synthesis. -/
theorem correction_source_log_action (c : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p∈burnolCompactCoPoissonClosedRange) :
    burnolPaResolventSourceCoefficient c (burnolPaSourceCorrection c ⟨p,inside⟩)=sourceLogCoefficient c p := by
  rw [←sourceVolterraPhysical_original_correction c p inside]
  unfold sourceVolterraPhysical
  rw [←(burnolPaResolventSourceCoefficient c).integral_comp_comm
    (sourceVolterraPhysical_integrable c (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))]
  change (∫ u : ℝ in Icc q 4, burnolPaResolventSourceCoefficient c
      (volterraSourceDensity c (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) u • volterraPhysicalShell c u))=
    inner ℂ (sourceLogKernel c) (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))
  rw [sourceLogKernel_read]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u admitted
  dsimp only
  rw [map_smul,volterra_shell_source_coefficient c u admitted]
  change volterraSourceDensity c (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) u*(2*(Real.log (u/q):ℂ))=_
  unfold volterraSourceDensity
  ring

/-- The log weight generates the entire adjoint action on the original Pa coefficient covector. -/
theorem correction_adjoint_r_source (c : BurnolCompletedMellinCoordinate) :
    (InnerProductSpace.toDual ℂ ↥Pa).symm
      ((innerSL ℂ (paCoefficientSource c)).comp (burnolPaSourceCorrection c))=sourceLogRiesz c := by
  apply ext_inner_right ℂ
  intro p
  rw [InnerProductSpace.toDual_symm_apply]
  change inner ℂ (paCoefficientSource c) (burnolPaSourceCorrection c p)=inner ℂ (sourceLogRiesz c) p
  rw [paCoefficientSource_read c _ (burnolPaSourceCorrection_mem c p)]
  have read := InnerProductSpace.toDual_symm_apply (𝕜:=ℂ)
    (x:=p) (y:=(sourceLogCoefficient c).comp burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL)
  change inner ℂ (sourceLogRiesz c) p=sourceLogCoefficient c (p : BurnolPaAmbientCarrier) at read
  rw [read,correction_source_log_action c p p.property]

/-- The same original Pa source and full inverse source drive the next actual coefficient, including both fees. -/
theorem actual_next_sourceCoefficient (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
    OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)=
      sourceLogCoefficient c (OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth ordinal)+
      OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal*
        burnolPaResolventSourceCoefficient c
          (OriginalKCombCofinalPaAction.E (OriginalKDirectRCofinalPaUpdate.sourceWholeUnit observation nontrivial half : BurnolL2))+
      inner ℂ (fourierL2 (burnolUnitTailResponse (OriginalPrimitiveRankBalance.conjugateCoordinate c) 4))
          (OriginalKCombCofinalPaAction.Q (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal) : BurnolL2)*
        burnolPaResolventSourceCoefficient c
          (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector c : BurnolPaAmbientCarrier) := by
  dsimp only
  let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
  have step := congrArg (burnolPaResolventSourceCoefficient c)
    (OriginalKDirectRCofinalReentrySourceAction.actual_Pa_successor_Q_reentry observation nontrivial half depth ordinal)
  rw [map_add,map_add,map_smul,map_smul] at step
  have correction := (OriginalKDirectRCofinalMobiusSourceAction.generated_correction_original observation nontrivial half depth ordinal).trans
    (OriginalKDirectRCofinalMobiusSourceAction.source_correction_original observation nontrivial half depth ordinal)
  rw [correction,correction_source_log_action] at step
  exact step

end OriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
