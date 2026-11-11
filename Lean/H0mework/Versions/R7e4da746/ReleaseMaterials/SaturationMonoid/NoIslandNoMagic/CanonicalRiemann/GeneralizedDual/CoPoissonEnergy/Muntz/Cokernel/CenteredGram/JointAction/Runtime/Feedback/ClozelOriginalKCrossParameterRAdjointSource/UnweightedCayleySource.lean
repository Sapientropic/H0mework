import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Source.PowerWave
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace ENNReal
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance unweightedQuarterComplete : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private theorem power_source_ne_zero (c : BurnolCompletedMellinCoordinate) : SingularCounting.powerL2 c≠0 := by
  intro vanished
  have zeroRead : (SingularCounting.powerL2 c:ℝ→ℂ)=ᵐ[μq] fun _=>0 := by
    rw [vanished]
    exact Lp.coeFn_zero ℂ 2 μq
  have impossible : ∀ᵐ x:ℝ ∂μq, False := by
    filter_upwards [SingularCounting.power_coeFn c,zeroRead,
      ae_restrict_of_ae (s:=symmetricInterval q) (volume.ae_ne (0:ℝ))] with x native zero nonzero
    have sourceNonzero : SingularCounting.powerRaw c x≠0 := by
      unfold SingularCounting.powerRaw
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)))
    exact sourceNonzero (native.symm.trans zero)
  have empty := ae_iff.mp impossible
  have collapse : μq Set.univ=0 := by simpa only [not_false_eq_true,Set.ofPred_true] using empty
  norm_num [symmetricInterval] at collapse

private theorem two_characters_differ (c : BurnolCompletedMellinCoordinate) :
    (2:ℂ)^(-star c.value)≠(1/2:ℂ) := by
  have exponent : (-1:ℝ)<(-star c.value).re := by
    simpa only [Complex.neg_re,Complex.star_def,Complex.conj_re] using neg_lt_neg c.belowOne
  have strict : (1/2:ℝ)<‖(2:ℂ)^(-star c.value)‖ := by
    change (1/2:ℝ)<‖((2:ℝ):ℂ)^(-star c.value)‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2)]
    have scaled := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) exponent
    norm_num at scaled ⊢
    exact scaled
  intro equal
  rw [equal] at strict
  norm_num at strict

/-- The two actual counting characters distinguish the source power from every constant. -/
theorem centeredPower_ne_zero (c : BurnolCompletedMellinCoordinate) : SingularCounting.centeredPower c≠0 := by
  intro centeredZero
  have read := OriginalRieszSource.Constructor.zeroMean_read (SingularCounting.powerL2 c)
  change (SingularCounting.centeredPower c:BurnolQuarterIntervalL2)=
    SingularCounting.powerL2 c-burnolQuarterMeanCoefficient (SingularCounting.powerL2 c) • intervalConstant q at read
  rw [centeredZero,ZeroMemClass.coe_zero] at read
  have constant : SingularCounting.powerL2 c=
      burnolQuarterMeanCoefficient (SingularCounting.powerL2 c) • intervalConstant q := sub_eq_zero.mp read.symm
  have constantAction : InverseAction.countingWindow (2:ℝ)
      (burnolQuarterMeanCoefficient (SingularCounting.powerL2 c) • intervalConstant q)=
      burnolQuarterMeanCoefficient (SingularCounting.powerL2 c) •
        InverseAction.countingWindow (2:ℝ) (intervalConstant q) := by
    unfold InverseAction.countingWindow
    simp only [map_smul,smul_smul]
    module
  have character : (2:ℂ)^(-star c.value) • SingularCounting.powerL2 c=
      (1/2:ℂ) • SingularCounting.powerL2 c := by
    calc
      _ = InverseAction.countingWindow (2:ℝ) (SingularCounting.powerL2 c) :=
        (SingularCounting.counting_power c 2 (by norm_num)).symm
      _ = InverseAction.countingWindow (2:ℝ)
          (burnolQuarterMeanCoefficient (SingularCounting.powerL2 c) • intervalConstant q) := congrArg _ constant
      _ = _ := constantAction
      _ = _ := by
        rw [SingularCounting.counting_constant 2 (by norm_num)]
        conv_rhs => rw [constant]
        simp only [smul_smul]
        norm_num
        congr 1
        ring
  have annihilated : ((2:ℂ)^(-star c.value)-1/2) • SingularCounting.powerL2 c=0 := by
    rw [sub_smul,character,sub_self]
  exact (smul_eq_zero.mp annihilated).elim
    (sub_ne_zero.mpr (two_characters_differ c)) (power_source_ne_zero c)

private theorem power_reflect (c : BurnolCompletedMellinCoordinate) :
    reflectRestricted q (SingularCounting.powerL2 c)=SingularCounting.powerL2 c := by
  apply Lp.ext
  let reflection := negMeasurePreserving_restrict q
  filter_upwards [Lp.coeFn_compMeasurePreserving (SingularCounting.powerL2 c) reflection,
    reflection.quasiMeasurePreserving.ae (SingularCounting.power_coeFn c),SingularCounting.power_coeFn c]
      with x reflected negative direct
  change reflectRestricted q (SingularCounting.powerL2 c) x=SingularCounting.powerL2 c (-x) at reflected
  rw [reflected,negative,direct]
  simp only [SingularCounting.powerRaw,abs_neg]

private theorem centered_reflect (c : BurnolCompletedMellinCoordinate) :
    reflectRestricted q (SingularCounting.centeredPower c:BurnolQuarterIntervalL2)=
      (SingularCounting.centeredPower c:BurnolQuarterIntervalL2) := by
  change reflectRestricted q (burnolQuarterMeanZeroProjection (SingularCounting.powerL2 c))=_
  rw [←burnolQuarterMeanZeroProjection_reflect,power_reflect]
  rfl

/-- The actual B double block is read before evenPart; only the generated power's parity is used. -/
theorem powerCorrection_quarter_source (c : BurnolCompletedMellinCoordinate) :
    quarterCotest (hPowerPhysicalCorrection c)=SingularCounting.centeredPower c := by
  let raw := burnolQuarterZeroExtension (hPowerBColumn c:BurnolQuarterIntervalL2)+
    fourierL2 (burnolQuarterZeroExtension (hPowerBSecond c:BurnolQuarterIntervalL2))
  have native : burnolQuarterMeanZeroProjection (burnolQuarterRestriction raw)=
      (SingularCounting.centeredPower c:BurnolQuarterIntervalL2) := by
    change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (_+_))=_
    rw [map_add,map_add,burnolQuarterRestriction_zeroExtension,burnolQuarterMeanZeroProjection_coe]
    change (hPowerBColumn c:BurnolQuarterIntervalL2)+
      (burnolMeanZeroTruncatedFourier (hPowerBSecond c):BurnolQuarterIntervalL2)=_
    exact congrArg (fun x:BurnolQuarterMeanZeroCarrier => (x:BurnolQuarterIntervalL2)) (h_power_B_source c).1
  have reflected : burnolQuarterMeanZeroProjection (burnolQuarterRestriction (reflectL2 raw))=
      reflectRestricted q (burnolQuarterMeanZeroProjection (burnolQuarterRestriction raw)) := by
    change burnolQuarterMeanZeroProjection (restrictToInterval q (reflectL2 raw))=_
    rw [restrictToInterval_reflectL2,burnolQuarterMeanZeroProjection_reflect]
    rfl
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (burnolAmbientEvenPart raw))=_
  unfold burnolAmbientEvenPart
  rw [map_smul,map_smul,map_add,map_add,reflected,native,centered_reflect]
  module

theorem powerCorrection_ne_zero (c : BurnolCompletedMellinCoordinate) : hPowerPhysicalCorrection c≠0 := by
  intro vanished
  have read := powerCorrection_quarter_source c
  rw [vanished] at read
  unfold quarterCotest at read
  simp only [map_zero] at read
  exact centeredPower_ne_zero c read.symm

private theorem powerWeight_ne_zero (c : BurnolCompletedMellinCoordinate) :
    ((‖hPowerPhysicalCorrection c‖^2:ℝ):ℂ)≠0 := by
  exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (powerCorrection_ne_zero c))
private theorem damping_ne_zero (c : BurnolCompletedMellinCoordinate) : (sourceDamping c:ℂ)≠0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (sourceDamping_pos c))

def sourceForwardRatio (c : BurnolCompletedMellinCoordinate) : ℂ :=
  sourceSigma c/((‖hPowerPhysicalCorrection (barC c)‖^2:ℝ):ℂ)
/-- Every coefficient is generated by the actual B-power/R source; no target response is read. -/
def sourceFKAction (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (sourceForwardRatio c/(sourceDamping c:ℂ)) • generatedK (barC c)-
    (sourceDamping c:ℂ)⁻¹ • fourierL2 (generatedK c)-
    (2*((‖generatedK c‖^2:ℝ):ℂ)) • physicalOutsideColumn c

def sourceConjugateAdjointAction (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (sourceAdjointRatio c/(sourceDamping c:ℂ)) • fourierL2 (generatedK c)-
    (sourceDamping c:ℂ)⁻¹ • generatedK (barC c)-
    (2*((‖generatedK (barC c)‖^2:ℝ):ℂ)) • hPowerPhysicalCorrection c

private theorem isolate_source (weight damping sigma norm : ℂ) (weightNe : weight≠0) (dampingNe : damping≠0)
    (input response outside target : BurnolL2)
    (action : weight • (input+damping • response+(2*damping*norm) • outside)=sigma • target) :
    response=((sigma/weight)/damping) • target-damping⁻¹ • input-(2*norm) • outside := by
  have unweighted := congrArg (fun x:BurnolL2 => weight⁻¹ • x) action
  rw [smul_smul,inv_mul_cancel₀ weightNe,one_smul,smul_smul] at unweighted
  have source := congrArg (fun x:BurnolL2 => damping⁻¹ • x) unweighted
  simp only [smul_add,smul_smul] at source
  have unit : damping⁻¹*damping=1 := inv_mul_cancel₀ dampingNe
  have cost : damping⁻¹*(2*damping*norm)=2*norm := by
    field_simp [dampingNe]
  rw [unit,one_smul,cost] at source
  linear_combination (norm := module) source

/-- This is the full original R(FK), unweighted by any caller-supplied normalization. -/
theorem original_R_FK_generated (c : BurnolCompletedMellinCoordinate) :
    burnolDirectRightResolvent (c.value/2) (fourierL2 (generatedK c))=sourceFKAction c := by
  exact isolate_source _ _ _ _ (powerWeight_ne_zero (barC c)) (damping_ne_zero c) _ _ _ _
    (source_FK_full_action c)

/-- The independent true adjoint direction keeps its own B-power normalization and full outside field. -/
theorem original_R_adjoint_conjugateK_generated (c : BurnolCompletedMellinCoordinate) :
    sourceAdjoint c (generatedK (barC c))=sourceConjugateAdjointAction c := by
  exact isolate_source _ _ _ _ (powerWeight_ne_zero c) (damping_ne_zero c) _ _ _ _
    (source_conjugateK_full_adjoint_action c)

end OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
