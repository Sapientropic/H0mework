import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.Collar
import H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ColumnGapMass
import H0mework.Versions.R7e4da746.Arithmetic.RieszColumns.Half
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszSource BurnolPhysicalState.OriginalRieszSourceGreen
open BurnolPhysicalState.OriginalRieszFinitePairing BurnolPhysicalState.OriginalRieszFiniteColumns
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre
open OriginalKExteriorCoPoissonAction OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
private def cutMap (r:ℝ) : BurnolL2 →L[ℂ] BurnolL2 := (burnolRadiusZeroExtension r).comp (burnolRadiusRestriction r)

def coreCharacterDefect (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  pairedMellinTranslationCharacter c.value h-pairedMellinTranslationCharacter (star c.value) h

/-- Only the position foot is compactified; the full Fourier loss is retained separately. -/
def positionCoreSource (c:BurnolCompletedMellinCoordinate) (h:ℝ) : BurnolL2 :=
  -(1/2:ℂ) • (gapDilationDifference c h+gapDilationDifference c (-h)+FullUnit.fullSource c h 1)

def compressedCoreSource (c:BurnolCompletedMellinCoordinate) (h:ℝ) : M :=
  Constructor.zeroMean (R (burnolMultiplicativeDilation (Real.log 2) (positionCoreSource c h)))

theorem core_two_foot_source (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    sourceCore c h=coreCharacterDefect c h • elementarySource c+positionCoreSource c h+
      (1/2:ℂ) • fourierL2 (FullUnit.fullSource c h 0) := by
  unfold sourceCore finiteBoundaryAction coreCharacterDefect positionCoreSource gapDilationDifference
  change _ = _ • elementarySource c + -(1/2:ℂ) •
    (burnolMultiplicativeDilation h (elementarySource c)-fullMellinTranslationCharacter (star c.value) h • elementarySource c+
      (burnolMultiplicativeDilation (-h) (elementarySource c)-fullMellinTranslationCharacter (star c.value) (-h) • elementarySource c)+
      fullWindowLoss h (sourceSB c))+(1/2:ℂ) • fourierL2 (fullWindowLoss h (sourceB c))
  have negchar : fullMellinTranslationCharacter (star c.value) (-h)=reciprocalMellinTranslationCharacter (star c.value) h := by
    unfold fullMellinTranslationCharacter reciprocalMellinTranslationCharacter
    congr 1
    push_cast
    ring
  unfold pairedMellinTranslationCharacter
  rw [negchar]
  module

private theorem ext_support (r:ℝ) (le:q≤r) (v:Hq) : cutMap r (E v)=E v := by
  change OriginalPaPhysicalGreen.originalPhysicalCutoff r (E v)=_
  simpa only [neg_zero,Real.exp_zero,mul_one,burnolMultiplicativeDilation_zero] using
    intervalDilation_cutoff_self v 0 r (by simpa using le)

private theorem exp_bound (h:ℝ) (bound:|h|≤Real.log 2) : Real.exp (-h)≤2 := by
  have e:=Real.exp_le_exp.mpr ((neg_le_abs h).trans bound)
  simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using e

private theorem gap_support (c:BurnolCompletedMellinCoordinate) (h:ℝ) (bound:|h|≤Real.log 2) :
    cutMap (1/2) (gapDilationDifference c h)=gapDilationDifference c h := by
  have shifted : cutMap (1/2) (burnolMultiplicativeDilation h (E (sourceSB c:Hq))) =
      burnolMultiplicativeDilation h (E (sourceSB c:Hq)) := by
    apply intervalDilation_cutoff_self
    have le:=exp_bound h bound
    norm_num at le ⊢
    linarith
  have reconstruction : gapDilationDifference c h=positionColumn c h-
      burnolMultiplicativeDilation h (E (sourceSB c:Hq))+
        fullMellinTranslationCharacter (star c.value) h • E (sourceSB c:Hq) := by
    rw [positionColumn_action]
    change _ = burnolMultiplicativeDilation h (gapState c+E (sourceSB c:Hq))-
      fullMellinTranslationCharacter (star c.value) h • (gapState c+E (sourceSB c:Hq))-_+_
    unfold gapDilationDifference
    rw [map_add]
    module
  rw [reconstruction,map_add,map_sub,map_smul]
  rw [show cutMap (1/2) (positionColumn c h)=positionColumn c h from positionColumn_half c h bound,
    shifted,ext_support (1/2) (by norm_num)]

private theorem loss_inventory (h:ℝ) (v:M) :
    fullWindowLoss h v=burnolMultiplicativeDilation (-h) (E (v:Hq))-
      E (meanZeroDilation (-h) v:Hq) := by
  have actual:=outward_full_source_inventory h v
  linear_combination (norm:=module) -actual

private theorem loss_support (h:ℝ) (_nn:0≤h) (bound:h≤Real.log 2) (v:M) :
    cutMap (1/2) (fullWindowLoss h v)=fullWindowLoss h v := by
  rw [loss_inventory,map_sub]
  congr 1
  · apply intervalDilation_cutoff_self
    have e:=Real.exp_le_exp.mpr bound
    rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at e
    simp only [neg_neg]
    linarith
  · exact ext_support (1/2) (by norm_num) _

theorem position_core_support (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff (1/2) (positionCoreSource c h)=positionCoreSource c h := by
  change cutMap (1/2) _=_
  rw [positionCoreSource,map_smul,map_add,map_add,gap_support c h (by rwa [abs_of_nonneg nn]),
    gap_support c (-h) (by rwa [abs_neg,abs_of_nonneg nn])]
  change _ • (_+_+cutMap (1/2) (fullWindowLoss h (sourceSB c)))=_
  rw [loss_support h nn bound]
  rfl

private theorem extension_mass (v:Hq) : (∫x:ℝ,E v x)=∫x in symmetricInterval q,v x := by
  rw [integral_congr_ae (burnolQuarterZeroExtension_coe v),integral_indicator (measurableSet_symmetricInterval q)]

private theorem mean_zero_mass (v:M) : (∫x:ℝ,E (v:Hq) x)=0 := by
  rw [extension_mass]
  have zero:=Constructor.mean_zero v
  rw [Constructor.mean_integral] at zero
  linear_combination zero/2

private theorem dilation_mass (v:BurnolL2) (h:ℝ) :
    (∫x:ℝ,burnolMultiplicativeDilation h v x)=(Real.exp (-h/2):ℂ)*(∫x:ℝ,v x) := by
  rw [integral_congr_ae (burnolMultiplicativeDilation_coeFn h v)]
  unfold burnolL2RawNormalizedDilation
  rw [integral_const_mul,Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr (Real.exp_pos h)),
    Complex.real_smul,Complex.ofReal_inv,←mul_assoc]
  congr 1
  rw [←Complex.ofReal_inv,←Complex.ofReal_mul,←Real.exp_neg,←Real.exp_add]
  congr 2
  ring

private theorem loss_mass (h:ℝ) (_nn:0≤h) (bound:h≤Real.log 2) (v:M) :
    (∫x:ℝ,fullWindowLoss h v x)=0 := by
  have a:=intervalDilation_cutoff_self (v:Hq) (-h) (1/2) (by
    have e:=Real.exp_le_exp.mpr bound
    rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at e
    simp only [neg_neg];linarith)
  have ai:=integrable_of_cutoff_eq_self (1/2) _ a
  have bi:=integrable_of_cutoff_eq_self (1/2) _ (ext_support (1/2) (by norm_num) (meanZeroDilation (-h) v:Hq))
  rw [loss_inventory,integral_congr_ae (Lp.coeFn_sub _ _)]
  simp only [Pi.sub_apply]
  rw [integral_sub ai bi,dilation_mass,mean_zero_mass,mean_zero_mass,mul_zero,sub_zero]

theorem position_core_mass (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    (∫x:ℝ,positionCoreSource c h x)=0 := by
  have ai:=gapDilationDifference_integrable c h
  have bi:=gapDilationDifference_integrable c (-h)
  have ci:Integrable (FullUnit.fullSource c h 1 : ℝ→ℂ):=
    integrable_of_cutoff_eq_self (1/2) _ (loss_support h nn bound (sourceSB c))
  rw [positionCoreSource,integral_congr_ae (Lp.coeFn_smul _ _)]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [integral_const_mul,integral_congr_ae (Lp.coeFn_add _ _)]
  simp only [Pi.add_apply]
  have abi:Integrable (gapDilationDifference c h+gapDilationDifference c (-h):BurnolL2) :=
    (ai.add bi).congr (Lp.coeFn_add _ _).symm
  rw [integral_add abi ci,integral_congr_ae (Lp.coeFn_add _ _)]
  simp only [Pi.add_apply]
  rw [integral_add ai bi,gapDilationDifference_integral_zero,gapDilationDifference_integral_zero]
  change _*(0+0+∫x:ℝ,fullWindowLoss h (sourceSB c) x)=0
  rw [loss_mass h nn bound]
  norm_num

private theorem restricted_reflection (r:ℝ) (v:BurnolL2) :
    burnolRadiusRestriction r (reflectL2 v)=reflectRestricted r (burnolRadiusRestriction r v) :=
  restrictToInterval_reflectL2 r v

private theorem cut_reflection (r:ℝ) (v:BurnolL2) : reflectL2 (cutMap r v)=cutMap r (reflectL2 v) := by
  change reflectL2 (burnolRadiusZeroExtension r (burnolRadiusRestriction r v))=_
  rw [burnolRadiusZeroExtension_reflect]
  change burnolRadiusZeroExtension r (reflectRestricted r (burnolRadiusRestriction r v))=
    burnolRadiusZeroExtension r (burnolRadiusRestriction r (reflectL2 v))
  rw [restricted_reflection]

theorem position_core_even (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    reflectL2 (positionCoreSource c h)=positionCoreSource c h := by
  have evenE:reflectL2 (gapState c)=gapState c:=burnolAmbientEvenPart_even _
  have evenV:reflectL2 (E (sourceSB c:Hq))=E (sourceSB c:Hq) := by
    change reflectL2 (burnolRadiusZeroExtension q (Constructor.returnState c:Hq))=burnolRadiusZeroExtension q (Constructor.returnState c:Hq)
    rw [burnolRadiusZeroExtension_reflect]
    change burnolRadiusZeroExtension q (reflectRestricted q (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c):Hq))=
      burnolRadiusZeroExtension q (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c):Hq)
    rw [burnolRieszSingleFourierReturn_reflection_fixed]
  have evenC:reflectL2 ConstantDual.seed=ConstantDual.seed := by
    change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=burnolRadiusZeroExtension q (intervalConstant q)
    rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
  have evenLoss:reflectL2 (FullUnit.fullSource c h 1)=FullUnit.fullSource c h 1 := by
    change reflectL2 (fullWindowLoss h (sourceSB c))=_
    change reflectL2 (burnolMultiplicativeDilation (-h) (E (sourceSB c:Hq))-
      cutMap q (burnolMultiplicativeDilation (-h) (E (sourceSB c:Hq)))+outwardMean h (sourceSB c) • ConstantDual.seed)=_
    rw [map_add,map_sub,map_smul,cut_reflection,reflectL2_burnolMultiplicativeDilation,evenV,evenC]
    rfl
  unfold positionCoreSource gapDilationDifference
  rw [map_smul,map_add,map_add,map_sub,map_sub,map_smul,map_smul,
    reflectL2_burnolMultiplicativeDilation,reflectL2_burnolMultiplicativeDilation,evenE,evenLoss]

private theorem compressed_support (v:BurnolL2) (support:OriginalPaPhysicalGreen.originalPhysicalCutoff (1/2) v=v) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff q (burnolMultiplicativeDilation (Real.log 2) v)=
      burnolMultiplicativeDilation (Real.log 2) v := by
  apply cutoff_eq_self_of_ae_zero
  have actual:=OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn (1/2) v
  rw [support] at actual
  filter_upwards [burnolMultiplicativeDilation_coeFn (Real.log 2) v,
    (Measure.quasiMeasurePreserving_smul (μ := (volume:Measure ℝ)) (Real.exp_ne_zero (Real.log 2))).ae actual]
    with x dilation source
  intro outside
  simp only [smul_eq_mul] at source
  have no:Real.exp (Real.log 2)*x∉symmetricInterval (1/2) := by
    intro inside
    have le:=abs_le.mpr inside
    rw [abs_mul,abs_of_pos (Real.exp_pos _),Real.exp_log (by norm_num : (0:ℝ)<2)] at le
    exact outside (abs_le.mp (by linarith : |x|≤q))
  rw [dilation,burnolL2RawNormalizedDilation,source,indicator_of_notMem no,mul_zero]

theorem compressed_core_whole (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    E (compressedCoreSource c h:Hq)=burnolMultiplicativeDilation (Real.log 2) (positionCoreSource c h) := by
  let moved:=burnolMultiplicativeDilation (Real.log 2) (positionCoreSource c h)
  have support:=compressed_support _ (position_core_support c h nn bound)
  have mass : burnolQuarterMeanCoefficient (R moved)=0 := by
    rw [Constructor.mean_integral,←extension_mass]
    change 2*(∫x:ℝ,OriginalPaPhysicalGreen.originalPhysicalCutoff q moved x)=0
    rw [support,dilation_mass,position_core_mass c h nn bound,mul_zero,mul_zero]
  change E (Constructor.zeroMean (R moved):Hq)=moved
  rw [Constructor.zeroMean_read,mass,zero_smul,sub_zero]
  exact support

theorem compressed_core_expanded (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    burnolMultiplicativeDilation (-Real.log 2) (E (compressedCoreSource c h:Hq))=positionCoreSource c h := by
  rw [compressed_core_whole c h nn bound,burnolMultiplicativeDilation_add,neg_add_cancel,
    burnolMultiplicativeDilation_zero]

theorem compressed_core_even (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    reflectRestricted q (compressedCoreSource c h:Hq)=compressedCoreSource c h := by
  have parity:reflectL2 (E (compressedCoreSource c h:Hq))=E (compressedCoreSource c h:Hq) := by
    rw [compressed_core_whole c h nn bound,reflectL2_burnolMultiplicativeDilation,position_core_even]
  have read:=congrArg R parity
  change R (reflectL2 (burnolRadiusZeroExtension q (compressedCoreSource c h:Hq)))=_ at read
  rw [burnolRadiusZeroExtension_reflect] at read
  change R (E (reflectRestricted q (compressedCoreSource c h:Hq)))=R (E (compressedCoreSource c h:Hq)) at read
  rw [burnolQuarterRestriction_zeroExtension,burnolQuarterRestriction_zeroExtension] at read
  exact read

end OriginalKElementaryArithmeticAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
