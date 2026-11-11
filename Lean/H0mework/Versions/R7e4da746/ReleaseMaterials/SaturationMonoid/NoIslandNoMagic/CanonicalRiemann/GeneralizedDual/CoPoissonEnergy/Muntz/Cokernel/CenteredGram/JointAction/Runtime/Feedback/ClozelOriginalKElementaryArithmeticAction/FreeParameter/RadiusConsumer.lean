import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer
open Complex Filter MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice OriginalKElementaryArithmeticAction.FreeParameter.Family OriginalKElementaryArithmeticAction.FreeParameter.FixedConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

def radiusTest (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation (-Real.log 16) (unitTest c h)

theorem actual_unit_radius_price (c : BurnolCompletedMellinCoordinate) (test : BurnolL2) :
    inner ℂ test (burnolUnitTailResponse c q)=
      (fullMellinTranslationCharacter c.value (Real.log 16))⁻¹*
      inner ℂ (burnolMultiplicativeDilation (-Real.log 16) test) (burnolUnitTailResponse c 4) := by
  have radius : (4:ℝ)*Real.exp (-Real.log 16)=q := by
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<16)]
    norm_num
  have source := burnolUnitTailResponse_radius_dilation c 4 (by norm_num) (by norm_num)
    (Real.log 16) (by rw [radius];norm_num)
  rw [radius] at source
  have read := congrArg (inner ℂ test) source
  rw [inner_smul_right] at read
  have moved := (burnolMultiplicativeDilation (Real.log 16)).inner_map_map
    (burnolMultiplicativeDilation (-Real.log 16) test) (burnolUnitTailResponse c 4)
  rw [burnolMultiplicativeDilation_add,add_neg_cancel,burnolMultiplicativeDilation_zero] at moved
  rw [moved] at read
  have scaled := congrArg (fun z : ℂ=>(fullMellinTranslationCharacter c.value (Real.log 16))⁻¹*z) read
  have phaseNe : fullMellinTranslationCharacter c.value (Real.log 16)≠0 := Complex.exp_ne_zero _
  rw [inv_mul_cancel_left₀ phaseNe] at scaled
  exact scaled.symm

theorem actual_native_unit_four_read (c d : BurnolCompletedMellinCoordinate) (h : ℝ) :
    nativeRead c h (star d.value)=
      ((1/2:ℂ)*(fullMellinTranslationCharacter (star d.value) (Real.log 16))⁻¹)*
        inner ℂ (radiusTest c h) (burnolUnitTailResponse (barC d) 4)-
      constantCoefficient (star d.value)*inner ℂ (movedTest c h) ConstantDual.value-
      inner ℂ (movedTest c h) (ReturnCounting.value d)+fourierContacts c h := by
  rw [actual_native_unit_read,actual_unit_radius_price]
  simp only [radiusTest,mul_assoc]
  rfl

def completeUnitNet (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (pairedMellinTranslationCharacter c.value h-pairedMellinTranslationCharacter (star c.value) h)*kernelSelfSource c+
    (1/2:ℂ)*(((1/2:ℂ)*(fullMellinTranslationCharacter (star c.value) (Real.log 16))⁻¹)*
      inner ℂ (radiusTest c h) (burnolUnitTailResponse (barC c) 4)-
      constantCoefficient (star c.value)*inner ℂ (movedTest c h) ConstantDual.value-
      inner ℂ (movedTest c h) (ReturnCounting.value c)+fourierContacts c h)

theorem actual_original_fixed_unit_net (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    BurnolPaBoundaryCancellationAt c zero↔completeUnitNet c (Real.log stageZeroSonineQ)=0 := by
  rw [actual_original_fixed_model]
  unfold completeModelNet completeUnitNet
  rw [actual_native_unit_four_read]

end OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
