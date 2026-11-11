import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.FourierContact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Contact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.OriginalPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCrossParameterRAdjointSource OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Completion OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Contact OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.FourierContact
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "F"=>fourierL2
local notation "Rq"=>burnolQuarterRestriction
local notation "Eq"=>burnolQuarterZeroExtension
local notation "b"=>burnolRieszSingleFourierSource
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "K"=>burnolCompletedMellinRieszVector

theorem actual_meanZero_fourier_contact (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h) (test:M):
    inner ℂ (F (Eq (test:Hq))) (wholeValue c zero h positive)=0:=by
  have unitary:=fourierL2.inner_map_map (F (Eq (test:Hq))) (wholeValue c zero h positive)
  rw [fourierL2_fourierL2] at unitary
  change inner ℂ (reflectL2 (burnolRadiusZeroExtension q (test:Hq)))
    (F (wholeValue c zero h positive))=_ at unitary
  rw [burnolRadiusZeroExtension_reflect] at unitary
  change inner ℂ (Eq (reflectRestricted q (test:Hq))) (F (wholeValue c zero h positive))=_ at unitary
  rw [←unitary,show Eq=burnolQuarterRestriction.adjoint from rfl,
    ContinuousLinearMap.adjoint_inner_left,actual_whole_fourier_quarter,inner_smul_right]
  have member:=reflectRestricted_quarter_preserves_meanZero test.property
  have mean:inner ℂ (intervalConstant q) (reflectRestricted q (test:Hq))=0:=
    (Submodule.mem_orthogonal _ _).mp member _ (Submodule.mem_span_singleton_self _)
  rw [inner_eq_zero_symm.mp mean,mul_zero]

theorem actual_original_K_arithmetic_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (K d:BurnolL2) (wholeValue c zero h positive)=
      inner ℂ (gapState d) (wholeValue c zero h positive)+
        ∑'n:ℕ,-(inverseClock c h)^(n+1)*scaledWindowRead c h ((n:ℝ)*h) (S (b d):Hq):=by
  rw [actual_original_K_price,←(actual_original_Sb_price c d zero h positive).tsum_eq]

theorem actual_original_FK_arithmetic_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (F (K d:BurnolL2)) (wholeValue c zero h positive)=
      inner ℂ (F (gapState d)) (wholeValue c zero h positive)-
        ∑'n:ℕ,-(inverseClock c h)^(n+1)*scaledWindowRead c h ((n:ℝ)*h) (b d:Hq):=by
  have even:reflectL2 (Eq (b d:Hq))=Eq (b d:Hq):=by
    change reflectL2 (burnolRadiusZeroExtension q (b d:Hq))=_
    rw [burnolRadiusZeroExtension_reflect,burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  have source:=congrArg (fun state:BurnolL2=>inner ℂ (F state) (wholeValue c zero h positive))
    (gapState_eq_kernel_add_correction d)
  rw [map_add,inner_add_left,sourceCorrection,map_sub,inner_sub_left,
    fourierL2_fourierL2,even,actual_meanZero_fourier_contact c zero h positive (S (b d)),sub_zero] at source
  rw [←(actual_compact_price c zero h positive (b d:Hq)).tsum_eq] at source
  linear_combination -source

/-- Both arithmetic banks are generated from the same absolute Whole source and the original b/Sb. -/
theorem actual_original_combo_arithmetic_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (sourceKernelCombo d) (wholeValue c zero h positive)=
      star (jQuarterAmplitude d)*inner ℂ (gapState d) (wholeValue c zero h positive)-
      star (hQuarterAmplitude d)*inner ℂ (F (gapState d)) (wholeValue c zero h positive)+
      star (jQuarterAmplitude d)*(∑'n:ℕ,-(inverseClock c h)^(n+1)*scaledWindowRead c h ((n:ℝ)*h) (S (b d):Hq))+
      star (hQuarterAmplitude d)*(∑'n:ℕ,-(inverseClock c h)^(n+1)*scaledWindowRead c h ((n:ℝ)*h) (b d:Hq)):=by
  rw [sourceKernelCombo_actual,inner_sub_left,inner_smul_left,inner_smul_left,
    starRingEnd_apply,starRingEnd_apply,actual_original_K_arithmetic_price,
    actual_original_FK_arithmetic_price]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.OriginalPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
