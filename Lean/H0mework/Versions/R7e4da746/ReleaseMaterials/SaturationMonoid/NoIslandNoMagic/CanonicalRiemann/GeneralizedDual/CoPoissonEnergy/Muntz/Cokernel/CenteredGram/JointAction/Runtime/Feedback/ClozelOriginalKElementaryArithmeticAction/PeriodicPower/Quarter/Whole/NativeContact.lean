import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativeContact
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "Rq"=>burnolQuarterRestriction
local notation "Eq"=>burnolQuarterZeroExtension
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "b"=>burnolRieszSingleFourierSource
local notation "K"=>burnolCompletedMellinRieszVector
local notation "F"=>fourierL2

/-- The same finite original forward/reverse programme computes the complete B contact. -/
theorem actual_B_contact (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    inner ℂ (b d:Hq) (forwardQuarter c zero)=
      inner ℂ (CountingDual.value d) (regularSource c zero):=by
  have finite (N:ℕ):inner ℂ (Rq (FiniteForcing.source N (regularSource c zero))) (b d:Hq)=
      inner ℂ (regularSource c zero) (DualSource.source N (Eq (b d:Hq))):=by
    rw [←CountingDual.source_pairing]
    exact (ContinuousLinearMap.adjoint_inner_right Rq _ _).symm
  have left:=(actual_regular_counting_limit c zero).inner (𝕜:=ℂ)
    (tendsto_const_nhds (x:=(b d:Hq)))
  have right:=(tendsto_const_nhds (x:=regularSource c zero)).inner (𝕜:=ℂ)
    (CountingDual.original_dual_tendsto d)
  have equality:=tendsto_nhds_unique (left.congr' (Eventually.of_forall finite)) right
  have mean:inner ℂ (intervalConstant q) (b d:Hq)=0:=
    (Submodule.mem_orthogonal _ _).mp (b d).property _ (Submodule.mem_span_singleton_self _)
  rw [inner_sub_left,inner_smul_left,mean,mul_zero,sub_zero] at equality
  simpa only [star_def,inner_conj_symm] using congrArg star equality

/-- The independent returned cotest keeps the same finite programme and the same Unit. -/
theorem actual_Sb_contact (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    inner ℂ (S (b d):Hq) (forwardQuarter c zero)=
      inner ℂ (ReturnCounting.value d) (regularSource c zero):=by
  have finite (N:ℕ):inner ℂ (Rq (FiniteForcing.source N (regularSource c zero)))
      (S (b d):Hq)=inner ℂ (regularSource c zero) (ReturnCounting.finite d N):=by
    rw [ReturnCounting.finite,←CountingDual.source_pairing]
    exact (ContinuousLinearMap.adjoint_inner_right Rq _ _).symm
  have left:=(actual_regular_counting_limit c zero).inner (𝕜:=ℂ)
    (tendsto_const_nhds (x:=(S (b d):Hq)))
  have right:=(tendsto_const_nhds (x:=regularSource c zero)).inner (𝕜:=ℂ)
    (ReturnCounting.finite_tendsto d)
  have equality:=tendsto_nhds_unique (left.congr' (Eventually.of_forall finite)) right
  have mean:inner ℂ (intervalConstant q) (S (b d):Hq)=0:=
    (Submodule.mem_orthogonal _ _).mp (S (b d)).property _ (Submodule.mem_span_singleton_self _)
  rw [inner_sub_left,inner_smul_left,mean,mul_zero,sub_zero] at equality
  simpa only [star_def,inner_conj_symm] using congrArg star equality

theorem actual_original_K_native_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (K d:BurnolL2) (wholeValue c zero h positive)=
      inner ℂ (gapState d) (wholeValue c zero h positive)+
        inner ℂ (ReturnCounting.value d) (regularSource c zero):=by
  rw [actual_original_forward_price,actual_Sb_contact]

theorem actual_original_FK_native_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (F (K d:BurnolL2)) (wholeValue c zero h positive)=
      inner ℂ (F (gapState d)) (wholeValue c zero h positive)-
        inner ℂ (CountingDual.value d) (regularSource c zero):=by
  rw [actual_original_fourier_source_price,actual_B_contact]

/-- Both complete native counted slots enter the original whole-kernel price together. -/
theorem actual_original_combo_native_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (sourceKernelCombo d) (wholeValue c zero h positive)=
      star (jQuarterAmplitude d)*inner ℂ (gapState d) (wholeValue c zero h positive)-
      star (hQuarterAmplitude d)*inner ℂ (F (gapState d)) (wholeValue c zero h positive)+
      star (jQuarterAmplitude d)*inner ℂ (ReturnCounting.value d) (regularSource c zero)+
      star (hQuarterAmplitude d)*inner ℂ (CountingDual.value d) (regularSource c zero):=by
  rw [actual_original_combo_source_price,actual_Sb_contact,actual_B_contact]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativeContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
