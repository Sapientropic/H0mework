import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.NativePrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.MixedBank

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.CompletePrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativeContact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Inverse
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.JointContact OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.NativePrice
open OriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.MixedBank
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "P0" => Constructor.zeroMean
local notation "μ" => burnolQuarterMeanCoefficient
local notation "C" => CenteredCountingDual.forward
local notation "b" => burnolRieszSingleFourierSource
local notation "ell" => CenteredCountingDual.logarithm

private theorem inverse_right (state:M):L (BI state)=state:=by
  change (L*BI) state=state
  rw [burnolMeanZeroBlockInverse_right]
  rfl

theorem actual_complete_contact_source (N:ℕ) (positive:0<N)
    (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    completeContact N c zero=L (C N (b c))-
      P0 (Rq (FiniteForcing.source N (regularSource c zero))):=by
  have generated:=congrArg L (actual_regular_inverse_count N positive c zero)
  change L (BI (P0 (Rq (FiniteForcing.source N (regularSource c zero)))))=
    L (C N (b c)-BI (completeContact N c zero)) at generated
  rw [map_sub,inverse_right,inverse_right] at generated
  rw [generated]
  module

private theorem counted_center_limit (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun N:ℕ=>C N (b c)) atTop
      (𝓝 (P0 (Rq (AmbientCounting.value c)))):=by
  have restricted:=burnolQuarterRestriction.continuous.continuousAt.tendsto.comp
    (AmbientCounting.original_ambient_limit c)
  exact Constructor.zeroMean.continuous.continuousAt.tendsto.comp restricted

/-- The full Ward contact is computed from the original K alias bank, with the actual Fourier mean. -/
theorem actual_complete_contact_limit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>completeContact N c zero) atTop
      (𝓝 (-S (S (P0 (Rq (AmbientCounting.value c))))-
        mixedBank c-fourierMean c • ell)):=by
  have first:=burnolMeanZeroOneMinusSquare.continuous.continuousAt.tendsto.comp
    (counted_center_limit c)
  have second:=Constructor.zeroMean.continuous.continuousAt.tendsto.comp
    (actual_regular_counting_limit c zero)
  have normalized:P0 (forwardQuarter c zero-
      OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment.regularReciprocalMean c • intervalConstant q)=
      P0 (forwardQuarter c zero):=by
    rw [map_sub,map_smul,Constructor.zeroMean_constant,smul_zero,sub_zero]
  rw [normalized] at second
  have native:=first.sub second
  have exchange:=actual_complete_counting_exchange c zero
  have source:P0 (forwardQuarter c zero)=P0 (Rq (AmbientCounting.value c))+
      mixedBank c+fourierMean c • ell:=by
    calc
      _=(mixedBank c+fourierMean c • ell)+P0 (Rq (AmbientCounting.value c)):=
        sub_eq_iff_eq_add.mp exchange
      _=_:=by module
  rw [source] at native
  have simplified:L (P0 (Rq (AmbientCounting.value c)))-
      (P0 (Rq (AmbientCounting.value c))+mixedBank c+fourierMean c • ell)=
      -S (S (P0 (Rq (AmbientCounting.value c))))-mixedBank c-fourierMean c • ell:=by
    change (P0 (Rq (AmbientCounting.value c))-S (S (P0 (Rq (AmbientCounting.value c)))))-_=_
    module
  rw [simplified] at native
  apply native.congr'
  filter_upwards [eventually_ge_atTop 1] with N bound
  exact (actual_complete_contact_source N (by omega) c zero).symm

/-- This is the opposite exterior price on the actual regular source, not a presumed S-preimage. -/
theorem actual_native_opposite_contact_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>inner ℂ (oppositeContact N (b d)) (P0 (regularQuarter c zero))) atTop
      (𝓝 (inner ℂ (S (b d):Hq) (Rq (AmbientCounting.value c))+
        inner ℂ (S (b d):Hq) (mixedBank c:Hq)+
        fourierMean c*inner ℂ (S (b d):Hq) (ell:Hq)-
        inner ℂ (S (P0 (Rq (AmbientCounting.value d)))) (P0 (regularQuarter c zero))-
        μ (regularQuarter c zero)*inner ℂ (Constructor.returnState d:Hq) SmallScaleLog.logL2)):=by
  have native:=actual_return_ward_price_limit c d zero
  rw [actual_Sb_mixed_price c d zero] at native
  have first:=(burnolMeanZeroTruncatedFourier.continuous.continuousAt.tendsto.comp
    (counted_center_limit d)).inner (𝕜:=ℂ)
      (tendsto_const_nhds (x:=P0 (regularQuarter c zero)))
  have price:=(native.sub first).sub (tendsto_const_nhds
    (x:=μ (regularQuarter c zero)*inner ℂ (Constructor.returnState d:Hq) SmallScaleLog.logL2))
  apply price.congr'
  filter_upwards with N
  dsimp only [Function.comp_apply]
  unfold returnWardPrice
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.CompletePrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
