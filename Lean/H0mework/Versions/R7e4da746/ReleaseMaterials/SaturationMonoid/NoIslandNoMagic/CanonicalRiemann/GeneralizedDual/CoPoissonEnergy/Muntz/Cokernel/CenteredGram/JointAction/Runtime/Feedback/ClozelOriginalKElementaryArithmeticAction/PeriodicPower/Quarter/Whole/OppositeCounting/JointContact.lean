import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Inverse
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.JointContact
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Inverse
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local notation "P0" => Constructor.zeroMean
local notation "μ" => burnolQuarterMeanCoefficient
local notation "C" => CenteredCountingDual.forward
local notation "k" => CenteredCountingDual.constantFourier
local notation "ell" => CenteredCountingDual.logarithm

private theorem mean_continuous:Continuous (μ:Hq→ℂ):=by
  unfold burnolQuarterMeanCoefficient
  exact (innerSL ℂ (intervalConstant q)).continuous.div_const _

def completeContact (N:ℕ) (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):M :=
  CountingJointEnergy.contact (Constructor.returnState c)+
    S (oppositeContact N (burnolRieszSingleFourierSource c))+
    ForcingPrimitive.leadingCoefficient c • C N (SingularCounting.centeredPower c)-
    C N (P0 (aliasQuarter c))+jumpCoefficient c • C N k-
    μ (Rq (regularSource c zero)) • ell

theorem actual_complete_inverse_limit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>C N (burnolRieszSingleFourierSource c)-BI (completeContact N c zero))
      atTop (𝓝 (sourceInverse c zero)):=by
  have centered:=Constructor.zeroMean.continuous.continuousAt.tendsto.comp
    (actual_regular_counting_limit c zero)
  have normalized:P0 (forwardQuarter c zero-regularReciprocalMean c • intervalConstant q)=
      P0 (forwardQuarter c zero):=by
    rw [map_sub,map_smul,Constructor.zeroMean_constant,smul_zero,sub_zero]
  rw [normalized] at centered
  have inverse:=burnolMeanZeroBlockInverse.continuous.continuousAt.tendsto.comp centered
  change Tendsto (fun N:ℕ=>BI (P0 (Rq (FiniteForcing.source N (regularSource c zero)))))
    atTop (𝓝 (sourceInverse c zero)) at inverse
  apply inverse.congr'
  filter_upwards [eventually_ge_atTop 1] with N bound
  exact actual_regular_inverse_count N (by omega) c zero

/-- A full arithmetic contact price, evaluated on an arbitrary actual inverse cotest. -/
theorem actual_complete_contact_price_limit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (test:M):
    Tendsto (fun N:ℕ=>inner ℂ test (C N (burnolRieszSingleFourierSource c))-
      inner ℂ test (BI (completeContact N c zero))) atTop
      (𝓝 (inner ℂ test (sourceInverse c zero))):=by
  have price:=((innerSL ℂ test).continuous.continuousAt.tendsto.comp
    (actual_complete_inverse_limit c zero))
  change Tendsto (fun N:ℕ=>inner ℂ test
    (C N (burnolRieszSingleFourierSource c)-BI (completeContact N c zero)))
    atTop (𝓝 (inner ℂ test (sourceInverse c zero))) at price
  simpa only [inner_sub_right] using price

theorem actual_position_unit_contact_limit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>μ (burnolTruncatedFourier
      (S (C N (burnolRieszSingleFourierSource c)-BI (completeContact N c zero)):Hq)))
      atTop (𝓝 (μ (burnolTruncatedFourier (S (sourceInverse c zero):Hq)))):=by
  have a:=burnolMeanZeroTruncatedFourier.continuous.continuousAt.tendsto.comp
    (actual_complete_inverse_limit c zero)
  have b:=burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.continuous.continuousAt.tendsto.comp a
  have f:=burnolTruncatedFourier.continuous.continuousAt.tendsto.comp b
  exact mean_continuous.continuousAt.tendsto.comp f

theorem actual_fourier_unit_contact_limit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>μ (burnolTruncatedFourier
      (C N (burnolRieszSingleFourierSource c)-BI (completeContact N c zero):Hq)))
      atTop (𝓝 (μ (burnolTruncatedFourier (sourceInverse c zero:Hq)))):=by
  have a:=burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.continuous.continuousAt.tendsto.comp
    (actual_complete_inverse_limit c zero)
  have f:=burnolTruncatedFourier.continuous.continuousAt.tendsto.comp a
  exact mean_continuous.continuousAt.tendsto.comp f

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.JointContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
