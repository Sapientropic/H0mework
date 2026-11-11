import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Inverse
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PowerHead
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionHead
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Source
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "P0" => Constructor.zeroMean
local notation "BI" => burnolMeanZeroBlockInverse
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "μ" => burnolQuarterMeanCoefficient
local notation "C" => CenteredCountingDual.forward
local notation "ell" => CenteredCountingDual.logarithm
local notation "k" => CenteredCountingDual.constantFourier
private abbrev eta (c:BurnolCompletedMellinCoordinate):M :=
  burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula c)

private def countCLM (N:ℕ):M→L[ℂ]M :=
  Constructor.zeroMean.comp (burnolQuarterRestriction.comp ((CountingDual.sourceCLM N).comp
    (burnolQuarterZeroExtension.comp burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL)))

private theorem count_apply (N:ℕ) (state:M):countCLM N state=C N state:=rfl

private theorem inverse_left (state:M):BI (L state)=state:=by
  change (BI*L) state=state
  rw [show BI*L=1 from Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit]
  rfl

theorem actual_original_inverse_exchange (N:ℕ) (positive:0<N)
    (c:BurnolCompletedMellinCoordinate):
    BI (C N (eta c))=C N (burnolRieszSingleFourierSource c)-
      BI (CountingJointEnergy.contact (Constructor.returnState c)+
        S (oppositeContact N (burnolRieszSingleFourierSource c))):=by
  have generated:=congrArg BI (actual_original_joint_forcing N positive c)
  rw [inverse_left,CountingJointEnergy.forcing,map_add] at generated
  rw [generated,map_add,map_add]
  module

/-- The counted regular source includes the actual alias and box, before any inverse. -/
theorem actual_regular_centered_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    P0 (Rq (regularSource c zero))=eta c-
      ForcingPrimitive.leadingCoefficient c • SingularCounting.centeredPower c+
      P0 (aliasQuarter c)-jumpCoefficient c • k:=by
  have split:=congrArg Rq (actual_source_split c zero)
  simp only [quarterWave,powerSource,map_add,map_smul,burnolQuarterRestriction_zeroExtension] at split
  have quarter:Rq (regularSource c zero)=periodicQuarter c-
      ForcingPrimitive.leadingCoefficient c • SingularCounting.powerL2 c:=by
    rw [split]
    module
  have original:=congrArg L (actual_original_B_periodic_source c)
  change L (burnolRieszSingleFourierSource c)=(L*BI) (P0 (completeQuarterForcing c)) at original
  rw [burnolMeanZeroBlockInverse_right,burnolRieszSingleFourierSource_equation] at original
  have input:eta c=P0 (completeQuarterForcing c):=original
  rw [quarter,input,completeQuarterForcing,map_sub,map_smul,map_add,map_sub,map_smul]
  change P0 (periodicQuarter c)-ForcingPrimitive.leadingCoefficient c • SingularCounting.centeredPower c=
    P0 (periodicQuarter c)-P0 (aliasQuarter c)+jumpCoefficient c • k-
      ForcingPrimitive.leadingCoefficient c • SingularCounting.centeredPower c+
      P0 (aliasQuarter c)-jumpCoefficient c • k
  module

private theorem regular_support (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    E (Rq (regularSource c zero))=regularSource c zero:=by
  have split:=actual_source_split c zero
  have value:regularSource c zero=quarterWave c-
      ForcingPrimitive.leadingCoefficient c • powerSource c:=by
    rw [split]
    module
  rw [value,quarterWave,powerSource,map_sub,map_smul,burnolQuarterRestriction_zeroExtension,
    burnolQuarterRestriction_zeroExtension,map_sub,map_smul]

private theorem counted_centering (N:ℕ) (positive:0<N) (state:Hq):
    P0 (WindowCounting.windowSource N state)=C N (P0 state)+μ state • ell:=by
  have projected:(P0 state:Hq)=state-μ state • intervalConstant q:=Constructor.zeroMean_read state
  have exactCount:C N (P0 state)=P0 (WindowCounting.windowSource N state)-μ state • ell:=by
    change P0 (Rq (CountingDual.sourceCLM N (E (P0 state:Hq))))=_
    rw [projected,map_sub,map_smul,map_sub,map_smul,map_sub,map_smul,map_sub,map_smul]
    change P0 (WindowCounting.windowSource N state)-
      μ state • P0 (WindowCounting.windowSource N (intervalConstant q))=_
    rw [CenteredCountingDual.constant_source N positive]
  rw [exactCount]
  module

/-- Same-N full source, both mean contacts, and both exterior actions enter the original BI together. -/
theorem actual_regular_inverse_count (N:ℕ) (positive:0<N)
    (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    BI (P0 (Rq (FiniteForcing.source N (regularSource c zero))))=
      C N (burnolRieszSingleFourierSource c)-BI (
        CountingJointEnergy.contact (Constructor.returnState c)+
        S (oppositeContact N (burnolRieszSingleFourierSource c))+
        ForcingPrimitive.leadingCoefficient c • C N (SingularCounting.centeredPower c)-
        C N (P0 (aliasQuarter c))+jumpCoefficient c • C N k-
        μ (Rq (regularSource c zero)) • ell):=by
  have feed:=congrArg (countCLM N) (actual_regular_centered_source c zero)
  rw [map_sub,map_add,map_sub,map_smul,map_smul] at feed
  simp only [count_apply] at feed
  have counted:=counted_centering N positive (Rq (regularSource c zero))
  change P0 (Rq (FiniteForcing.source N (E (Rq (regularSource c zero)))))=_ at counted
  rw [regular_support,feed] at counted
  rw [counted,map_add,map_sub,map_add,map_sub,map_smul,map_smul,
    actual_original_inverse_exchange N positive c]
  simp only [map_add,map_sub,map_smul]
  module

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Inverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
