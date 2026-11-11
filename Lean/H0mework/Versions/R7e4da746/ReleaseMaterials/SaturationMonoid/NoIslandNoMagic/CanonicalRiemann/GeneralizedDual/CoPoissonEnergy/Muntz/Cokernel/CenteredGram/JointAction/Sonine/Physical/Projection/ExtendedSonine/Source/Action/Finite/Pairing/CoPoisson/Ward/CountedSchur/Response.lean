import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Crossing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.OutsideQuarterAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKForcedInverseSourceCalculation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open Complex Filter MeasureTheory Set
open OriginalRieszSource OriginalRieszSourceGreen
open scoped Topology InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "h" => hPowerBColumn
local notation "w" => SingularCounting.centeredPower
local notation "C" => CenteredCountingDual.forward
local notation "D" => CenteredCountingDual.reverse
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "X" => burnolAmbientMeanZeroPosition
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

open private fourier_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
open private first_B_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private second_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.OutsideQuarterAction

/-- The old power source retains its original ordinary mean and centered logarithm. -/
def logSource (coordinate:BurnolCompletedMellinCoordinate) : M :=
  (-burnolQuarterMeanCoefficient (SingularCounting.powerL2 coordinate)) • SmallScaleLog.centeredLog

def powerSource (N:ℕ) (coordinate:BurnolCompletedMellinCoordinate) : M :=
  FiniteForcing.coefficient (star coordinate.value) N • w coordinate+logSource coordinate

/-- This rank source is the already generated forward commutator, independent of the positive cutoff. -/
def rankSource (state:M) : M := CountingJointEnergy.contact state

def resolvedFirst (N:ℕ) (coordinate:BurnolCompletedMellinCoordinate) : M :=
  BI (powerSource N coordinate+S (oppositeSource N (h coordinate))+rankSource (S (h coordinate)))

def resolvedSecond (N:ℕ) (coordinate:BurnolCompletedMellinCoordinate) : M :=
  -S (resolvedFirst N coordinate)-oppositeSource N (h coordinate)

theorem actual_power_source (N:ℕ) (positive:0<N) (coordinate:BurnolCompletedMellinCoordinate) :
    C N (w coordinate)=powerSource N coordinate := by
  have generated:=SingularCounting.projected_power_source coordinate N positive
  rw [SmallScaleLog.smallScaleResidual_eq_log] at generated
  exact generated

theorem original_zero_power_limit (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) :
    Tendsto (fun N=>C N (w coordinate)) atTop (𝓝 (logSource coordinate)) := by
  have actual:=SingularCounting.projected_power_limit coordinate zero
  rw [SmallScaleLog.smallScaleResidual_eq_log] at actual
  exact actual

private theorem h_even (coordinate:BurnolCompletedMellinCoordinate) :
    reflectRestricted q (h coordinate:Hq)=h coordinate :=
  congrArg (fun state:M=>(state:Hq)) (log_B_even coordinate 0)

private theorem forward_sub (N:ℕ) (left right:M) : C N (left-right)=C N left-C N right := by
  simp only [CenteredCountingDual.forward,WindowCounting.windowSource,Submodule.coe_sub,
    ←CountingDual.sourceCLM_apply,map_sub]

/-- The unknown counted h is solved from the explicit crossing source, not supplied on its right-hand side. -/
theorem resolvedFirst_actual (N:ℕ) (positive:0<N) (coordinate:BurnolCompletedMellinCoordinate) :
    resolvedFirst N coordinate=C N (h coordinate) := by
  have source:= (h_power_B_source coordinate).1
  change h coordinate+S (-S (h coordinate))=w coordinate at source
  simp only [map_neg,←sub_eq_add_neg] at source
  have counted:=congrArg (C N) source
  rw [forward_sub,actual_power_source N positive coordinate] at counted
  have oldRank:=CountingJointEnergy.commutator N positive (S (h coordinate))
    (fourier_even _ (h_even coordinate))
  have opposite:=oppositeSource_action N (h coordinate) (h_even coordinate)
  have schur:L (C N (h coordinate))=
      powerSource N coordinate+S (oppositeSource N (h coordinate))+rankSource (S (h coordinate)) := by
    change C N (h coordinate)-S (S (C N (h coordinate)))=_
    rw [opposite,map_sub]
    change _=powerSource N coordinate+(S (D N (S (h coordinate)))-S (S (C N (h coordinate))))+
      CountingJointEnergy.contact (S (h coordinate))
    linear_combination (norm:=module) counted+oldRank
  have result:=congrArg BI schur
  have inverseLeft:BI*L=1:=Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  change (BI*L) (C N (h coordinate))=resolvedFirst N coordinate at result
  rw [inverseLeft] at result
  exact result.symm

theorem resolvedSecond_actual (N:ℕ) (positive:0<N) (coordinate:BurnolCompletedMellinCoordinate) :
    resolvedSecond N coordinate=D N (hPowerBSecond coordinate) := by
  rw [resolvedSecond,resolvedFirst_actual N positive coordinate,
    oppositeSource_action N (h coordinate) (h_even coordinate)]
  change _=D N (-S (h coordinate))
  simp only [CenteredCountingDual.reverse,Submodule.coe_neg,map_neg,CountingDual.dual_eq_adjoint]
  module

/-- Both equations keep the crossing source, old rank source, and ordinary mean. -/
theorem resolved_blocks (N:ℕ) (coordinate:BurnolCompletedMellinCoordinate) :
    resolvedFirst N coordinate+S (resolvedSecond N coordinate)=
      powerSource N coordinate+rankSource (S (h coordinate)) ∧
    S (resolvedFirst N coordinate)+resolvedSecond N coordinate= -oppositeSource N (h coordinate) := by
  have inverseRead:=congrArg (fun op:M→L[ℂ]M=>op
    (powerSource N coordinate+S (oppositeSource N (h coordinate))+rankSource (S (h coordinate))))
    burnolMeanZeroBlockInverse_right
  change resolvedFirst N coordinate-S (S (resolvedFirst N coordinate))=
    powerSource N coordinate+S (oppositeSource N (h coordinate))+rankSource (S (h coordinate)) at inverseRead
  constructor
  · rw [resolvedSecond,map_sub,map_neg]
    linear_combination (norm:=module) inverseRead
  · rw [resolvedSecond]
    module

/-- The newly computed pair is consumed against both complete original B equations. -/
theorem actual_B2_read (N:ℕ) (coordinate:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    inner ℂ (resolvedFirst N coordinate) (Y value)+inner ℂ (resolvedSecond N coordinate) (X value)=
      star (FiniteForcing.coefficient (star coordinate.value) N)*inner ℂ (w coordinate) (d value)+
      inner ℂ (logSource coordinate+rankSource (S (h coordinate))) (d value)-
      inner ℂ (oppositeSource N (h coordinate)) (b value) := by
  have first:=burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs value)
  have second:=burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs value)
  change b value+S (d value)=X value at first
  change S (b value)+d value=Y value at second
  have bp:reflectRestricted q (b value:Hq)=b value:=congrArg (fun state:M=>(state:Hq)) (first_B_even value)
  have dp:reflectRestricted q (d value:Hq)=d value:=congrArg (fun state:M=>(state:Hq)) (second_even value)
  have sumRead:inner ℂ (resolvedFirst N coordinate) (Y value)+inner ℂ (resolvedSecond N coordinate) (X value)=
      inner ℂ (resolvedFirst N coordinate+S (resolvedSecond N coordinate)) (d value)+
      inner ℂ (S (resolvedFirst N coordinate)+resolvedSecond N coordinate) (b value) := by
    rw [←first,←second,inner_add_right,inner_add_right,inner_add_left,inner_add_left,
      meanZero_fourier_pairing_of_reflection _ _ dp,meanZero_fourier_pairing_of_reflection _ _ bp]
    ring
  have scaled : inner ℂ (FiniteForcing.coefficient (star coordinate.value) N • w coordinate) (d value)=
      star (FiniteForcing.coefficient (star coordinate.value) N)*inner ℂ (w coordinate) (d value) :=
    inner_smul_left (𝕜:=ℂ) (w coordinate) (d value) (FiniteForcing.coefficient (star coordinate.value) N)
  rw [sumRead,(resolved_blocks N coordinate).1,(resolved_blocks N coordinate).2,powerSource,
    inner_add_left,inner_add_left,scaled,inner_neg_left,inner_add_left]
  ring

/-- This is the original paired-D K/B₂ fixed cotest, with no new Pa or actor membership. -/
theorem fixed_price_source (N:ℕ) (c:BurnolCompletedMellinCoordinate) :
    inner ℂ (resolvedFirst N (barC c)) (Y (OriginalKPairedBEulerJunctionSource.sourceAction c))+
      inner ℂ (resolvedSecond N (barC c)) (X (OriginalKPairedBEulerJunctionSource.sourceAction c))=
      star (FiniteForcing.coefficient (star (barC c).value) N)*
        OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c+
      inner ℂ (logSource (barC c)+rankSource (S (h (barC c)))) (OriginalKPairedBEulerJunctionSource.sourceSecond c)-
      inner ℂ (oppositeSource N (h (barC c))) (OriginalKPairedBEulerJunctionSource.sourceFirst c) :=
  actual_B2_read N (barC c) (OriginalKPairedBEulerJunctionSource.sourceAction c)

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
