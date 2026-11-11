import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.BForwardGapProjectionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockEuler

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalUpperWaveRGapSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteColumns
open OriginalCommonInverseForcing.SourceJoint
open OriginalKPairedBEulerJunctionSource OriginalKPairedBEulerJunctionSource.BandFullStockAction
open OriginalKFiniteOrderRelease OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKFiniteOrderRelease.UnitPowerJordanAction OriginalKFiniteOrderRelease.QuarterSourceCommutator
open OriginalKFiniteOrderRelease.GenericSourceStepBAction
open scoped InnerProductSpace Topology

local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "F" => fourierL2
local notation "R" => burnolDirectRightResolventCLM
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "BI" => burnolMeanZeroBlockInverse
local notation "mu" => burnolQuarterMeanCoefficient
local notation "Rq" => burnolQuarterRestriction
local notation "h0" => junctionShift
local notation "u" => upperSeedFactor h0

open private physical_fibres
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.BForwardGapProjectionSource
open private firstMap secondMap
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockAction
open private source_action_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockEuler

private theorem h_nonnegative : 0≤h0 := junctionShift_pos.le
private theorem h_bounded : h0≤Real.log 2 := (le_abs_self _).trans fixedShift_small

private theorem R_paired (coordinate:BurnolCompletedMellinCoordinate) (shift:ℝ) (value:BurnolL2) :
    R coordinate (pairedBurnolMultiplicativeDilation shift value)=
      pairedBurnolMultiplicativeDilation shift (R coordinate value) := by
  change R coordinate ((1/2:ℂ) •
    (burnolMultiplicativeDilation shift value+burnolMultiplicativeDilation (-shift) value))=
    (1/2:ℂ) • (burnolMultiplicativeDilation shift (R coordinate value)+
      burnolMultiplicativeDilation (-shift) (R coordinate value))
  rw [map_smul,map_add]
  change (1/2:ℂ) •
    (burnolDirectRightResolvent (coordinate.value/2) (burnolMultiplicativeDilation shift value)+
      burnolDirectRightResolvent (coordinate.value/2) (burnolMultiplicativeDilation (-shift) value))=_
  rw [burnolDirectRightResolvent_dilation,burnolDirectRightResolvent_dilation]
  rfl

/-- The same full-stock word is acted on before either B projection. -/
theorem whole_debt_R_source (coordinate:BurnolCompletedMellinCoordinate) :
    R coordinate (wholeDebt coordinate)=
      R coordinate (upperSourceWave coordinate h0)-
        (2*u) • pairedBurnolMultiplicativeDilation h0 (R coordinate (K coordinate:BurnolL2))+
        (2*u*pairedMellinTranslationCharacter (star coordinate.value) h0) •
          R coordinate (K coordinate:BurnolL2) := by
  rw [whole_debt_raw_source,map_add,map_sub,map_smul,map_smul]
  rw [show R coordinate (sourceAction coordinate)=
      pairedBurnolMultiplicativeDilation h0 (R coordinate (K coordinate:BurnolL2)) from
    R_paired coordinate h0 (K coordinate:BurnolL2)]

private theorem debt_even (coordinate:BurnolCompletedMellinCoordinate) :
    reflectL2 (wholeDebt coordinate)=wholeDebt coordinate := by
  have waveEven:=mem_evenL2ClosedFace_iff.mp
    (upperSourceWaveAmbient coordinate h0 h_nonnegative h_bounded).property.2
  change reflectL2 (upperSourceWave coordinate h0)=upperSourceWave coordinate h0 at waveEven
  have kernelEven:=mem_evenL2ClosedFace_iff.mp (K coordinate).property.2
  rw [whole_debt_raw_source]
  simp only [map_add,map_sub,map_smul,waveEven,source_action_even,kernelEven]

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

/-- Exact original order acts on the already generated whole Pa source. -/
theorem original_upper_R_physical (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    R c (upperSourceWave c h)∈evenBurnolClosedFace q := by
  have actual:=CombSource.Division.whole_pa_physical observation nontrivial half.down 1
    (generatedRiemannXiZeroOrder_pos observation nontrivial)
    (upperSourceWaveAmbient c h nn bound) (actual_upper_ambient_inPa c h nn bound)
  change R c (upperSourceWave c h)∈evenBurnolClosedFace q at actual
  exact actual

/-- All next B faces are dependent reads of this same qualified whole-source action. -/
theorem original_upper_projection (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    gapSecondNext c (upperSourceWave c h)=0 ∧
      firstNext (barC c) (F (upperSourceWave c h))=0 ∧
      secondNext (barC c) (F (upperSourceWave c h))=0 := by
  have qualified:upperSourceWave c h∈evenBurnolClosedFace q :=
    (upperSourceWaveAmbient c h nn bound).property
  have even:=mem_evenL2ClosedFace_iff.mp qualified.2
  have physical:=physical_fibres
    ⟨R c (upperSourceWave c h),original_upper_R_physical observation nontrivial half h nn bound⟩
  have gap:=actual_forward_R_gap_B c (upperSourceWave c h) even qualified.1.1
  have full:=actual_forward_R_B c (upperSourceWave c h) even
  exact ⟨gap.2.symm.trans physical.2,full.2.symm.trans physical.2,full.1.symm.trans physical.1⟩

/-- Mean, exterior tail, Fourier drive and all six contacts remain in the generated equation. -/
theorem original_upper_full_source_equation (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    centeredQuarterStep (barC c) (b (F (upperSourceWave c h)))+
      (-2*(sourceTail (barC c) (F (upperSourceWave c h))+
        mu (Rq (F (upperSourceWave c h)))*(q:ℂ)^(1-star (barC c).value)/(1-star (barC c).value))) •
          logBFirst (barC c) 0-
      BI (∑ i:Fin 6,contactCoefficients (barC c) (b (F (upperSourceWave c h)):Hq) i •
        contactColumns (barC c) i)+
      BI (backwardContact (barC c) (Y (F (upperSourceWave c h))))=0 := by
  simpa only [firstNext,currentAmplitude,contactAction] using
    (original_upper_projection observation nontrivial half h nn bound).2.1

/-- Only the whole Pa source is removed; the original RK word, phase and units are retained. -/
theorem original_whole_debt_R_fibres :
    b (R c (wholeDebt c))=(-2*u) •
      b (pairedBurnolMultiplicativeDilation h0 (R c (K c:BurnolL2))-
        pairedMellinTranslationCharacter (star (c).value) h0 • R c (K c:BurnolL2)) ∧
    d (R c (wholeDebt c))=(-2*u) •
      d (pairedBurnolMultiplicativeDilation h0 (R c (K c:BurnolL2))-
        pairedMellinTranslationCharacter (star (c).value) h0 • R c (K c:BurnolL2)) := by
  have paid:=physical_fibres
    ⟨R c (upperSourceWave c h0),
      original_upper_R_physical observation nontrivial half h0 h_nonnegative h_bounded⟩
  change firstMap (R c (upperSourceWave c h0))=0 ∧
    secondMap (R c (upperSourceWave c h0))=0 at paid
  constructor
  · change firstMap (R c (wholeDebt c))=(-2*u) •
      firstMap (pairedBurnolMultiplicativeDilation h0 (R c (K c:BurnolL2))-
        pairedMellinTranslationCharacter (star (c).value) h0 • R c (K c:BurnolL2))
    rw [whole_debt_R_source,map_add,map_sub,map_smul,map_smul,map_sub,map_smul,paid.1]
    module
  · change secondMap (R c (wholeDebt c))=(-2*u) •
      secondMap (pairedBurnolMultiplicativeDilation h0 (R c (K c:BurnolL2))-
        pairedMellinTranslationCharacter (star (c).value) h0 • R c (K c:BurnolL2))
    rw [whole_debt_R_source,map_add,map_sub,map_smul,map_smul,map_sub,map_smul,paid.2]
    module

/-- The existing complete Step programmes consume the same full-stock R constraint. -/
theorem original_whole_debt_R_programmes :
    firstNext (barC c) (F (wholeDebt c))=(-2*u) •
      d (pairedBurnolMultiplicativeDilation h0 (R c (K c:BurnolL2))-
        pairedMellinTranslationCharacter (star (c).value) h0 • R c (K c:BurnolL2)) ∧
    secondNext (barC c) (F (wholeDebt c))=(-2*u) •
      b (pairedBurnolMultiplicativeDilation h0 (R c (K c:BurnolL2))-
        pairedMellinTranslationCharacter (star (c).value) h0 • R c (K c:BurnolL2)) := by
  have generated:=actual_forward_R_B c (wholeDebt c) (debt_even c)
  have fields:=original_whole_debt_R_fibres observation nontrivial half
  exact ⟨generated.2.symm.trans fields.2,generated.1.symm.trans fields.1⟩

end OriginalUpperWaveRGapSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

