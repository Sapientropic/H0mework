import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterCurrentSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.QuarterCurrentEffect
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open UnitPowerJordanSource UnitPowerJordanAction QuarterCurrentSource
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Eq" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Pi" => burnolEvenAmbientProjection
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

open private source_evenPart
  from H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource

private theorem source_first_even (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    sourceMeanZeroReflection (burnolAmbientMeanZeroFirstCorrection (sourceField c j))=
      burnolAmbientMeanZeroFirstCorrection (sourceField c j) := by
  apply Subtype.ext
  change reflectRestricted q (burnolAmbientMeanZeroFirstCorrection (sourceField c j):Hq)=_
  have even (k : Nat) : reflectRestricted q (logBFirst c k:Hq)=(logBFirst c k:Hq) :=
    congrArg (fun v:M=>(v:Hq)) (log_B_even c k)
  rw [source_B_first]
  simp only [Submodule.coe_sum,SetLike.val_smul,map_sum,map_smul,even]

private theorem extension_even (value : M) (even : sourceMeanZeroReflection value=value) :
    reflectL2 (Eq (value:Hq))=Eq (value:Hq) := by
  change reflectL2 (burnolRadiusZeroExtension q (value:Hq))=_
  rw [burnolRadiusZeroExtension_reflect]
  exact congrArg (burnolRadiusZeroExtension q) (congrArg (fun v:M=>(v:Hq)) even)

/-- The paid Fourier block of this same source action fixes its entire second B leg. -/
theorem actual_sourceStep_second_B (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    burnolAmbientMeanZeroSecondCorrection (sourceStep c (sourceField c j))=
      -S (currentBNext c (sourceField c j)) := by
  have fourier : burnolAmbientMeanZeroFourier (sourceStep c (sourceField c j))=0 := by
    change OriginalKDirectRCofinalOutsideVolterraSource.quarterCotest
      (fourierL2 (burnolAmbientEvenPart (sourceField c (j+1))))=0
    rw [source_evenPart]
    exact source_fourier_quarter_zero c (j+1)
  have block := burnolMeanZeroBlock_second_equation
    (burnolAmbientMeanZeroBlockRhs (sourceStep c (sourceField c j)))
  change S (burnolAmbientMeanZeroFirstCorrection (sourceStep c (sourceField c j)))+
    burnolAmbientMeanZeroSecondCorrection (sourceStep c (sourceField c j))=
      burnolAmbientMeanZeroFourier (sourceStep c (sourceField c j)) at block
  rw [fourier,actual_sourceStep_B_current] at block
  linear_combination (norm:=module) block

/-- The original complete B correction retains both actual feet of this same current source action. -/
theorem actual_sourceStep_correction (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    burnolAmbientEvenMeanZeroCorrection (sourceStep c (sourceField c j))=
      Eq (currentBNext c (sourceField c j):Hq)-
        fourierL2 (Eq (S (currentBNext c (sourceField c j)):Hq)) := by
  have firstEven : sourceMeanZeroReflection (currentBNext c (sourceField c j))=
      currentBNext c (sourceField c j) := by
    rw [←actual_sourceStep_B_current]
    exact source_first_even c (j+1)
  have secondEven : sourceMeanZeroReflection (S (currentBNext c (sourceField c j)))=
      S (currentBNext c (sourceField c j)) := by
    have actual := sourceMeanZeroFourier_reflect (currentBNext c (sourceField c j))
    rw [firstEven] at actual
    exact actual.symm
  have rawEven : reflectL2
      (Eq (currentBNext c (sourceField c j):Hq)-fourierL2 (Eq (S (currentBNext c (sourceField c j)):Hq)))=
      Eq (currentBNext c (sourceField c j):Hq)-fourierL2 (Eq (S (currentBNext c (sourceField c j)):Hq)) := by
    rw [map_sub,extension_even _ firstEven,←fourierL2_reflectL2_commute,extension_even _ secondEven]
  unfold burnolAmbientEvenMeanZeroCorrection burnolAmbientRawMeanZeroCorrection
  rw [actual_sourceStep_B_current,actual_sourceStep_second_B]
  change burnolAmbientEvenPart
    (Eq (currentBNext c (sourceField c j):Hq)+fourierL2 (Eq (-(S (currentBNext c (sourceField c j)):Hq))))=_
  rw [map_neg,map_neg]
  rw [←sub_eq_add_neg]
  unfold burnolAmbientEvenPart
  rw [rawEven]
  module

/-- The original physical projection closure consumes that complete same-action B correction. -/
theorem actual_sourceStep_physical (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    (Pi (sourceStep c (sourceField c j)):BurnolL2)=sourceStep c (sourceField c j)-
      (Eq (currentBNext c (sourceField c j):Hq)-
        fourierL2 (Eq (S (currentBNext c (sourceField c j)):Hq))) := by
  have projected := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula (sourceStep c (sourceField c j))
  change (Pi (sourceStep c (sourceField c j)):BurnolL2)=
    burnolAmbientEvenPart (sourceStep c (sourceField c j))-
      burnolAmbientEvenMeanZeroCorrection (sourceStep c (sourceField c j)) at projected
  have actualEven : burnolAmbientEvenPart (sourceStep c (sourceField c j))=
      sourceStep c (sourceField c j) := source_evenPart c (j+1)
  rw [actualEven,actual_sourceStep_correction] at projected
  exact projected

/-- The original orthogonal outside projection retains the same complete vector, not one scalar price. -/
theorem actual_sourceStep_outside (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    outside (sourceStep c (sourceField c j))=
      Eq (currentBNext c (sourceField c j):Hq)-
        fourierL2 (Eq (S (currentBNext c (sourceField c j)):Hq)) := by
  have whole := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal
    (sourceStep c (sourceField c j))
  change (Pi (sourceStep c (sourceField c j)):BurnolL2)+outside (sourceStep c (sourceField c j))=
    sourceStep c (sourceField c j) at whole
  rw [actual_sourceStep_physical] at whole
  linear_combination (norm:=module) whole

end OriginalKFiniteOrderRelease.QuarterCurrentEffect
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
