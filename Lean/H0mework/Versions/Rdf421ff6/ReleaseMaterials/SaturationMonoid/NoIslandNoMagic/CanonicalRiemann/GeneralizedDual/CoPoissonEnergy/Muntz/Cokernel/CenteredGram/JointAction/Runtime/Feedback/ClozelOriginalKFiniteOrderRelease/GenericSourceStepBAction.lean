import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.GenericSourceStepBAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open UnitPowerJordanSource UnitPowerJordanAction QuarterSourceCommutator
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "D" => burnolTruncatedFourier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local notation "P" => Constructor.zeroMean
local notation "mu" => burnolQuarterMeanCoefficient
local notation "Cq" => intervalConstant q
local notation "X" => burnolAmbientMeanZeroPosition
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

open private inward_restriction source_fourier fourier_source centered_fourier_read
  from H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private centered_constant_step inverse_even fourier_even
  from H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction

private theorem evenPart_of_even (value : BurnolL2) (even : reflectL2 value=value) :
    burnolAmbientEvenPart value=value := by
  unfold burnolAmbientEvenPart
  rw [even]
  module

private theorem source_even (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) : reflectL2 (sourceStep c value)=sourceStep c value := by
  change reflectL2 (OriginalPaPhysicalGreen.sourceVolterraResolvent (barC c) value)=_
  rw [OriginalPaPhysicalGreen.sourceVolterraResolvent_reflect,even]
  rfl

private theorem position_read (value : BurnolL2) (even : reflectL2 value=value) :
    X value=P (Rq value) := by
  unfold burnolAmbientMeanZeroPosition
  rw [evenPart_of_even value even]
  rfl

private theorem fourier_read (value : BurnolL2) (even : reflectL2 value=value) :
    Y value=P (Rq (fourierL2 value)) := by
  unfold burnolAmbientMeanZeroFourier
  rw [evenPart_of_even value even]
  rfl

/-- The complete quarter legs retain both actual means before their B projections. -/
theorem actual_sourceStep_quarters (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) :
    Rq (sourceStep c value)=quarterStep c (Rq value)+
        (-2*sourceTail c value) • SingularCounting.powerL2 c ∧
      Rq (fourierL2 (sourceStep c value))=inwardQuarter (barC c) (Rq (fourierL2 value)) := by
  exact ⟨source_quarter_step c value even,by rw [fourier_source,inward_restriction]⟩

/-- The second drive is the centered original inward action, with the conjugate parameter. -/
def centeredInwardStep (c : BurnolCompletedMellinCoordinate) : M →L[ℂ] M :=
  Constructor.zeroMean.comp ((inwardQuarter (barC c)).comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))

private theorem inward_constant_centered (c : BurnolCompletedMellinCoordinate) :
    P (inwardQuarter c Cq)=0 := by
  have right : 1/4<(c.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  have gap : Rq (Eq Cq)=(1:ℂ) • Cq := by
    rw [burnolQuarterRestriction_zeroExtension,one_smul]
  have generated := OriginalKForcingGapAction.right_resolvent_quarter_constant
    (c.value/2) right (Eq Cq) 1 gap
  change inwardQuarter c Cq=_ at generated
  rw [generated,map_smul,Constructor.zeroMean_constant,smul_zero]

private theorem inward_centering (c : BurnolCompletedMellinCoordinate) (value : Hq) :
    centeredInwardStep c (P value)=P (inwardQuarter (barC c) value) := by
  change P (inwardQuarter (barC c) (P value:Hq))=_
  rw [Constructor.zeroMean_read,map_sub,map_smul,map_sub,map_smul,
    inward_constant_centered,smul_zero,sub_zero]

/-- This coefficient reads the same complete current input, including its mean and exterior tail. -/
def currentAmplitude (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  -2*(sourceTail c value+mu (Rq value)*(q:ℂ)^(1-star c.value)/(1-star c.value))

private theorem actual_position_step (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) :
    X (sourceStep c value)=centeredQuarterStep c (X value)+
      currentAmplitude c value • SingularCounting.centeredPower c := by
  rw [position_read _ (source_even c value even),position_read value even,
    source_quarter_step c value even,map_add,map_smul]
  change P (quarterStep c (Rq value))+(-2*sourceTail c value) • SingularCounting.centeredPower c=
    P (quarterStep c (P (Rq value):Hq))+currentAmplitude c value • SingularCounting.centeredPower c
  rw [Constructor.zeroMean_read,map_sub,map_smul,map_sub,map_smul,centered_constant_step]
  unfold currentAmplitude
  module

private theorem actual_fourier_step (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) :
    Y (sourceStep c value)=centeredInwardStep c (Y value) := by
  rw [fourier_read _ (source_even c value even),fourier_read value even,
    (actual_sourceStep_quarters c value even).2,inward_centering]

/-- The previously nonzero Fourier drive generates four of the original six fixed contacts. -/
def backwardContact (c : BurnolCompletedMellinCoordinate) (value : M) : M :=
  (-2*inner ℂ (SingularCounting.powerL2 (barC c)) (value:Hq)) • contactColumns c 0+
  (2*sourceTail c (fourierL2 (Eq (value:Hq)))) • contactColumns c 1-
  mu (D (value:Hq)) • contactColumns c 2+
  mu (inwardQuarter (barC c) (value:Hq)) • contactColumns c 5

private theorem backward_contact_source (c : BurnolCompletedMellinCoordinate) (value : M)
    (even : sourceMeanZeroReflection value=value) :
    centeredQuarterStep c (S value)-S (centeredInwardStep c value)=backwardContact c value := by
  have raw := congrArg P (backward_source c (value:Hq)
    (congrArg (fun state:M=>(state:Hq)) even))
  rw [map_sub,map_add,map_smul,map_smul] at raw
  change P (quarterStep c (S value:Hq))-P (D (P (inwardQuarter (barC c) (value:Hq)):Hq))=_
  rw [centered_fourier_read,Constructor.zeroMean_read,map_sub,map_smul,map_sub,map_smul,
    map_sub,map_smul,map_sub,map_smul]
  change _=
    (-2*inner ℂ (SingularCounting.powerL2 (barC c)) (value:Hq)) • P (fourierTailColumn c)+
    (2*sourceTail c (fourierL2 (Eq (value:Hq)))) • SingularCounting.centeredPower c-
    mu (D (value:Hq)) • P (quarterStep c Cq)+
    mu (inwardQuarter (barC c) (value:Hq)) • P (D Cq)
  unfold SingularCounting.centeredPower
  linear_combination (norm:=module) raw

private theorem position_even (value : BurnolL2) : sourceMeanZeroReflection (X value)=X value := by
  apply Subtype.ext
  exact burnolAmbientMeanZeroPosition_reflection_fixed value

private theorem fourier_driver_even (value : BurnolL2) : sourceMeanZeroReflection (Y value)=Y value := by
  apply Subtype.ext
  exact burnolAmbientMeanZeroFourier_reflection_fixed value

private theorem first_B_even (value : BurnolL2) : sourceMeanZeroReflection (b value)=b value := by
  apply inverse_even
  apply Subtype.ext
  change reflectRestricted q ((X value:Hq)-(S (Y value):Hq))=
    (X value:Hq)-(S (Y value):Hq)
  have reflected := congrArg (fun state:M=>(state:Hq)) (fourier_even _ (fourier_driver_even value))
  change reflectRestricted q (S (Y value):Hq)=(S (Y value):Hq) at reflected
  rw [map_sub,burnolAmbientMeanZeroPosition_reflection_fixed,reflected]

/-- The complete current carrier generates this first B step; no future state is read. -/
def firstNext (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : M :=
  centeredQuarterStep c (b value)+currentAmplitude c value • logBFirst c 0-
    BI (contactAction c (b value:Hq))+BI (backwardContact c (Y value))

/-- The second B leg retains the actual Fourier drive. -/
def secondNext (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : M :=
  centeredInwardStep c (Y value)-S (firstNext c value)

/-- The original complete even source action generates both actual B feet from its current input. -/
theorem actual_sourceStep_B (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) :
    b (sourceStep c value)=firstNext c value ∧ d (sourceStep c value)=secondNext c value := by
  have feedback := quarter_inverse_action c (X value-S (Y value))
  change centeredQuarterStep c (b value)=
    BI (centeredQuarterStep c (X value-S (Y value)))+BI (quarterCommutator c (b value)) at feedback
  rw [centered_contact_source c _ (first_B_even value)] at feedback
  have generated : b (sourceStep c value)=
      BI (centeredQuarterStep c (X value-S (Y value)))+
      currentAmplitude c value • logBFirst c 0+BI (backwardContact c (Y value)) := by
    change BI (X (sourceStep c value)-S (Y (sourceStep c value)))=_
    rw [actual_position_step c value even,actual_fourier_step c value even]
    have drive : centeredQuarterStep c (X value)+currentAmplitude c value • SingularCounting.centeredPower c-
        S (centeredInwardStep c (Y value))=
        centeredQuarterStep c (X value-S (Y value))+
          currentAmplitude c value • SingularCounting.centeredPower c+backwardContact c (Y value) := by
      rw [map_sub,←backward_contact_source c _ (fourier_driver_even value)]
      module
    rw [drive,map_add,map_add,map_smul]
    rfl
  have first : b (sourceStep c value)=firstNext c value := by
    unfold firstNext
    linear_combination (norm:=module) generated-feedback
  refine ⟨first,?_⟩
  change Y (sourceStep c value)-S (b (sourceStep c value))=_
  rw [actual_fourier_step c value even,first]
  rfl

private theorem position_fourier (value : BurnolL2) : X (fourierL2 value)=Y value := by
  unfold burnolAmbientMeanZeroPosition burnolAmbientMeanZeroFourier
  rw [←fourierL2_burnolAmbientEvenPart]

private theorem fourier_fourier (value : BurnolL2) : Y (fourierL2 value)=X value := by
  unfold burnolAmbientMeanZeroPosition burnolAmbientMeanZeroFourier
  rw [←fourierL2_burnolAmbientEvenPart,fourierL2_fourierL2,burnolAmbientEvenPart_even]

private theorem block_unique (x y left right : M)
    (position : left+S right=x) (fourier : S left+right=y) :
    left=burnolMeanZeroBlockFirst (x,y) ∧ right=burnolMeanZeroBlockSecond (x,y) := by
  have equation : burnolMeanZeroOneMinusSquare left=x-S y := by
    change left-S (S left)=_
    rw [←position,←fourier,map_add]
    module
  have solved := congrArg BI equation
  have inverseLeft : BI*burnolMeanZeroOneMinusSquare=1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  change (BI*burnolMeanZeroOneMinusSquare) left=burnolMeanZeroBlockFirst (x,y) at solved
  rw [inverseLeft] at solved
  change left=burnolMeanZeroBlockFirst (x,y) at solved
  refine ⟨solved,?_⟩
  change right=y-S (burnolMeanZeroBlockFirst (x,y))
  rw [←solved]
  linear_combination (norm:=module) fourier

/-- Fourier exchanges the two feet of the same original B block solve. -/
theorem B_fourier (value : BurnolL2) : b (fourierL2 value)=d value ∧ d (fourierL2 value)=b value := by
  have position := burnolMeanZeroBlock_first_equation (X value,Y value)
  have fourier := burnolMeanZeroBlock_second_equation (X value,Y value)
  change b value+S (d value)=X value at position
  change S (b value)+d value=Y value at fourier
  have swapped := block_unique (Y value) (X value) (d value) (b value)
    (by simpa only [add_comm] using fourier) (by simpa only [add_comm] using position)
  constructor
  · change burnolMeanZeroBlockFirst (X (fourierL2 value),Y (fourierL2 value))=_
    rw [position_fourier,fourier_fourier]
    exact swapped.1.symm
  · change burnolMeanZeroBlockSecond (X (fourierL2 value),Y (fourierL2 value))=_
    rw [position_fourier,fourier_fourier]
    exact swapped.2.symm

private theorem conjugate_twice (c : BurnolCompletedMellinCoordinate) : barC (barC c)=c := by
  cases c
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]

/-- The true Fourier conjugacy computes the original forward R, preserving its original c. -/
theorem actual_forward_R_B (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) :
    b (burnolDirectRightResolventCLM c value)=secondNext (barC c) (fourierL2 value) ∧
      d (burnolDirectRightResolventCLM c value)=firstNext (barC c) (fourierL2 value) := by
  have fftEven : reflectL2 (fourierL2 value)=fourierL2 value := by
    rw [←fourierL2_reflectL2_commute,even]
  have action := actual_sourceStep_B (barC c) (fourierL2 value) fftEven
  rw [source_fourier,conjugate_twice,(B_fourier _).1,(B_fourier _).2] at action
  exact ⟨action.2,action.1⟩

/-- The original position gap removes its actual centered position drive. -/
private theorem position_gap_zero (value : BurnolL2) (even : reflectL2 value=value)
    (gap : value∈locallyConstantFace q) : X value=0 := by
  rw [position_read value even]
  apply Subtype.ext
  exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr gap

private theorem backward_zero (c : BurnolCompletedMellinCoordinate) : backwardContact c 0=0 := by
  simp [backwardContact,burnolQuarterMeanCoefficient]

/-- Under the actual position gap, the next second B foot reads the current second foot, mean and tail. -/
def gapSecondNext (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : M :=
  centeredQuarterStep (barC c) (d value)+currentAmplitude (barC c) (fourierL2 value) • logBFirst (barC c) 0-
    BI (contactAction (barC c) (d value:Hq))

/-- This specialization consumes the original gap and keeps the complete original forward R action. -/
theorem actual_forward_R_gap_B (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) (gap : value∈locallyConstantFace q) :
    b (burnolDirectRightResolventCLM c value)=-S (gapSecondNext c value) ∧
      d (burnolDirectRightResolventCLM c value)=gapSecondNext c value := by
  have zeroDrive : Y (fourierL2 value)=0 := by
    rw [fourier_fourier,position_gap_zero value even gap]
  have first : firstNext (barC c) (fourierL2 value)=gapSecondNext c value := by
    unfold firstNext gapSecondNext
    rw [(B_fourier value).1,zeroDrive,backward_zero,map_zero,add_zero]
  have actual := actual_forward_R_B c value even
  rw [first] at actual
  refine ⟨?_,actual.2⟩
  rw [actual.1,secondNext,zeroDrive,map_zero,first,zero_sub]

end OriginalKFiniteOrderRelease.GenericSourceStepBAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
