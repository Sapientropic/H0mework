import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRColumnForwardSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKFiniteOrderRelease.GenericSourceStepBAction
open OriginalKFiniteOrderRelease.QuarterSourceCommutator
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace Topology
local notation "q" => (1/4 : ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "F" => fourierL2
local notation "D" => burnolTruncatedFourier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "mu" => burnolQuarterMeanCoefficient
local notation "Cq" => intervalConstant q
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "P0" => Constructor.zeroMean
local notation "P" => burnolEvenAmbientProjection
local notation "R" => burnolDirectRightResolventCLM
open private centered_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open private inverse_even fourier_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction
open private source_fourier fourier_source source_extension from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private sourceTail_extension_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource

private theorem conjugate_twice (c : BurnolCompletedMellinCoordinate) : barC (barC c)=c := by
  cases c
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]

private theorem first_even (c : BurnolCompletedMellinCoordinate) :
    sourceMeanZeroReflection (hPowerBColumn c)=hPowerBColumn c := by
  apply inverse_even
  apply Subtype.ext
  exact centered_reflect c

private theorem second_even (c : BurnolCompletedMellinCoordinate) :
    sourceMeanZeroReflection (hPowerBSecond c)=hPowerBSecond c := by
  apply Subtype.ext
  change reflectRestricted q (-(S (hPowerBColumn c):Hq))=-(S (hPowerBColumn c):Hq)
  rw [map_neg]
  exact congrArg Neg.neg (congrArg (fun v:M=>(v:Hq)) (fourier_even _ (first_even c)))

private theorem extension_even (value : M) (even : sourceMeanZeroReflection value=value) :
    reflectL2 (Eq (value:Hq))=Eq (value:Hq) := by
  change reflectL2 (burnolRadiusZeroExtension q (value:Hq))=_
  rw [burnolRadiusZeroExtension_reflect]
  have reflected:=congrArg (fun v:M=>(v:Hq)) even
  change reflectRestricted q (value:Hq)=(value:Hq) at reflected
  rw [reflected]
  rfl

private theorem unit_source (c : BurnolCompletedMellinCoordinate) :
    hPowerPhysicalCorrection c=Eq (hPowerBColumn c:Hq)+F (Eq (hPowerBSecond c:Hq)) := by
  have first:=extension_even _ (first_even c)
  have second:=extension_even _ (second_even c)
  unfold hPowerPhysicalCorrection burnolAmbientEvenPart
  rw [map_add,←fourierL2_reflectL2_commute,first,second]
  module

/-- The whole source uses the original two B columns before the target forward action is read. -/
def adjointField (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Eq (quarterStep (barC c) (hPowerBColumn (barC c):Hq))+
    F (R c (Eq (hPowerBSecond (barC c):Hq)))

def forwardField (c : BurnolCompletedMellinCoordinate) : BurnolL2 := fourierL2.symm (adjointField c)

def positionMean (c : BurnolCompletedMellinCoordinate) : ℂ := mu (D (hPowerBSecond (barC c):Hq))
def fourierMean (c : BurnolCompletedMellinCoordinate) : ℂ := mu (D (hPowerBColumn (barC c):Hq))
def tailSource (c : BurnolCompletedMellinCoordinate) : ℂ :=
  sourceTail (barC c) (F (Eq (hPowerBSecond (barC c):Hq)))
def constantSource (c : BurnolCompletedMellinCoordinate) : ℂ :=
  positionMean c-mu (SingularCounting.powerL2 (barC c))
def powerAmplitude (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -2*(tailSource c+constantSource c*(q:ℂ)^(1-c.value)/(1-c.value))

/-- The first new unit is the actual resonant log column; the whole power fee remains. -/
def firstFoot (c : BurnolCompletedMellinCoordinate) : M :=
  (-2:ℂ) • logBFirst (barC c) 1+powerAmplitude c • hPowerBColumn (barC c)
def secondFoot (c : BurnolCompletedMellinCoordinate) : M :=
  (-2:ℂ) • logBSecond (barC c) 1+powerAmplitude c • hPowerBSecond (barC c)
def outsideField (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolAmbientEvenPart (Eq (firstFoot c:Hq)+F (Eq (secondFoot c:Hq)))
def physicalField (c : BurnolCompletedMellinCoordinate) : BurnolL2 := adjointField c-outsideField c

theorem actual_adjoint_action (c : BurnolCompletedMellinCoordinate) :
    OriginalWholeDebtRAdjointContactSource.T (barC c) (hPowerPhysicalCorrection (barC c))=
      adjointField c := by
  rw [OriginalWholeDebtRAdjointContactSource.T,sourceStep_actual,unit_source,map_add,
    source_extension,source_fourier,conjugate_twice]
  rfl

theorem adjoint_even (c : BurnolCompletedMellinCoordinate) :
    reflectL2 (adjointField c)=adjointField c := by
  rw [←actual_adjoint_action,OriginalWholeDebtRAdjointContactSource.T,sourceStep_actual]
  change reflectL2 (OriginalPaPhysicalGreen.sourceVolterraResolvent (barC (barC c))
    (hPowerPhysicalCorrection (barC c)))=_
  rw [OriginalPaPhysicalGreen.sourceVolterraResolvent_reflect]
  have even:=burnolAmbientEvenPart_even
    (Eq (hPowerBColumn (barC c):Hq)+F (Eq (hPowerBSecond (barC c):Hq)))
  exact congrArg (OriginalPaPhysicalGreen.sourceVolterraResolvent (barC (barC c))) even

theorem actual_column_action (c : BurnolCompletedMellinCoordinate) :
    R c (physicalOutsideColumn c)=forwardField c := by
  have source:=fourier_source (barC c) (hPowerPhysicalCorrection (barC c))
  rw [conjugate_twice] at source
  have even:=burnolAmbientEvenPart_even
    (Eq (hPowerBColumn (barC c):Hq)+F (Eq (hPowerBSecond (barC c):Hq)))
  have inverse : F (hPowerPhysicalCorrection (barC c))=
      fourierL2.symm (hPowerPhysicalCorrection (barC c)) := by
    apply fourierL2.injective
    rw [fourierL2_fourierL2,fourierL2.apply_symm_apply]
    exact even
  rw [←sourceStep_actual,←OriginalWholeDebtRAdjointContactSource.T,actual_adjoint_action] at source
  rw [inverse] at source
  have output : F (adjointField c)=fourierL2.symm (adjointField c) := by
    apply fourierL2.injective
    rw [fourierL2_fourierL2,fourierL2.apply_symm_apply,adjoint_even]
  exact source.symm.trans output

private theorem mu_add (left right:Hq) : mu (left+right)=mu left+mu right := by
  simp only [burnolQuarterMeanCoefficient,inner_add_right,add_div]

private theorem mu_smul (scalar:ℂ) (value:Hq) : mu (scalar • value)=scalar*mu value := by
  simp only [burnolQuarterMeanCoefficient,inner_smul_right]
  ring

private theorem mu_constant : mu Cq=1 := by
  have nonzero : Cq≠0 := by
    intro zero
    have mass:=burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)
    rw [zero,norm_zero] at mass
    norm_num at mass
  have read:=Constructor.zeroMean_read Cq
  rw [Constructor.zeroMean_constant,ZeroMemClass.coe_zero] at read
  have cancelled : (1-mu Cq) • Cq=0 := by
    linear_combination (norm:=module) -read
  exact (sub_eq_zero.mp ((smul_eq_zero.mp cancelled).resolve_right nonzero)).symm

private theorem unit_inventory (c : BurnolCompletedMellinCoordinate) :
    Rq (hPowerPhysicalCorrection (barC c))=
      SingularCounting.powerL2 (barC c)+constantSource c • Cq ∧
    Rq (F (hPowerPhysicalCorrection (barC c)))=fourierMean c • Cq ∧
    sourceTail (barC c) (hPowerPhysicalCorrection (barC c))=tailSource c := by
  have raw:=unit_source (barC c)
  have firstMean : mu (Rq (hPowerPhysicalCorrection (barC c)))=positionMean c := by
    rw [raw,map_add,burnolQuarterRestriction_zeroExtension]
    change mu ((hPowerBColumn (barC c):Hq)+D (hPowerBSecond (barC c):Hq))=_
    rw [mu_add,Constructor.mean_zero,zero_add]
    rfl
  have centered:=OriginalKCrossParameterRAdjointSource.UnweightedCayleySource.powerCorrection_quarter_source (barC c)
  change P0 (Rq (hPowerPhysicalCorrection (barC c)))=P0 (SingularCounting.powerL2 (barC c)) at centered
  have first : Rq (hPowerPhysicalCorrection (barC c))=
      SingularCounting.powerL2 (barC c)+constantSource c • Cq := by
    have centeredRead:=congrArg (fun state:M=>(state:Hq)) centered
    rw [Constructor.zeroMean_read,Constructor.zeroMean_read,firstMean] at centeredRead
    unfold constantSource
    linear_combination (norm:=module) centeredRead
  have fourierRaw : Rq (F (hPowerPhysicalCorrection (barC c)))=
      D (hPowerBColumn (barC c):Hq)+(hPowerBSecond (barC c):Hq) := by
    rw [raw,map_add,map_add,fourierL2_fourierL2,extension_even _ (second_even _),
      burnolQuarterRestriction_zeroExtension]
    rfl
  have secondCentered : P0 (Rq (F (hPowerPhysicalCorrection (barC c))))=0 := by
    rw [fourierRaw,map_add,
      show P0 (hPowerBSecond (barC c):Hq)=hPowerBSecond (barC c) from
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _]
    change S (hPowerBColumn (barC c))+hPowerBSecond (barC c)=0
    exact (h_power_B_source (barC c)).2
  have second : Rq (F (hPowerPhysicalCorrection (barC c)))=fourierMean c • Cq := by
    have mean : mu (Rq (F (hPowerPhysicalCorrection (barC c))))=fourierMean c := by
      rw [fourierRaw,mu_add,Constructor.mean_zero,add_zero]
      rfl
    have centeredRead:=congrArg (fun state:M=>(state:Hq)) secondCentered
    rw [Constructor.zeroMean_read,ZeroMemClass.coe_zero,mean] at centeredRead
    exact sub_eq_zero.mp centeredRead
  refine ⟨first,second,?_⟩
  rw [raw,map_add,sourceTail_extension_zero,zero_add]
  rfl

theorem actual_source_inventory (c : BurnolCompletedMellinCoordinate) :
    mu (Rq (hPowerPhysicalCorrection (barC c)))=positionMean c ∧
    mu (Rq (F (hPowerPhysicalCorrection (barC c))))=fourierMean c ∧
    sourceTail (barC c) (hPowerPhysicalCorrection (barC c))=tailSource c := by
  have raw:=unit_source (barC c)
  constructor
  · rw [raw,map_add,burnolQuarterRestriction_zeroExtension]
    change mu ((hPowerBColumn (barC c):Hq)+D (hPowerBSecond (barC c):Hq))=_
    rw [mu_add,Constructor.mean_zero,zero_add]
    rfl
  constructor
  · rw [(unit_inventory c).2.1]
    rw [mu_smul,mu_constant,mul_one]
  · exact (unit_inventory c).2.2

theorem actual_quarters (c : BurnolCompletedMellinCoordinate) :
    Rq (adjointField c)=
      (2*constantSource c/(1-c.value)) • Cq+(-2:ℂ) • dividedLogColumn (barC c) 1+
        powerAmplitude c • SingularCounting.powerL2 (barC c) ∧
    Rq (F (adjointField c))=(-2*fourierMean c/c.value) • Cq := by
  have even:=burnolAmbientEvenPart_even
    (Eq (hPowerBColumn (barC c):Hq)+F (Eq (hPowerBSecond (barC c):Hq)))
  have source:=actual_sourceStep_quarters (barC c) (hPowerPhysicalCorrection (barC c)) even
  rw [←sourceStep_actual,←OriginalWholeDebtRAdjointContactSource.T,actual_adjoint_action] at source
  constructor
  · rw [source.1,(unit_inventory c).1,map_add,map_smul,quarterStep_constant,
      show SingularCounting.powerL2 (barC c)=dividedLogColumn (barC c) 0 from rfl,
      quarterStep_log_column,(unit_inventory c).2.2]
    change _= _+(-2:ℂ) • dividedLogColumn (barC c) 1+powerAmplitude c • dividedLogColumn (barC c) 0
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
    unfold powerAmplitude
    module
  · rw [source.2,conjugate_twice,(unit_inventory c).2.1,map_smul]
    have right : 1/4<(c.value/2).re := by rw [Complex.div_re];norm_num;linarith [c.rightHalf]
    have gap : Rq (Eq Cq)=(1:ℂ) • Cq := by rw [burnolQuarterRestriction_zeroExtension,one_smul]
    have constant:=OriginalKForcingGapAction.right_resolvent_quarter_constant
      (c.value/2) right (Eq Cq) 1 gap
    change inwardQuarter c Cq=(-1/(c.value/2)) • Cq at constant
    have rate : (-1:ℂ)/(c.value/2)=-2/c.value := by ring
    rw [rate] at constant
    rw [constant,smul_smul]
    congr 1
    ring

theorem actual_B_feet (c : BurnolCompletedMellinCoordinate) :
    burnolAmbientMeanZeroFirstCorrection (adjointField c)=firstFoot c ∧
    burnolAmbientMeanZeroSecondCorrection (adjointField c)=secondFoot c := by
  have evenPart : burnolAmbientEvenPart (adjointField c)=adjointField c := by
    unfold burnolAmbientEvenPart
    rw [adjoint_even]
    module
  have position : burnolAmbientMeanZeroPosition (adjointField c)=
      (-2:ℂ) • centeredLogColumn (barC c) 1+
        powerAmplitude c • SingularCounting.centeredPower (barC c) := by
    change P0 (Rq (burnolAmbientEvenPart (adjointField c)))=_
    rw [evenPart,(actual_quarters c).1,map_add,map_add,map_smul,map_smul,map_smul,
      Constructor.zeroMean_constant,smul_zero,zero_add]
    rfl
  have fourier : burnolAmbientMeanZeroFourier (adjointField c)=0 := by
    change P0 (Rq (F (burnolAmbientEvenPart (adjointField c))))=0
    rw [evenPart,(actual_quarters c).2,map_smul,Constructor.zeroMean_constant,smul_zero]
  have first : burnolAmbientMeanZeroFirstCorrection (adjointField c)=firstFoot c := by
    change burnolMeanZeroBlockInverse (burnolAmbientMeanZeroPosition (adjointField c)-
      S (burnolAmbientMeanZeroFourier (adjointField c)))=_
    rw [position,fourier,map_zero,sub_zero,map_add,map_smul,map_smul]
    rfl
  refine ⟨first,?_⟩
  change burnolAmbientMeanZeroFourier (adjointField c)-S (burnolAmbientMeanZeroFirstCorrection (adjointField c))=_
  rw [fourier,first,firstFoot,map_add,map_smul,map_smul,zero_sub]
  unfold secondFoot logBSecond hPowerBSecond
  module

theorem actual_outside (c : BurnolCompletedMellinCoordinate) :
    adjointField c-(P (adjointField c):BurnolL2)=outsideField c ∧
    (P (adjointField c):BurnolL2)=physicalField c := by
  have projected:=burnolEvenOrthogonalProjectionOnto_eq_resolventFormula (adjointField c)
  have evenPart : burnolAmbientEvenPart (adjointField c)=adjointField c := by
    unfold burnolAmbientEvenPart
    rw [adjoint_even]
    module
  change (P (adjointField c):BurnolL2)=_ at projected
  unfold burnolAmbientExtendedSonineProjectionFormula burnolAmbientEvenMeanZeroCorrection
    burnolAmbientRawMeanZeroCorrection at projected
  rw [evenPart,(actual_B_feet c).1,(actual_B_feet c).2] at projected
  change (P (adjointField c):BurnolL2)=adjointField c-outsideField c at projected
  exact ⟨by linear_combination (norm:=module) -projected,projected⟩

end OriginalWholeDebtRColumnForwardSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
