import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.QuarterSourceCommutator
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open UnitPowerJordanSource UnitPowerJordanAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "D" => burnolTruncatedFourier
local notation "Cq" => intervalConstant q
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def inwardQuarter (c : BurnolCompletedMellinCoordinate) : Hq →L[ℂ] Hq :=
  burnolQuarterRestriction.comp ((burnolDirectRightResolventCLM c).comp burnolQuarterZeroExtension)

private theorem inward_restriction (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    Rq (burnolDirectRightResolventCLM c value)=inwardQuarter c (Rq value) := by
  have right : 1/4<(c.value/2).re := by
    rw [Complex.div_re]; norm_num; linarith [c.rightHalf]
  have gap : Rq (value-Eq (Rq value))=(0:ℂ) • Cq := by
    rw [map_sub,burnolQuarterRestriction_zeroExtension,sub_self,zero_smul]
  have generated := OriginalKForcingGapAction.right_resolvent_quarter_constant
    (c.value/2) right (value-Eq (Rq value)) 0 gap
  change Rq (burnolDirectRightResolventCLM c (value-Eq (Rq value)))=_ at generated
  rw [map_sub,map_sub,neg_zero,zero_div,zero_smul] at generated
  exact sub_eq_zero.mp generated

private theorem extension_inner (value : BurnolL2) (state : Hq) :
    inner ℂ value (Eq state)=inner ℂ (Rq value) state :=
  ContinuousLinearMap.adjoint_inner_right Rq value state

private theorem quarter_adjoint (c : BurnolCompletedMellinCoordinate) (left right : Hq) :
    inner ℂ left (quarterStep c right)=inner ℂ (inwardQuarter c left) right := by
  calc
    _=inner ℂ (Eq left) (sourceStep c (Eq right)) :=
      (ContinuousLinearMap.adjoint_inner_left Rq _ left).symm
    _=inner ℂ (burnolDirectRightResolventCLM c (Eq left)) (Eq right) := by
      rw [←sourceStep_actual,ContinuousLinearMap.adjoint_inner_right]
    _=_ := extension_inner _ _

private theorem source_extension (c : BurnolCompletedMellinCoordinate) (state : Hq) :
    sourceStep c (Eq state)=Eq (quarterStep c state) := by
  apply ext_inner_left ℂ
  intro test
  calc
    _=inner ℂ (burnolDirectRightResolventCLM c test) (Eq state) := by
      rw [←sourceStep_actual,ContinuousLinearMap.adjoint_inner_right]
    _=inner ℂ (inwardQuarter c (Rq test)) state := by
      rw [extension_inner,inward_restriction]
    _=inner ℂ (Rq test) (quarterStep c state) := (quarter_adjoint c _ _).symm
    _=_ := (extension_inner _ _).symm

private theorem source_fourier (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    sourceStep c (fourierL2 value)=fourierL2 (burnolDirectRightResolventCLM (barC c) value) := by
  rw [sourceStep_fourier_source,fourierL2.symm_apply_apply]
  rfl

private theorem fourier_source (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    fourierL2 (sourceStep c value)=burnolDirectRightResolventCLM (barC c) (fourierL2 value) := by
  have actual := source_fourier c (fourierL2 value)
  rw [fourierL2_fourierL2] at actual
  have reflected : sourceStep c (reflectL2 value)=reflectL2 (sourceStep c value) :=
    (OriginalPaPhysicalGreen.sourceVolterraResolvent_reflect (barC c) value).symm
  rw [reflected] at actual
  have transformed := congrArg fourierL2.symm actual
  rw [fourierL2.symm_apply_apply] at transformed
  calc
    _=fourierL2.symm (reflectL2 (sourceStep c value)) := by
      rw [←fourierL2_fourierL2,fourierL2.symm_apply_apply]
    _=_ := transformed

/-- The first Fourier leg is the original inward/outward source intertwining. -/
theorem forward_source (c : BurnolCompletedMellinCoordinate) (value : Hq) :
    D (quarterStep c value)=inwardQuarter (barC c) (D value) := by
  change Rq (fourierL2 (Eq (quarterStep c value)))=_
  rw [←source_extension,fourier_source,inward_restriction]
  rfl

open private source_directRightResolvent_reflect
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.EvenAction

private theorem extension_even (value : Hq) (even : reflectRestricted q value=value) :
    reflectL2 (Eq value)=Eq value := by
  change reflectL2 (burnolRadiusZeroExtension q value)=_
  rw [burnolRadiusZeroExtension_reflect,even]
  rfl

private theorem restriction_even (value : BurnolL2) (even : reflectL2 value=value) :
    reflectRestricted q (Rq value)=Rq value := by
  change reflectRestricted q (restrictToInterval q value)=_
  rw [←restrictToInterval_reflectL2,even]
  rfl

private theorem inward_even (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) :
    reflectL2 (burnolDirectRightResolventCLM c value)=burnolDirectRightResolventCLM c value := by
  change reflectL2 (burnolDirectRightResolvent (c.value/2) value)=_
  rw [source_directRightResolvent_reflect,even]
  rfl

private theorem quarter_inward_even (c : BurnolCompletedMellinCoordinate) (value : Hq)
    (even : reflectRestricted q value=value) :
    reflectRestricted q (inwardQuarter c value)=inwardQuarter c value :=
  restriction_even _ (inward_even _ _ (extension_even _ even))

private theorem evenPart_inner (value test : BurnolL2) (even : reflectL2 test=test) :
    inner ℂ (burnolAmbientEvenPart value) test=inner ℂ value test := by
  have reflected : inner ℂ (reflectL2 value) test=inner ℂ value test := by
    conv_lhs => rw [←even]
    exact reflectL2.inner_map_map _ _
  change inner ℂ ((1/2:ℂ) • (value+reflectL2 value)) test=_
  rw [inner_smul_left,inner_add_left,reflected]
  simp only [starRingEnd_apply]
  norm_num
  ring

private theorem inner_evenPart (value test : BurnolL2) (even : reflectL2 value=value) :
    inner ℂ value (burnolAmbientEvenPart test)=inner ℂ value test := by
  calc
    _=star (inner ℂ (burnolAmbientEvenPart test) value) := (inner_conj_symm _ _).symm
    _=star (inner ℂ test value) := congrArg star (evenPart_inner test value even)
    _=_ := inner_conj_symm _ _

/-- The contact is the existing source-tail adjoint, on the original even component. -/
def tailColumn (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolAmbientEvenPart ((sourceTail c).adjoint (1:ℂ))

private theorem tail_pair (c : BurnolCompletedMellinCoordinate) (test : BurnolL2)
    (even : reflectL2 test=test) :
    inner ℂ test (tailColumn c)=star (sourceTail c test) := by
  unfold tailColumn
  rw [inner_evenPart _ _ even,ContinuousLinearMap.adjoint_inner_right]
  rw [RCLike.inner_apply,one_mul]
  rfl

private theorem quarter_adjoint_left (c : BurnolCompletedMellinCoordinate) (left right : Hq) :
    inner ℂ (quarterStep c left) right=inner ℂ left (inwardQuarter c right) := by
  calc
    _=star (inner ℂ right (quarterStep c left)) := (inner_conj_symm _ _).symm
    _=star (inner ℂ (inwardQuarter c right) left) := congrArg star (quarter_adjoint c right left)
    _=_ := inner_conj_symm _ _

/-- The actual inward source of a quarter input has one original exterior contact. -/
theorem inward_source (c : BurnolCompletedMellinCoordinate) (value : Hq)
    (even : reflectRestricted q value=value) :
    burnolDirectRightResolventCLM c (Eq value)=Eq (inwardQuarter c value)+
      (-2*inner ℂ (SingularCounting.powerL2 c) value) • tailColumn c := by
  have fullEven := inward_even c (Eq value) (extension_even value even)
  have quarterEven := extension_even _ (quarter_inward_even c value even)
  have rightEven : reflectL2 (Eq (inwardQuarter c value)+
      (-2*inner ℂ (SingularCounting.powerL2 c) value) • tailColumn c)=
      Eq (inwardQuarter c value)+(-2*inner ℂ (SingularCounting.powerL2 c) value) • tailColumn c := by
    rw [map_add,map_smul,quarterEven]
    unfold tailColumn
    rw [burnolAmbientEvenPart_even]
  apply ext_inner_left ℂ
  intro test
  let t := burnolAmbientEvenPart test
  have tEven : reflectL2 t=t := burnolAmbientEvenPart_even test
  calc
    _=inner ℂ t (burnolDirectRightResolventCLM c (Eq value)) := (evenPart_inner test _ fullEven).symm
    _=inner ℂ (sourceStep c t) (Eq value) := by
      rw [←sourceStep_actual,ContinuousLinearMap.adjoint_inner_left]
    _=inner ℂ (Rq (sourceStep c t)) value := extension_inner _ _
    _=inner ℂ (quarterStep c (Rq t)+(-2*sourceTail c t) • SingularCounting.powerL2 c) value := by
      rw [source_quarter_step c t tEven]
    _=inner ℂ (Rq t) (inwardQuarter c value)+
        star (-2*sourceTail c t)*inner ℂ (SingularCounting.powerL2 c) value := by
      rw [inner_add_left,inner_smul_left,quarter_adjoint_left]
      rfl
    _=inner ℂ t (Eq (inwardQuarter c value)+
        (-2*inner ℂ (SingularCounting.powerL2 c) value) • tailColumn c) := by
      rw [inner_add_right,inner_smul_right,extension_inner,tail_pair c t tEven]
      simp only [star_mul,star_neg,star_ofNat]
      ring
    _=_ := evenPart_inner test _ rightEven

def fourierTailColumn (c : BurnolCompletedMellinCoordinate) : Hq :=
  Rq (fourierL2 (tailColumn (barC c)))

/-- The second Fourier leg consists of its two actual q-boundary contacts. -/
theorem backward_source (c : BurnolCompletedMellinCoordinate) (value : Hq)
    (even : reflectRestricted q value=value) :
    quarterStep c (D value)-D (inwardQuarter (barC c) value)=
      (-2*inner ℂ (SingularCounting.powerL2 (barC c)) value) • fourierTailColumn c+
      (2*sourceTail c (fourierL2 (Eq value))) • SingularCounting.powerL2 c := by
  have fftEven : reflectL2 (fourierL2 (Eq value))=fourierL2 (Eq value) := by
    rw [←fourierL2_reflectL2_commute,extension_even value even]
  have actual := source_quarter_step c (fourierL2 (Eq value)) fftEven
  rw [source_fourier,inward_source (barC c) value even,map_add,map_smul,map_add,map_smul] at actual
  change D (inwardQuarter (barC c) value)+
      (-2*inner ℂ (SingularCounting.powerL2 (barC c)) value) • fourierTailColumn c=
    quarterStep c (D value)+(-2*sourceTail c (fourierL2 (Eq value))) • SingularCounting.powerL2 c at actual
  linear_combination (norm:=module) -actual

/-- The original square difference is generated by two fixed source contacts. -/
theorem uncentered_square_source (c : BurnolCompletedMellinCoordinate) (value : Hq)
    (even : reflectRestricted q value=value) :
    quarterStep c (D (D value))-D (D (quarterStep c value))=
      (-2*inner ℂ (SingularCounting.powerL2 (barC c)) (D value)) • fourierTailColumn c+
      (2*sourceTail c (fourierL2 (Eq (D value)))) • SingularCounting.powerL2 c := by
  have dEven : reflectRestricted q (D value)=D value := by
    rw [←sourceTruncatedFourier_reflect,even]
  rw [forward_source]
  exact backward_source c (D value) dEven

local notation "S" => burnolMeanZeroTruncatedFourier
local notation "P" => Constructor.zeroMean
local notation "mu" => burnolQuarterMeanCoefficient

private theorem mean_sub (left right : Hq) : mu (left-right)=mu left-mu right := by
  unfold burnolQuarterMeanCoefficient
  rw [inner_sub_right,sub_div]

private theorem mean_smul (scalar : ℂ) (value : Hq) : mu (scalar • value)=scalar*mu value := by
  unfold burnolQuarterMeanCoefficient
  rw [inner_smul_right]
  ring

private theorem centered_fourier_read (value : M) :
    (S value:Hq)=D (value:Hq)-mu (D (value:Hq)) • Cq :=
  Constructor.zeroMean_read _

private theorem centered_square_read (value : M) :
    S (S value)=P (D (D (value:Hq)))-mu (D (value:Hq)) • P (D Cq) := by
  change P (D (S value:Hq))=_
  rw [centered_fourier_read,map_sub,map_smul,map_sub,map_smul]

/-- All centered corrections are retained on their actual source input. -/
theorem centered_square_balance (c : BurnolCompletedMellinCoordinate) (value : M) :
    quarterCommutator c value=
      P (quarterStep c (D (D (value:Hq)))-D (D (quarterStep c (value:Hq))))-
      mu (D (D (value:Hq))) • P (quarterStep c Cq)-
      mu (D (value:Hq)) • P (quarterStep c (P (D Cq):Hq))+
      mu (quarterStep c (value:Hq)) • P (D (D Cq))+
      (mu (D (quarterStep c (value:Hq)))-mu (D Cq)*mu (quarterStep c (value:Hq))) • P (D Cq) := by
  have first : centeredQuarterStep c (S (S value))=
      P (quarterStep c (D (D (value:Hq))))-
      mu (D (D (value:Hq))) • P (quarterStep c Cq)-
      mu (D (value:Hq)) • P (quarterStep c (P (D Cq):Hq)) := by
    rw [centered_square_read,map_sub,map_smul]
    change P (quarterStep c (P (D (D (value:Hq))):Hq))-
      mu (D (value:Hq)) • P (quarterStep c (P (D Cq):Hq))=_
    rw [Constructor.zeroMean_read,map_sub,map_smul,map_sub,map_smul]
  have second : S (S (centeredQuarterStep c value))=
      P (D (D (quarterStep c (value:Hq))))-
      mu (quarterStep c (value:Hq)) • P (D (D Cq))-
      (mu (D (quarterStep c (value:Hq)))-mu (D Cq)*mu (quarterStep c (value:Hq))) • P (D Cq) := by
    rw [centered_square_read]
    change P (D (D (P (quarterStep c (value:Hq)):Hq)))-
      mu (D (P (quarterStep c (value:Hq)):Hq)) • P (D Cq)=_
    rw [Constructor.zeroMean_read,map_sub,map_smul,map_sub,map_smul,map_sub,map_smul,
      mean_sub,mean_smul]
    congr 2
    ring
  unfold quarterCommutator
  rw [first,second,map_sub]
  module

/-- Fixed source-generated contact columns; no target or vanishing coefficient is admitted. -/
def contactColumns (c : BurnolCompletedMellinCoordinate) : Fin 6 → M :=
  ![P (fourierTailColumn c),SingularCounting.centeredPower c,
    P (quarterStep c Cq),P (quarterStep c (P (D Cq):Hq)),P (D (D Cq)),P (D Cq)]

def contactCoefficients (c : BurnolCompletedMellinCoordinate) (value : Hq) : Fin 6 → ℂ :=
  ![-2*inner ℂ (SingularCounting.powerL2 (barC c)) (D value),
    2*sourceTail c (fourierL2 (Eq (D value))),
    -mu (D (D value)),-mu (D value),mu (quarterStep c value),
    mu (D (quarterStep c value))-mu (D Cq)*mu (quarterStep c value)]

def contactAction (c : BurnolCompletedMellinCoordinate) (value : Hq) : M :=
  ∑ i : Fin 6,contactCoefficients c value i • contactColumns c i

/-- The same-input Volterra/Fourier commutator is generated by six fixed original contacts. -/
theorem centered_contact_source (c : BurnolCompletedMellinCoordinate) (value : M)
    (even : sourceMeanZeroReflection value=value) :
    quarterCommutator c value=contactAction c (value:Hq) := by
  have source := congrArg P (uncentered_square_source c (value:Hq)
    (congrArg (fun v:M=>(v:Hq)) even))
  rw [map_add,map_smul,map_smul] at source
  rw [centered_square_balance,source]
  simp only [contactAction,Fin.sum_univ_succ,Fin.sum_univ_zero,contactCoefficients,contactColumns,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  unfold SingularCounting.centeredPower
  module

/-- The original finite source coefficients generate all six contact coefficients. -/
def finiteContactCoefficients (c : BurnolCompletedMellinCoordinate) (j : Nat) (i : Fin 6) : ℂ :=
  ∑ k∈Finset.range j,sourceCoefficient c j k*contactCoefficients c (logBFirst c k:Hq) i

def finiteContactAction (c : BurnolCompletedMellinCoordinate) (j : Nat) : M :=
  ∑ i : Fin 6,finiteContactCoefficients c j i • contactColumns c i

/-- The actual source feedback is a fixed six-column source, with the complete actual means and tails. -/
theorem finite_contact_source (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    finiteCommutator c j=finiteContactAction c j := by
  classical
  unfold finiteCommutator finiteContactAction finiteContactCoefficients
  simp_rw [centered_contact_source c _ (log_B_even c _),contactAction,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_smul.symm

/-- The next original full-adjoint B column directly consumes its fixed contact source. -/
theorem actual_B_source_contact_step (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    burnolAmbientMeanZeroFirstCorrection (sourceField c (j+1))=
      centeredQuarterStep c (burnolAmbientMeanZeroFirstCorrection (sourceField c j))+
      (sourceAmplitude c j-2*finiteMeanContact c j) • logBFirst c 0-
      burnolMeanZeroBlockInverse (finiteContactAction c j) := by
  rw [actual_B_source_step,finite_contact_source]

end OriginalKFiniteOrderRelease.QuarterSourceCommutator
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
