import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactReceiptConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRColumnForwardSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
set_option cleanup.letToHave false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRColumnForwardReceiptConsumer
open Complex BurnolPhysicalState OriginalWholeDebtRAdjointContactSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open OriginalKPairedBEulerJunctionSource.BandFullStockEuler
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalWholeDebtRColumnForwardSource
open private actualPaDelta actual_pa_first_release from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactReceiptConsumer
open private full_source_balance from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource
open scoped InnerProductSpace
local notation "C" => correctionRaw
local notation "V" => physicalOutsideColumn
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "Cq" => intervalConstant (1/4 : ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

def columnContactPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  inner ℂ (regularSource c) (forwardField c)+
    star (sourceJump c 0)*((1-c.value)*inner ℂ (step junctionPoint) (forwardField c)-
      2*inner ℂ (step junctionPoint) (V c))-
    star (sourceTrace c 0)*((1-c.value)*inner ℂ (step (1/4)) (forwardField c)-
      2*inner ℂ (step (1/4)) (V c))-
    star (sourceJump c 1)*(c.value*inner ℂ (fourierL2 (step junctionPoint)) (forwardField c)+
      2*inner ℂ (fourierL2 (step junctionPoint)) (V c))+
    star (sourceTrace c 1)*(c.value*inner ℂ (fourierL2 (step (1/4))) (forwardField c)+
      2*inner ℂ (fourierL2 (step (1/4))) (V c))

private theorem actual_column_contact_price (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (sourceEffect c c) (V c)=columnContactPrice c := by
  simp only [sourceEffect,contactLift,positionContact,fourierContact,
    inner_add_left,inner_sub_left,inner_smul_left,T,
    ContinuousLinearMap.adjoint_inner_left,actual_column_action,
    map_sub,map_one,map_ofNat,starRingEnd_apply,star_star,columnContactPrice]
  ring

private theorem quarter_constant_zero (value : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (value : Hq) Cq=0 := by
  rw [inner_eq_zero_symm]
  exact (Submodule.mem_orthogonal _ _).mp value.property _ (Submodule.mem_span_singleton_self _)

def columnLogPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -2*inner ℂ (sourceSecond c : Hq)
      (OriginalKFiniteOrderRelease.UnitPowerJordanSource.dividedLogColumn (barC c) 1)+
    powerAmplitude c*inner ℂ (sourceSecond c : Hq) (SingularCounting.powerL2 (barC c))

private theorem actual_column_log_price (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (C c) (forwardField c)=columnLogPrice c := by
  have inverse : fourierL2.symm (adjointField c)=fourierL2 (adjointField c) := by
    apply fourierL2.injective
    rw [fourierL2.apply_symm_apply,fourierL2_fourierL2,adjoint_even]
  have extension (value : Hq) (field : BurnolL2) :
      inner ℂ (Eq value) field=inner ℂ value (Rq field) := by
    exact ContinuousLinearMap.adjoint_inner_left Rq field value
  unfold forwardField
  rw [inverse,correctionRaw,inner_add_left,fourierL2.inner_map_map,
    extension,extension,(actual_quarters c).2,(actual_quarters c).1]
  simp only [inner_add_right,inner_smul_right,quarter_constant_zero,mul_zero,zero_add]
  unfold columnLogPrice
  ring

-- The half is a numerical source unit; every regular/contact/outside fee remains in the price.
def columnReturnPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  (1/2 : ℂ)*(columnContactPrice c-star (sigma c c)*columnLogPrice c)

private theorem actual_column_return_price (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (C c) (V c)=columnReturnPrice c := by
  have full := congrArg (fun value : BurnolL2 => inner ℂ value (V c)) (full_source_balance c c)
  rw [actual_column_contact_price,inner_add_left,inner_smul_left,inner_smul_left,
    T,ContinuousLinearMap.adjoint_inner_left,actual_column_action,actual_column_log_price] at full
  simp only [map_ofNat,starRingEnd_apply] at full
  unfold columnReturnPrice
  linear_combination -(1/2 : ℂ)*full

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation

private theorem actual_pa_column_release :
    (∀ k : Nat,k<m → inner ℂ (sourceEffect c c)
      (CombSource.Division.rawIterate observation half.down k
        (actualPaDelta observation nontrivial half depth ordinal : BurnolL2))=0) ∧
    inner ℂ (sourceEffect c c) (CombSource.Division.rawIterate observation half.down m
      (actualPaDelta observation nontrivial half depth ordinal : BurnolL2))=
      star (sigma c c)*
        (OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+3)-
          OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1))*
        ((-2*e)*columnReturnPrice c) := by
  have actual := actual_pa_first_release observation nontrivial half depth ordinal
  rw [actual_column_return_price] at actual
  exact actual

private noncomputable def Result : Sort _ :=
  Σ' prior : type_of% (OriginalWholeDebtRAdjointContactReceiptConsumer.actual_adjoint_contact_source_whole_next
      observation nontrivial half depth ordinal),
    PProd (prior=OriginalWholeDebtRAdjointContactReceiptConsumer.actual_adjoint_contact_source_whole_next
        observation nontrivial half depth ordinal)
      ((type_of% (actual_adjoint_action c)) ∧ (type_of% (actual_column_action c)) ∧
        (type_of% (actual_source_inventory c)) ∧ (type_of% (actual_quarters c)) ∧
        (type_of% (actual_B_feet c)) ∧ (type_of% (actual_outside c)) ∧
        (type_of% (actual_column_contact_price c)) ∧ (type_of% (actual_column_log_price c)) ∧
        (type_of% (actual_column_return_price c)) ∧
        (type_of% (actual_pa_column_release observation nontrivial half depth ordinal)))

/-- The actual Pa first return consumes the forward column's complete log/source fees. -/
noncomputable opaque actual_column_forward_source_whole_next :
    Result observation nontrivial half depth ordinal := by
  let prior := OriginalWholeDebtRAdjointContactReceiptConsumer.actual_adjoint_contact_source_whole_next
    observation nontrivial half depth ordinal
  exact ⟨prior,rfl,actual_adjoint_action c,actual_column_action c,actual_source_inventory c,
    actual_quarters c,actual_B_feet c,actual_outside c,actual_column_contact_price c,
    actual_column_log_price c,actual_column_return_price c,
    actual_pa_column_release observation nontrivial half depth ordinal⟩

end OriginalWholeDebtRColumnForwardReceiptConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
