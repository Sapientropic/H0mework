import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticActualPole
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRestPoleSpectrum

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumRestModeCoupling
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair Stage10 Stage10.CanonicalMatter
open YangMills.FullPairing Electromagnetic.ExternalState Stage9DEF Stage9DEF.Compatibility
open ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open PreparationVacuumElectromagneticIdentity PreparationVacuumStaticPoleResponse
open scoped BigOperators Matrix InnerProductSpace
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def sourceCurrentDirection (mu : Fin 4) (direction : Fin 3) : Mother:=
  phaseInverse.comp (currentAction mu (sourceColorP286Generator direction))

def sourceCurrentValues (mu : Fin 4) (direction : Fin 3) (values : Source.Index→ℂ) (index : Source.Index) : ℂ:=
  -Complex.I*∑spin : Fin 4,(diracGammaZero*diracGamma mu) index.1 spin*
    ∑color : Fin 2,values (spin,color)*sourceColorPauli direction index.2 color

theorem sourceCurrentDirection_embedding (mu : Fin 4) (direction : Fin 3) (values : Source.Index→ℂ) :
    sourceCurrentDirection mu direction (embed values)=embed (sourceCurrentValues mu direction values):=by
  simp only [sourceCurrentDirection,LinearMap.comp_apply,currentAction,LinearMap.smul_apply,
    phaseInverse,LinearMap.neg_apply,map_smul]
  rw [generator_embed,←LinearMap.comp_apply,←SU7ExteriorBreakingYukawa.diracMatrixMatterAction_mul,spin_embed,
    ←map_neg,←map_smul]
  congr 1
  funext index
  simp only [sourceCurrentValues,Pi.neg_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem sourceCurrentValues_smul (mu : Fin 4) (direction : Fin 3) (c : ℂ) (values : Source.Index→ℂ) :
    sourceCurrentValues mu direction (c • values)=c • sourceCurrentValues mu direction values:=by
  funext index
  simp only [sourceCurrentValues,Pi.smul_apply,smul_eq_mul]
  simp_rw [mul_assoc,←Finset.mul_sum,mul_left_comm _ c,←Finset.mul_sum]
  ring

def sourceRestSpatialMixing (mu : Fin 4) (direction : Fin 3) : Matrix RestStateIndex RestStateIndex ℂ:=fun left right=>
  (1/2:ℂ)*∑index : Source.Index,star (sourceRestStateValues left index)*
    sourceCurrentValues mu direction (sourceRestStateValues right) index

private theorem sourceRestAmplitude_square (point : BasePoint) :
    star (actualRestAmplitude point)*actualRestAmplitude point=(1/2:ℂ):=by
  have unit:=actualRestState_orthonormal point (0,0) (0,0)
  rw [actualRestState_full_prepared,inner_embed] at unit
  norm_num [coordinates_embed,actualRestStateCoordinates,sourceRestStateValues,sourceRestStateCoefficients,
    ChargedPreparation.CanonicalParticle.upperValues,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two] at unit
  change (starRingEnd ℂ) (actualRestAmplitude point)*actualRestAmplitude point=(1/2:ℂ)
  linear_combination unit/2

/-- The repaired actual independent dual reads the complete spatial rest-state transition matrix. -/
theorem actualRestState_spatial_current (mu : Fin 4) (direction : Fin 3) (point : BasePoint) (left right : RestStateIndex) :
    actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
      (currentAction mu (sourceColorP286Generator direction) (actualRestStatePreparation right (actual.matter point))))=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceRestSpatialMixing mu direction left right:=by
  rw [Electromagnetic.ExternalState.original_prepared_vertex]
  change 4*(spinScale:ℂ)*inner ℂ
    (operator (actualRestStatePreparation left) (YangMills.FullPairing.prepared point))
    (operator ((sourceCurrentDirection mu direction).comp (actualRestStatePreparation right)) (YangMills.FullPairing.prepared point))=_
  have composed : operator ((sourceCurrentDirection mu direction).comp (actualRestStatePreparation right)) (YangMills.FullPairing.prepared point)=
      operator (sourceCurrentDirection mu direction) (operator (actualRestStatePreparation right) (YangMills.FullPairing.prepared point)):=by
    simp [YangMills.FullPairing.prepared,operator_coordinates]
  rw [composed,actualRestState_full_prepared,actualRestState_full_prepared,operator_coordinates,sourceCurrentDirection_embedding,inner_embed]
  simp only [coordinates_embed,sourceCurrentValues_smul,actualRestStateCoordinates,Pi.smul_apply,smul_eq_mul,star_mul]
  have factor : (∑index : Source.Index,(star (sourceRestStateValues left index)*star (actualRestAmplitude point))*
      (actualRestAmplitude point*sourceCurrentValues mu direction (sourceRestStateValues right) index))=
      (star (actualRestAmplitude point)*actualRestAmplitude point)*
        ∑index : Source.Index,star (sourceRestStateValues left index)*sourceCurrentValues mu direction (sourceRestStateValues right) index:=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [factor,sourceRestAmplitude_square,Stage10.ActionNormalization.phaseMomentum_source]
  simp only [sourceRestSpatialMixing]
  push_cast
  rfl

def sourceKernelCurrentMixing : Matrix RestStateIndex RestStateIndex ℂ:=
  (2:ℂ) • sourceRestSpatialMixing 1 1-(2:ℂ) • sourceRestSpatialMixing 2 0

def sourceKernelCurrentBlock : Matrix (Fin 4) (Fin 4) ℂ:=
  !![0,0,2*Complex.I,0;0,0,0,0;-2*Complex.I,0,0,0;0,0,0,0]

def sourceKernelValues (values : Source.Index→ℂ) (index : Source.Index) : ℂ:=
  if index=(0,1) then 2*Complex.I*values (1,0)
  else if index=(1,0) then -2*Complex.I*values (0,1)
  else if index=(2,1) then -2*Complex.I*values (3,0)
  else if index=(3,0) then 2*Complex.I*values (2,1) else 0

set_option maxHeartbeats 200000 in
theorem sourceKernelValues_generated (values : Source.Index→ℂ) (index : Source.Index) :
    2*sourceCurrentValues 1 1 values index-2*sourceCurrentValues 2 0 values index=sourceKernelValues values index:=by
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    norm_num [sourceCurrentValues,sourceKernelValues,sourceColorPauli,diracGamma,diracGammaZero,
      diracGammaOne,diracGammaTwo,Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_two]
  all_goals norm_num [Matrix.cons_val,Fin.ext_iff]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

theorem sourceKernelCurrentMixing_action (left right : RestStateIndex) :
    sourceKernelCurrentMixing left right=(1/2:ℂ)*∑index : Source.Index,
      star (sourceRestStateValues left index)*sourceKernelValues (sourceRestStateValues right) index:=by
  simp only [sourceKernelCurrentMixing,sourceRestSpatialMixing,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  simp_rw [←sourceKernelValues_generated,mul_sub,Finset.sum_sub_distrib]
  simp only [mul_sub,Finset.mul_sum]
  simp only [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem sourceKernelCurrentMixing_generated (left right : RestStateIndex) :
    sourceKernelCurrentMixing left right=
      if left.1=right.1 then -sourceRestSign left.1*sourceKernelCurrentBlock left.2 right.2 else 0:=by
  rw [sourceKernelCurrentMixing_action]
  rcases left with ⟨side,state⟩
  rcases right with ⟨side',state'⟩
  fin_cases side <;> fin_cases side' <;> fin_cases state <;> fin_cases state' <;>
    norm_num [sourceKernelValues,sourceKernelCurrentBlock,sourceRestSign,sourceRestStateValues,sourceRestStateCoefficients,
      ChargedPreparation.CanonicalParticle.upperValues,lowerValues,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two]
  all_goals norm_num [Matrix.cons_val,Fin.ext_iff]
  all_goals ring

theorem sourceKernelCurrent_charge_commutator (left right : RestStateIndex) :
    (frequency:ℂ)*sourceKernelCurrentMixing left right=
      2*Complex.I*(sourceRestPoleEnergy (sourceRestStatePole left)-sourceRestPoleEnergy (sourceRestStatePole right))*
        sourceRestChargeMixing 2 left right:=by
  rw [sourceKernelCurrentMixing_generated,sourceRestChargeMixing_generated]
  rcases left with ⟨side,state⟩
  rcases right with ⟨side',state'⟩
  fin_cases side <;> fin_cases side' <;> fin_cases state <;> fin_cases state' <;>
    norm_num [sourceRestSign,sourceKernelCurrentBlock,sourceRestChargeMixingBlock,sourceRestPoleEnergy,
      sourceRestStatePole,sourceRestSymmetry]
  all_goals ring

theorem actualRestState_kernel_current (point : BasePoint) (left right : RestStateIndex) :
    2*actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
      (currentAction 1 (sourceColorP286Generator 1) (actualRestStatePreparation right (actual.matter point))))-
    2*actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
      (currentAction 2 (sourceColorP286Generator 0) (actualRestStatePreparation right (actual.matter point))))=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceKernelCurrentMixing left right:=by
  rw [actualRestState_spatial_current,actualRestState_spatial_current]
  simp only [sourceKernelCurrentMixing,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

end LowEnergy.PreparationVacuumRestModeCoupling
