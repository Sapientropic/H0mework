import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceJointLocking
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRestSpatialAction

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalElectromagneticDirection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair Stage10 Stage10.CanonicalMatter
open YangMills.FullPairing Electromagnetic.ExternalState Stage9DEF Stage9DEF.Compatibility
open ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open PreparationVacuumElectromagneticIdentity PreparationVacuumRestModeCoupling
open SU7ExteriorBreakingYukawa
open scoped BigOperators Matrix InnerProductSpace
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def sourceLockedValues (i : Fin 3) (values : Source.Index→ℂ) (index : Source.Index) : ℂ :=
  (∑c : Fin 2,values (index.1,c)*sourceColorPauli i index.2 c)+
    (1/2 : ℂ)*(∑s : Fin 4,spinRotation i index.1 s*values (s,index.2))

theorem sourceLockedAction_embedding (i : Fin 3) (values : Source.Index→ℂ) :
    sourceLockedAction i (embed values)=embed (sourceLockedValues i values) := by
  simp only [sourceLockedAction,LinearMap.add_apply,LinearMap.smul_apply]
  rw [generator_embed,spin_embed,←map_smul,←map_add]
  congr 1

def sourceLockedCurrent (mu : Fin 4) (i : Fin 3) : Mother :=
  Complex.I • (diracMatrixMatterAction (diracGamma mu)).comp (sourceLockedAction i)

def sourceLockedCurrentDirection (mu : Fin 4) (i : Fin 3) : Mother :=
  phaseInverse.comp (sourceLockedCurrent mu i)

def sourceLockedCurrentValues (mu : Fin 4) (i : Fin 3) (values : Source.Index→ℂ) (index : Source.Index) : ℂ :=
  -Complex.I*∑s : Fin 4,(diracGammaZero*diracGamma mu) index.1 s*sourceLockedValues i values (s,index.2)

theorem sourceLockedCurrentDirection_embedding (mu : Fin 4) (i : Fin 3) (values : Source.Index→ℂ) :
    sourceLockedCurrentDirection mu i (embed values)=embed (sourceLockedCurrentValues mu i values) := by
  simp only [sourceLockedCurrentDirection,sourceLockedCurrent,LinearMap.comp_apply,
    LinearMap.smul_apply,phaseInverse,LinearMap.neg_apply,map_smul]
  rw [sourceLockedAction_embedding,←LinearMap.comp_apply,←diracMatrixMatterAction_mul,spin_embed,
    ←map_neg,←map_smul]
  congr 1
  funext index
  simp only [sourceLockedCurrentValues,Pi.neg_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem sourceLockedCurrentValues_smul (mu : Fin 4) (i : Fin 3) (c : ℂ) (values : Source.Index→ℂ) :
    sourceLockedCurrentValues mu i (c • values)=c • sourceLockedCurrentValues mu i values := by
  have generated:=(sourceLockedCurrentDirection mu i).map_smul c (embed values)
  rw [←map_smul,sourceLockedCurrentDirection_embedding,sourceLockedCurrentDirection_embedding] at generated
  have read:=congrArg coordinates generated
  simpa only [map_smul,coordinates_embed] using read

private theorem sourceTemporalLockedValues (i : Fin 3) (values : Source.Index→ℂ) :
    sourceLockedCurrentValues 0 i values=Complex.I • sourceLockedValues i values := by
  have source:=sourceLockedCurrentDirection_embedding 0 i values
  simp only [sourceLockedCurrentDirection,sourceLockedCurrent,LinearMap.comp_apply,
    LinearMap.smul_apply,map_smul,diracGamma,Matrix.cons_val_zero,phase_inverse_source] at source
  rw [sourceLockedAction_embedding] at source
  have read:=congrArg coordinates source
  exact (by simpa only [map_smul,coordinates_embed] using read.symm)

private def sourceRotationMatrix (i : Fin 3) : DiracMatrix :=
  ![!![0,Complex.I,0,0;Complex.I,0,0,0;0,0,0,Complex.I;0,0,Complex.I,0],
    !![0,1,0,0;-1,0,0,0;0,0,0,1;0,0,-1,0],
    !![Complex.I,0,0,0;0,-Complex.I,0,0;0,0,Complex.I,0;0,0,0,-Complex.I]] i

private theorem sourceRotationMatrix_generated (i : Fin 3) : spinRotation i=sourceRotationMatrix i := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinRotation,sourceRotationMatrix,diracGamma,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four]

def sourceRestLockedMixing (mu : Fin 4) (i : Fin 3) : Matrix RestStateIndex RestStateIndex ℂ :=
  fun left right=>(1/2 : ℂ)*∑index : Source.Index,star (sourceRestStateValues left index)*
    sourceLockedCurrentValues mu i (sourceRestStateValues right) index

def sourceRestLockedChargeBlock (i : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  let s := (spinScale : ℂ)/2
  ![!![0,0,0,0;0,0,-s,0;0,-s,0,-s;0,0,-s,0],
    !![0,0,0,0;0,0,Complex.I*s,0;0,-Complex.I*s,0,Complex.I*s;0,0,-Complex.I*s,0],
    !![0,0,0,0;0,-1,0,0;0,0,0,0;0,0,0,1]] i

theorem sourceRestLockedCharge_generated (i : Fin 3) (left right : RestStateIndex) :
    sourceRestLockedMixing 0 i left right=
      if left.1=right.1 then sourceRestLockedChargeBlock i left.2 right.2 else 0 := by
  have scale : (spinScale : ℂ)^2=2 := by exact_mod_cast spinScale_sq
  unfold sourceRestLockedMixing
  rw [sourceTemporalLockedValues]
  simp only [Pi.smul_apply,sourceLockedValues,sourceRotationMatrix_generated]
  rcases left with ⟨side,state⟩
  rcases right with ⟨side',state'⟩
  fin_cases i <;> fin_cases side <;> fin_cases side' <;> fin_cases state <;> fin_cases state' <;>
    norm_num [sourceRestLockedChargeBlock,sourceRestStateValues,sourceRestStateCoefficients,
      ChargedPreparation.CanonicalParticle.upperValues,lowerValues,sourceRotationMatrix,
      sourceColorPauli,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two]
  all_goals try ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals try ring_nf
  all_goals norm_num [scale]

private theorem sourceRestAmplitude_square (point : BasePoint) :
    star (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ) := by
  have unit:=actualRestState_orthonormal point (0,0) (0,0)
  rw [actualRestState_full_prepared,inner_embed] at unit
  norm_num [coordinates_embed,actualRestStateCoordinates,sourceRestStateValues,sourceRestStateCoefficients,
    ChargedPreparation.CanonicalParticle.upperValues,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two] at unit
  change (starRingEnd ℂ) (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ)
  linear_combination unit/2

theorem actualRestState_locked_current (mu : Fin 4) (i : Fin 3) (point : BasePoint) (left right : RestStateIndex) :
    actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
      (sourceLockedCurrent mu i (actualRestStatePreparation right (actual.matter point))))=
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*sourceRestLockedMixing mu i left right := by
  rw [Electromagnetic.ExternalState.original_prepared_vertex]
  change 4*(spinScale : ℂ)*inner ℂ
    (operator (actualRestStatePreparation left) (YangMills.FullPairing.prepared point))
    (operator ((sourceLockedCurrentDirection mu i).comp (actualRestStatePreparation right))
      (YangMills.FullPairing.prepared point))=_
  have composed : operator ((sourceLockedCurrentDirection mu i).comp (actualRestStatePreparation right))
      (YangMills.FullPairing.prepared point)=operator (sourceLockedCurrentDirection mu i)
      (operator (actualRestStatePreparation right) (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared,operator_coordinates]
  rw [composed,actualRestState_full_prepared,actualRestState_full_prepared,operator_coordinates,
    sourceLockedCurrentDirection_embedding,inner_embed]
  simp only [coordinates_embed,sourceLockedCurrentValues_smul,actualRestStateCoordinates,
    Pi.smul_apply,smul_eq_mul,star_mul]
  have factor : (∑index : Source.Index,(star (sourceRestStateValues left index)*star (actualRestAmplitude point))*
      (actualRestAmplitude point*sourceLockedCurrentValues mu i (sourceRestStateValues right) index))=
      (star (actualRestAmplitude point)*actualRestAmplitude point)*
        ∑index : Source.Index,star (sourceRestStateValues left index)*
          sourceLockedCurrentValues mu i (sourceRestStateValues right) index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [factor,sourceRestAmplitude_square,Stage10.ActionNormalization.phaseMomentum_source]
  simp only [sourceRestLockedMixing]
  push_cast
  rfl

end LowEnergy.PreparationVacuumPhysicalElectromagneticDirection
