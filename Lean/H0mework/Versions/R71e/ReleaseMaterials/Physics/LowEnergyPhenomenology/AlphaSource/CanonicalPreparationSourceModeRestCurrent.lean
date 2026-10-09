import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeModeAction

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalModeChargeRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction DiracCliffordRepresentation Stage9C.Material.SpinPair
open Stage10 Stage10.CanonicalMatter Stage9DEF Stage9DEF.Compatibility
open YangMills.FullPairing Electromagnetic.ExternalState
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalElectromagneticDirection
open PreparationVacuumNativePoleTensor PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback
open Filter Set
open scoped BigOperators Matrix InnerProductSpace Topology
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
attribute [local irreducible] sourceModeCurrent sourceModeCurrentDirection sourceModeMother actualRestStatePreparation

def sourceModeRestValues (F : Fin 289→ℂ) (mu : Fin 4) (values : Source.Index→ℂ) : Source.Index→ℂ :=
  Stage9DEF.Compatibility.coordinates (sourceModeCurrentDirection F mu (embed values))

theorem sourceModeRestValues_smul (F : Fin 289→ℂ) (mu : Fin 4) (c : ℂ) (values : Source.Index→ℂ) :
    sourceModeRestValues F mu (c • values)=c • sourceModeRestValues F mu values := by
  simp only [sourceModeRestValues,map_smul]

/-- Both external legs range over all eight original states; the full mother action is not truncated. -/
def sourceModeRestMixing (F : Fin 289→ℂ) (mu : Fin 4) : Matrix RestStateIndex RestStateIndex ℂ :=
  fun left right=>(1/2 : ℂ)*∑index : Source.Index,star (sourceRestStateValues left index)*
    sourceModeRestValues F mu (sourceRestStateValues right) index

private theorem sourceRestAmplitude_square (point : BasePoint) :
    star (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ) := by
  have unit:=actualRestState_orthonormal point (0,0) (0,0)
  rw [actualRestState_full_prepared,inner_embed] at unit
  norm_num [coordinates_embed,actualRestStateCoordinates,sourceRestStateValues,sourceRestStateCoefficients,
    ChargedPreparation.CanonicalParticle.upperValues,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two] at unit
  change (starRingEnd ℂ) (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ)
  linear_combination unit/2

/-- The actual repaired independent dual generates the full mode current matrix with its original phase coefficient. -/
theorem actualRestState_mode_current (F : Fin 289→ℂ) (mu : Fin 4) (point : BasePoint)
    (left right : RestStateIndex) :
    actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
      (sourceModeCurrent F mu (actualRestStatePreparation right (actual.matter point))))=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceModeRestMixing F mu left right := by
  rw [Electromagnetic.ExternalState.original_prepared_vertex]
  have direction : phaseInverse.comp ((sourceModeCurrent F mu).comp (actualRestStatePreparation right))=
      (sourceModeCurrentDirection F mu).comp (actualRestStatePreparation right) := by
    unfold sourceModeCurrentDirection
    rfl
  rw [direction]
  change 4*(spinScale:ℂ)*inner ℂ
    (operator (actualRestStatePreparation left) (YangMills.FullPairing.prepared point))
    (operator ((sourceModeCurrentDirection F mu).comp (actualRestStatePreparation right))
      (YangMills.FullPairing.prepared point))=_
  have composed : operator ((sourceModeCurrentDirection F mu).comp (actualRestStatePreparation right))
      (YangMills.FullPairing.prepared point)=operator (sourceModeCurrentDirection F mu)
        (operator (actualRestStatePreparation right) (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared,operator_coordinates]
  rw [composed,actualRestState_full_prepared,actualRestState_full_prepared,operator_coordinates,inner_embed]
  change 4*(spinScale:ℂ)*(∑index : Source.Index,star (actualRestStateCoordinates point left index)*
    sourceModeRestValues F mu (actualRestStateCoordinates point right) index)=_
  simp only [actualRestStateCoordinates,sourceModeRestValues_smul,Pi.smul_apply,smul_eq_mul,star_mul]
  have factor : (∑index : Source.Index,(star (sourceRestStateValues left index)*star (actualRestAmplitude point))*
      (actualRestAmplitude point*sourceModeRestValues F mu (sourceRestStateValues right) index))=
      (star (actualRestAmplitude point)*actualRestAmplitude point)*∑index : Source.Index,
        star (sourceRestStateValues left index)*sourceModeRestValues F mu (sourceRestStateValues right) index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [factor,sourceRestAmplitude_square,Stage10.ActionNormalization.phaseMomentum_source]
  simp only [sourceModeRestMixing]
  push_cast
  rfl

/-- The previous joint action and all its non-diagonal charge entries are one generated restriction. -/
theorem sourceModeRestMixing_locked (mu : Fin 4) (i : Fin 3) :
    sourceModeRestMixing (fun j=>(sourceLockedField mu i j:ℂ)) mu=sourceRestLockedMixing mu i := by
  have action : sourceModeCurrentDirection (fun j=>(sourceLockedField mu i j:ℂ)) mu=
      sourceLockedCurrentDirection mu i := by
    unfold sourceModeCurrentDirection sourceModeCurrent sourceLockedCurrentDirection sourceLockedCurrent
    rw [sourceLockedModeMother]
  have values (v : Source.Index→ℂ) : sourceModeRestValues (fun j=>(sourceLockedField mu i j:ℂ)) mu v=
      sourceLockedCurrentValues mu i v := by
    unfold sourceModeRestValues
    rw [action,sourceLockedCurrentDirection_embedding,coordinates_embed]
  ext left right
  simp only [sourceModeRestMixing,sourceRestLockedMixing,values]

/-- Every actual full-field pole residue has the corresponding original full-eight current read. -/
theorem actualSheetRest_current (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (l r : RestStateIndex) (T : ℝ) (mu : Fin 4) (point : BasePoint) (left right : RestStateIndex) :
    actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
      (sourceModeCurrent (actualSheetResidue q epsilon s n p l r T) mu
        (actualRestStatePreparation right (actual.matter point))))=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*
        sourceModeRestMixing (actualSheetResidue q epsilon s n p l r T) mu left right :=
  actualRestState_mode_current _ _ _ _ _

end LowEnergy.PreparationVacuumPhysicalModeChargeRead
