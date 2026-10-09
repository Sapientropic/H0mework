import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedPreparedBalance

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalChargedFieldFactor
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalModeChargeRead PreparationVacuumPhysicalElectromagneticDirection
open PreparationVacuumPhysicalLockedGaussBalance PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets
open GaussComposite GaussComposite.PhysicalModeCharge GaussComposite.PhysicalModeEMCurrent
open Stage9C.Material.SpinPair Electromagnetic.ExternalState DiracExteriorMatterAction
open SourceQuantumNativeDimensions PreparationVacuumElectromagneticIdentity
open Stage10.CanonicalMatter ProofFreeRicherAnholonomicSource Stage9DEF.Compatibility
open scoped Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
open scoped Matrix BigOperators

/-- The coefficient is read at the original rotational Lorentz slot of the actual field. -/
def sourceChargedCoefficient (F : Fin 289→ℂ) (mu : Fin 4) : ℂ :=
  F (lorentzSlot mu (sourceSpinSlot 2))

def sourceChargedLockedField (mu : Fin 4) : Fin 289→ℂ :=
  fun j=>(sourceLockedField mu 2 j:ℂ)

def sourceChargedFieldPart (F : Fin 289→ℂ) : Fin 289→ℂ :=
  ∑mu : Fin 4,sourceChargedCoefficient F mu • sourceChargedLockedField mu

/-- Every other field slot remains in the original field carrier. -/
def sourceChargedFieldRemainder (F : Fin 289→ℂ) : Fin 289→ℂ :=
  F-sourceChargedFieldPart F

private theorem locked_slot (mu nu : Fin 4) :
    sourceChargedLockedField mu (lorentzSlot nu (sourceSpinSlot 2))=
      if nu=mu then (1:ℂ) else 0 := by
  have h:=sourceLockedField_lorentz mu nu 2 (sourceSpinSlot 2)
  change (sourceLockedField mu 2 (lorentzSlot nu (sourceSpinSlot 2)):ℂ)=_
  change sourceLockedField mu 2 (lorentzSlot nu (sourceSpinSlot 2))=
    if nu=mu ∧ sourceSpinSlot 2=sourceSpinSlot 2 then 1 else 0 at h
  simp only [and_true] at h
  rw [h]
  split_ifs <;> norm_num

theorem sourceChargedFieldPart_coefficient (F : Fin 289→ℂ) (mu : Fin 4) :
    sourceChargedCoefficient (sourceChargedFieldPart F) mu=sourceChargedCoefficient F mu := by
  simp only [sourceChargedCoefficient,sourceChargedFieldPart,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,locked_slot,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq Finset.univ mu]
  simp

theorem sourceChargedRemainder_rotational_slot (F : Fin 289→ℂ) (mu : Fin 4) :
    sourceChargedFieldRemainder F (lorentzSlot mu (sourceSpinSlot 2))=0 := by
  change sourceChargedCoefficient F mu-sourceChargedCoefficient (sourceChargedFieldPart F) mu=0
  rw [sourceChargedFieldPart_coefficient,sub_self]

private theorem locked_connection (mu nu : Fin 4) :
    sourceModeConnection nu (sourceChargedLockedField mu)=
      if nu=mu then Quantum.operatorMatrix (sourceLockedAction 2) else 0 := by
  unfold sourceChargedLockedField
  rw [sourceModeConnection_real,sourceLockedField_connection]

theorem sourceChargedConnection_part (F : Fin 289→ℂ) (mu : Fin 4) :
    sourceModeConnection mu (sourceChargedFieldPart F)=
      sourceChargedCoefficient F mu • Quantum.operatorMatrix (sourceLockedAction 2) := by
  simp only [sourceChargedFieldPart,map_sum,map_smul,locked_connection]
  rw [Finset.sum_eq_single mu]
  · rw [if_pos rfl]
  · intro nu _ different
    rw [if_neg (Ne.symm different),smul_zero]
  · intro absent
    exact (absent (Finset.mem_univ mu)).elim

/-- This equality holds on the full original exterior matter representation. -/
theorem sourceChargedMother_generated (F : Fin 289→ℂ) (mu : Fin 4) :
    sourceModeMother F mu=sourceChargedCoefficient F mu • sourceLockedAction 2+
      sourceModeMother (sourceChargedFieldRemainder F) mu := by
  apply Quantum.operatorMatrix.injective
  rw [map_add,map_smul,sourceModeMother_generated,sourceModeMother_generated]
  rw [sourceChargedFieldRemainder,map_sub,sourceChargedConnection_part]
  abel

theorem sourceChargedCurrent_generated (F : Fin 289→ℂ) (mu : Fin 4) :
    PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent F mu=
      sourceChargedCoefficient F mu • sourceLockedCurrent mu 2+
        PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent (sourceChargedFieldRemainder F) mu := by
  unfold PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent sourceLockedCurrent
  rw [sourceChargedMother_generated,LinearMap.comp_add,LinearMap.comp_smul,smul_add,
    smul_comm]

theorem sourceChargedCurrent_minus (F : Fin 289→ℂ) (mu : Fin 4)
    (point : BasePoint) (side : Fin 2) :
    PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent F mu
      (actualRestStatePreparation (side,1) (actual.matter point))=
      sourceChargedCoefficient F mu • currentAction mu Stage10.HyperchargeResponse.chargeDirection
        (actualRestStatePreparation (side,1) (actual.matter point))+
      PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent (sourceChargedFieldRemainder F) mu
        (actualRestStatePreparation (side,1) (actual.matter point)) := by
  rw [sourceChargedCurrent_generated]
  simp only [LinearMap.add_apply,LinearMap.smul_apply]
  have paid:=modeCurrent_minus_actual point side mu
  have lock : PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent (sourceChargedLockedField mu) mu=
      sourceLockedCurrent mu 2 := by
    unfold PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent sourceLockedCurrent
    unfold sourceChargedLockedField
    rw [sourceLockedModeMother]
  change PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent (sourceChargedLockedField mu) mu _=_ at paid
  rw [lock] at paid
  rw [paid]

theorem sourceChargedCurrent_plus (F : Fin 289→ℂ) (mu : Fin 4)
    (point : BasePoint) (side : Fin 2) :
    PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent F mu
      (actualRestStatePreparation (side,3) (actual.matter point))=
      -(sourceChargedCoefficient F mu • currentAction mu Stage10.HyperchargeResponse.chargeDirection
        (actualRestStatePreparation (side,3) (actual.matter point)))+
      PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent (sourceChargedFieldRemainder F) mu
        (actualRestStatePreparation (side,3) (actual.matter point)) := by
  rw [sourceChargedCurrent_generated]
  simp only [LinearMap.add_apply,LinearMap.smul_apply]
  have paid:=modeCurrent_plus_actual point side mu
  have lock : PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent (sourceChargedLockedField mu) mu=
      sourceLockedCurrent mu 2 := by
    unfold PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent sourceLockedCurrent
    unfold sourceChargedLockedField
    rw [sourceLockedModeMother]
  change PreparationVacuumPhysicalModeChargeRead.sourceModeCurrent (sourceChargedLockedField mu) mu _=_ at paid
  rw [lock] at paid
  rw [paid,smul_neg]

end LowEnergy.PreparationVacuumPhysicalChargedFieldFactor
