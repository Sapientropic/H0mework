import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedFirstResidue
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceJointCausalField
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualNativePole

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalModeChargeRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumSourceActionJets PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumPhysicalLockedCurrentFirstResidue
open PreparationVacuumFullSlowFieldResponse PreparationVacuumNativePoleTensor PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCharacteristic
open FullQuantum.StateGreen Electromagnetic.CanonicalCoframe
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge CanonicalGradedSpatialSource
open DiracExteriorMatterAction DiracCliffordRepresentation
open Stage10.CanonicalMatter StageNineHolonomicField YangMills.FullPairing
open Filter Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator Topology InnerProductSpace
local instance : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local irreducible] actualSheetField actualSheetResidue sourceLockedField fieldDirectionLinear

/-- The original full Field289 action is complexified only after its physical real derivative is fixed. -/
def sourceModeConnection (mu : Fin 4) : (Fin 289→ℂ)→L[ℂ] SourceMatrix :=
  ∑j : Fin 289,(ContinuousLinearMap.proj j : (Fin 289→ℂ)→L[ℂ] ℂ).smulRight
    (connectionDirection (PreparationVacuumMixedFieldReturn.sourceField (fieldUnit j)) mu)

private def connectionSelect (mu : Fin 4) : ActionState→ₗ[ℝ] SourceMatrix where
  toFun s:=s.2.1 mu
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem sourceModeConnection_apply (mu : Fin 4) (F : Fin 289→ℂ) :
    sourceModeConnection mu F=∑j : Fin 289,F j •
      connectionDirection (PreparationVacuumMixedFieldReturn.sourceField (fieldUnit j)) mu := by
  simp only [sourceModeConnection,sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

/-- This is exactly the original gauge plus Lorentz connection on any physical real field. -/
theorem sourceModeConnection_real (mu : Fin 4) (f : Field289) :
    sourceModeConnection mu (fun j=>(f j:ℂ))=
      connectionDirection (PreparationVacuumMixedFieldReturn.sourceField f) mu := by
  have generated:=congrArg (connectionSelect mu) (fieldDirection_coordinates f)
  simp only [map_sum,map_smul] at generated
  change connectionDirection (PreparationVacuumMixedFieldReturn.sourceField f) mu=
    ∑j : Fin 289,f j • connectionDirection (PreparationVacuumMixedFieldReturn.sourceField (fieldUnit j)) mu at generated
  rw [sourceModeConnection_apply]
  calc
    _=∑j : Fin 289,f j • connectionDirection (PreparationVacuumMixedFieldReturn.sourceField (fieldUnit j)) mu := by
      apply Finset.sum_congr rfl
      intro j _
      ext a b
      simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
    _=_ := generated.symm

/-- The original full-matter representation fixes the mode generator; no electromagnetic direction is supplied. -/
def sourceModeMother (F : Fin 289→ℂ) (mu : Fin 4) : Mother :=
  Quantum.operatorMatrix.symm (sourceModeConnection mu F)

theorem sourceModeMother_generated (F : Fin 289→ℂ) (mu : Fin 4) :
    Quantum.operatorMatrix (sourceModeMother F mu)=sourceModeConnection mu F :=
  Quantum.operatorMatrix.apply_symm_apply _

def sourceModeCurrent (F : Fin 289→ℂ) (mu : Fin 4) : Mother :=
  Complex.I • ((diracMatrixMatterAction (diracGamma mu)).comp (sourceModeMother F mu))

def sourceModeCurrentDirection (F : Fin 289→ℂ) (mu : Fin 4) : Mother :=
  phaseInverse.comp (sourceModeCurrent F mu)

/-- The generated locking action is one exact restriction of the same full Field289 mode action. -/
theorem sourceLockedModeMother (mu : Fin 4) (i : Fin 3) :
    sourceModeMother (fun j=>(sourceLockedField mu i j:ℂ)) mu=sourceLockedAction i := by
  apply Quantum.operatorMatrix.injective
  rw [sourceModeMother_generated,sourceModeConnection_real,sourceLockedField_connection,if_pos rfl]

/-- Both original simple pole branches feed their actual full289 field into this same source action. -/
theorem sourceActualSheetConnection_residue (q : PhysicalResponsePoint) (branch : Fin 2)
    (n p : PhysicalMomentum) (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ) (mu : Fin 4) :
    ∀ᶠ e in scaleApproach,
      Tendsto (fun t=>((t-sourceSheet branch n unit e.val:ℝ):ℂ) •
        sourceModeConnection mu (actualSheetField q e.val t n p l r T))
        (𝓝[≠] (sourceSheet branch n unit e.val))
        (𝓝 (sourceModeConnection mu (actualSheetResidue q e.val (sourceSheet branch n unit e.val) n p l r T))) := by
  filter_upwards [actualSheetField_residue q branch n p unit l r T] with e pole
  have generated:=(sourceModeConnection mu).continuous.tendsto _ |>.comp pole
  simpa only [Function.comp_def,map_smul] using generated

end LowEnergy.PreparationVacuumPhysicalModeChargeRead
