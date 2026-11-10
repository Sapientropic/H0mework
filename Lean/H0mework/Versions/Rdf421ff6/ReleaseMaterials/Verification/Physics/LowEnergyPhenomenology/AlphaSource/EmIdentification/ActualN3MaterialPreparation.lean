import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronPhysicalDomainAndContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourcePreparationBridge
open GaussCoreHilbert GaussCoreDifferential GaussFockLift GaussHalfDensity GaussDensityCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates MixedSpectatorCandidate
open ActualCompositeFieldCurrent ActualElectronPhysicalNormalization ActualElectronPhysicalJointInverse
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumRawJointFeedback
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets
open PreparationVacuumHalfDensityFiber PreparationVacuumFullFieldRiesz
open PreparationVacuumGaugeSourceInjection
open CanonicalGradedSpatialSource
open scoped InnerProductSpace BigOperators
attribute [local irreducible] compositeProfile actualElectronInputInverseNorm
  actualElectronPhysicalSeed actualElectronAmputatedLeg compositeInput candidate candidateTest

def materialTensor (b : Base) (v : FockFiber) : H :=
  fockHalfDensityEquiv.symm (WithLp.toLp 2 (fun word : Occupation => v word • b))

theorem material_tensor_inner (b c : Base) (v w : FockFiber) :
    inner ℂ (materialTensor b v) (materialTensor c w) =
      inner ℂ v w * inner ℂ b c := by
  rw [←fockHalfDensityEquiv.inner_map_map]
  simp only [materialTensor,LinearIsometryEquiv.apply_symm_apply,PiLp.inner_apply,
    inner_smul_left,inner_smul_right]
  simp only [RCLike.inner_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro word _
  ring

private theorem fiber_entry_sum (A : FiberOp) (v : FockFiber) (word : Occupation) :
    ∑ input : Occupation,entry A word input * v input = A v word := by
  have expansion : v=∑ input : Occupation,v input • EuclideanSpace.single input 1 := by
    apply PiLp.ext
    intro output
    simp [WithLp.ofLp_sum,Finset.sum_apply,EuclideanSpace.single,Pi.single_apply]
  conv_rhs => rw [expansion,map_sum]
  simp only [map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,entry]
  apply Finset.sum_congr rfl
  intro input _
  exact mul_comm _ _

theorem material_tensor_lift (b : Base) (v : FockFiber) (A : FiberOp) :
    GaussFockLift.lift A (materialTensor b v)=materialTensor b (A v) := by
  rw [GaussFockLift.lift_apply]
  unfold materialTensor
  apply congrArg fockHalfDensityEquiv.symm
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro word
  rw [flatLift_apply]
  change (∑ input : Occupation,entry A word input • (v input • b)) = A v word • b
  simp only [smul_smul]
  rw [←Finset.sum_smul,fiber_entry_sum]

def actualMaterialBase (leg : CompositeLeg) : Base :=
  actualElectronInputInverseNorm leg •
    halfDensityEquiv 3 (scalarLp 3 (compositeProfile leg.dual))

attribute [local irreducible] actualMaterialBase materialTensor

/-- The actual amputated source keeps its own selected profile and Number-three half density. -/
theorem actual_amputated_material_tensor (leg : CompositeLeg) :
    actualElectronPhysicalSeed leg=materialTensor (actualMaterialBase leg) (candidate leg.dual) := by
  have prepared : fockHalfDensityEquiv (embed (ActualCompositeFieldCurrent.compositeInput leg)) =
      WithLp.toLp 2 (fun word : Occupation => candidate leg.dual word •
        halfDensityEquiv 3 (scalarLp 3 (compositeProfile leg.dual))) := by
    unfold ActualCompositeFieldCurrent.compositeInput
    exact actual_candidate_half_density leg.dual (compositeProfile leg.dual)
  apply fockHalfDensityEquiv.injective
  rw [actualElectronPhysicalSeed,actual_electron_amputated_source]
  simp only [map_smul]
  rw [prepared]
  simp only [materialTensor,LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro word
  change actualElectronInputInverseNorm leg •
    (candidate leg.dual word • halfDensityEquiv 3 (scalarLp 3 (compositeProfile leg.dual))) = _
  simp only [actualMaterialBase,smul_smul,mul_comm]

/-- Candidate Gram two and the actual source's norm one determine the scalar factor. -/
theorem actual_material_base_gram (leg : CompositeLeg) :
    inner ℂ (actualMaterialBase leg) (actualMaterialBase leg)=(1/2:ℂ) := by
  have unit : inner ℂ (actualElectronPhysicalSeed leg) (actualElectronPhysicalSeed leg)=1 := by
    rw [inner_self_eq_norm_sq_to_K,actual_electron_physical_seed_norm]
    norm_num
  rw [actual_amputated_material_tensor,material_tensor_inner,actual_candidate_norm_sq] at unit
  linear_combination (1/2:ℂ)*unit

/-- Every homogeneous material operator on the original full CAR source has a finite source contraction. -/
theorem actual_material_source_contraction (leg : CompositeLeg) (A : FiberOp) :
    inner ℂ (actualElectronPhysicalSeed leg)
      (GaussFockLift.lift A (actualElectronPhysicalSeed leg)) =
        (1/2:ℂ)*inner ℂ (candidate leg.dual) (A (candidate leg.dual)) := by
  rw [actual_amputated_material_tensor,material_tensor_lift,material_tensor_inner,actual_material_base_gram]
  ring

/-- These finite matrices are the literal original independent-dual current and contact symbols. -/
def sourceCurrentMaterial (reader : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FiberOp :=
  GaussQuantumMultiplier.quantizer (rawActionSymbol reader p (sourceState z))

def sourceContactMaterial (reader force : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FiberOp :=
  GaussQuantumMultiplier.quantizer (rawActionContact reader p (sourceState z) (fieldDirection force))

theorem actual_source_current_material (leg : CompositeLeg) (reader : Field289)
    (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    inner ℂ (actualElectronPhysicalSeed leg)
      (GaussFockLift.lift (sourceCurrentMaterial reader p z) (actualElectronPhysicalSeed leg)) =
        (1/2:ℂ)*inner ℂ (candidate leg.dual) (rawStateFiber reader p (sourceState z) (candidate leg.dual)) := by
  rw [actual_material_source_contraction]
  rfl

theorem actual_source_contact_material (leg : CompositeLeg) (reader force : Field289)
    (p : PhysicalMomentum) (z : GaussHistoryHilbert.physicalChart) :
    inner ℂ (actualElectronPhysicalSeed leg)
      (GaussFockLift.lift (sourceContactMaterial reader force p z.val) (actualElectronPhysicalSeed leg)) =
        (1/2:ℂ)*inner ℂ (candidate leg.dual) (rawContactFiber reader force p z.val (candidate leg.dual)) := by
  rw [actual_material_source_contraction]
  rw [sourceContactMaterial,rawActionContact_actual]

end LowEnergy.GaussComposite.ActualSourcePreparationBridge
