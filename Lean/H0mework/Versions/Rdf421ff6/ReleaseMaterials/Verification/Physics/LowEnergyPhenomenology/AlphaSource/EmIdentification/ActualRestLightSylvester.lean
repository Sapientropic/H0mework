import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestMaterialHamiltonian
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightPreparedKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceLightCircuit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussFockLift GaussQuantumMultiplier ActualSourcePreparationBridge
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open PreparationVacuumElectromagneticIdentity PreparationVacuumActionFieldLift PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalDensity PreparationVacuumSourceFieldFamily
open CanonicalGradedSpatialSource MixedSpectatorCandidate ActualCompositeFieldCurrent ActualElectronPhysicalJointInverse
open scoped BigOperators InnerProductSpace
attribute [local irreducible] actualElectronPhysicalSeed candidate rawActionSymbol sourceState sourceHamiltonianMaterial

private theorem rest_restriction_left_lift (left right : RestBlock) (H : FullMaterialMatrix) (B : RestMatterMatrix) :
    restBlockRestriction left (H*restBlockLift right B)=
      if left=right then restBlockRestriction left H*B else 0 := by
  unfold restBlockRestriction restBlockLift
  calc
    _=((restBlockFrame left).conjTranspose*H*restBlockFrame right)*B*
      ((restBlockFrame right).conjTranspose*restBlockFrame left) := by simp only [Matrix.mul_assoc]
    _=if left=right then ((restBlockFrame left).conjTranspose*H*restBlockFrame left)*B else 0 := by
      rw [rest_block_frame_gram]
      by_cases same : left=right
      · subst right;simp
      · simp [same,Ne.symm same]

private theorem rest_restriction_right_lift (left right : RestBlock) (H : FullMaterialMatrix) (B : RestMatterMatrix) :
    restBlockRestriction left (restBlockLift right B*H)=
      if left=right then B*restBlockRestriction left H else 0 := by
  unfold restBlockRestriction restBlockLift
  calc
    _=((restBlockFrame left).conjTranspose*restBlockFrame right)*B*
      ((restBlockFrame right).conjTranspose*H*restBlockFrame left) := by simp only [Matrix.mul_assoc]
    _=if left=right then B*((restBlockFrame left).conjTranspose*H*restBlockFrame left) else 0 := by
      rw [rest_block_frame_gram]
      by_cases same : left=right
      · subst right;simp only [if_true,Matrix.one_mul,Matrix.mul_assoc]
      · simp [same]

private theorem rest_light_H_left (block : RestBlock) (H A : FullMaterialMatrix) :
    restBlockRestriction block (H*sourceRestLightMatrix A)=
      restBlockRestriction block H*sourceRestLight (restBlockRestriction block A) := by
  unfold sourceRestLightMatrix restBlockLightMatrix
  simp only [Matrix.mul_sum,restBlockRestriction,Matrix.mul_sum,Matrix.sum_mul]
  change (∑b : RestBlock,restBlockRestriction block (H*restBlockLift b
    (sourceRestLight (restBlockRestriction b A))))=_
  simp only [rest_restriction_left_lift]
  simp [restBlockRestriction]

private theorem rest_light_H_right (block : RestBlock) (H A : FullMaterialMatrix) :
    restBlockRestriction block (sourceRestLightMatrix A*H)=
      sourceRestLight (restBlockRestriction block A)*restBlockRestriction block H := by
  unfold sourceRestLightMatrix restBlockLightMatrix
  simp only [Matrix.sum_mul,restBlockRestriction,Matrix.mul_sum,Matrix.sum_mul]
  change (∑b : RestBlock,restBlockRestriction block (restBlockLift b
    (sourceRestLight (restBlockRestriction b A))*H))=_
  simp only [rest_restriction_right_lift]
  simp [restBlockRestriction]

/-- The original two-momentum matching matrix is the true source block restriction of the complete light material Sylvester. -/
theorem source_rest_light_two_momentum_matching (side : Fin 2) (pL pR : PhysicalMomentum) (A : FullMaterialMatrix) :
    restBlockRestriction (false,side) (sourceMaterialSylvesterMatrix pL pR GaussHistoryHilbert.sourcePoint.val
      (sourceRestLightMatrix A))=
      actualMatterMatchingSylvester 0 side pL pR (sourceRestLight (restBlockRestriction (false,side) A)) := by
  unfold sourceMaterialSylvesterMatrix
  rw [rest_block_restriction_smul]
  have subtract (B C : FullMaterialMatrix) : restBlockRestriction (false,side) (B-C)=
      restBlockRestriction (false,side) B-restBlockRestriction (false,side) C := by
    simp only [restBlockRestriction,Matrix.mul_sub,Matrix.sub_mul]
  rw [subtract,rest_light_H_left,rest_light_H_right,source_rest_primal_hamiltonian,source_rest_primal_hamiltonian]
  rw [matching_clock_same_source]
  rfl

/-- The same actual current, now source-light, still generates its genuine four-CAR two-momentum residue on actual N3. -/
theorem actual_light_current_material_sylvester (leg : CompositeLeg) (reader : Field289)
    (pL pR : PhysicalMomentum) (z : SourceCoordinateSlice) :
    inner ℂ (actualElectronPhysicalSeed leg)
      (GaussFockLift.lift (sourceMaterialSylvester pL pR z
        (sourceRestLightMatrix (rawActionSymbol reader pR (sourceState z)))) (actualElectronPhysicalSeed leg))=
      (1/2 : ℂ)*inner ℂ (candidate leg.dual)
        ((quantizer (sourceMaterialSylvesterMatrix pL pR z
          (sourceRestLightMatrix (rawActionSymbol reader pR (sourceState z))))+
          sourceMaterialSylvesterResidual pL pR z
            (sourceRestLightMatrix (rawActionSymbol reader pR (sourceState z)))) (candidate leg.dual)) := by
  rw [actual_material_source_contraction,source_material_sylvester_generated]

/-- Equal momenta remove the original normal-order term algebraically, without changing the actual N3 carrier. -/
theorem source_material_equal_momentum_residual (p : PhysicalMomentum) (z : SourceCoordinateSlice) (A : FullMaterialMatrix) :
    sourceMaterialSylvesterResidual p p z A=0 := by
  unfold sourceMaterialSylvesterResidual
  have zero:=material_normal_product_sub_left (sourceHamiltonianMaterial p z) (sourceHamiltonianMaterial p z) A
  rw [sub_self,sub_self] at zero
  rw [sub_self,zero,smul_zero]

end LowEnergy.GaussComposite.ActualSourceLightCircuit
