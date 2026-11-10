import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualN3PreparedCurrentIntegral
import H0mework.Physics.LowEnergy.Quantum.JointCurrentHeisenberg

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourcePreparationBridge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussFockLift GaussHalfDensity GaussDensityCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open MixedSpectatorCandidate ActualCompositeFieldCurrent ActualElectronPhysicalNormalization ActualElectronPhysicalJointInverse
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumRawJointFeedback
open PreparationVacuumSourceActionJets PreparationVacuumHalfDensityFiber PreparationVacuumFullFieldRiesz
open PreparationVacuumSourceFieldFamily
open PreparationVacuumGaugeSourceInjection CanonicalGradedSpatialSource
open scoped InnerProductSpace BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] candidate sourceState sourceSymbol rawActionSymbol
  actualElectronPhysicalSeed actualElectronAmputatedLeg compositeProfile
abbrev FullMaterialMatrix := Matrix Mode Mode ℂ

/-- This is the original four-CAR normal product, transported through the original fiber coordinates. -/
def materialNormalProduct (A B : FullMaterialMatrix) : FiberOp :=
  (fiberCoordinates.symm.toLinearMap.comp
    ((Fermion.normalProduct A B).comp fiberCoordinates.toLinearMap)).toContinuousLinearMap

theorem material_quantized_normal_order (A B : FullMaterialMatrix) :
    GaussQuantumMultiplier.quantizer A*GaussQuantumMultiplier.quantizer B=
      GaussQuantumMultiplier.quantizer (A*B)+materialNormalProduct A B := by
  apply ContinuousLinearMap.ext
  intro v
  apply fiberCoordinates.injective
  have original:=LinearMap.congr_fun (Fermion.quantize_normal_order A B) (fiberCoordinates v)
  change fiberCoordinates (quantizedFiber A (quantizedFiber B v))=
    fiberCoordinates (quantizedFiber (A*B) v+
      fiberCoordinates.symm (Fermion.normalProduct A B (fiberCoordinates v)))
  simp only [quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_add]
  simpa only [Module.End.mul_apply,LinearMap.add_apply] using original

theorem material_normal_product_symmetric (A B : FullMaterialMatrix) :
    materialNormalProduct A B=materialNormalProduct B A := by
  unfold materialNormalProduct
  rw [SourceJointCurrentHeisenberg.normalProduct_comm]

theorem material_normal_product_sub_left (A B C : FullMaterialMatrix) :
    materialNormalProduct (A-B) C=materialNormalProduct A C-materialNormalProduct B C := by
  apply ContinuousLinearMap.ext
  intro v
  apply fiberCoordinates.injective
  change Fermion.normalProduct (A-B) C (fiberCoordinates v)=
    Fermion.normalProduct A C (fiberCoordinates v)-Fermion.normalProduct B C (fiberCoordinates v)
  simp only [Fermion.normalProduct,Matrix.sub_apply,sub_mul,sub_smul,
    Finset.sum_sub_distrib,LinearMap.sum_apply,LinearMap.smul_apply]

/-- Independent momenta create the source normal-order defect; it is fixed by the Hamiltonian difference. -/
theorem material_two_momentum_sylvester (HL HR A : FullMaterialMatrix) :
    GaussQuantumMultiplier.quantizer HL*GaussQuantumMultiplier.quantizer A-
      GaussQuantumMultiplier.quantizer A*GaussQuantumMultiplier.quantizer HR=
        GaussQuantumMultiplier.quantizer (HL*A-A*HR)+materialNormalProduct (HL-HR) A := by
  rw [material_quantized_normal_order,material_quantized_normal_order,
    material_normal_product_symmetric A HR,material_normal_product_sub_left]
  rw [map_sub]
  abel

def sourceMaterialClock : ℝ := GaussNativeEnergy.sourceTime 0*Real.sqrt 2

def sourceHamiltonianMaterial (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FullMaterialMatrix :=
  sourceSymbol p (sourceState z)

def sourceMaterialSylvester (pL pR : PhysicalMomentum) (z : SourceCoordinateSlice)
    (A : FullMaterialMatrix) : FiberOp :=
  (Complex.I/(sourceMaterialClock:ℂ)) •
    (GaussQuantumMultiplier.quantizer (sourceHamiltonianMaterial pL z)*GaussQuantumMultiplier.quantizer A-
      GaussQuantumMultiplier.quantizer A*GaussQuantumMultiplier.quantizer (sourceHamiltonianMaterial pR z))

def sourceMaterialSylvesterMatrix (pL pR : PhysicalMomentum) (z : SourceCoordinateSlice)
    (A : FullMaterialMatrix) : FullMaterialMatrix :=
  (Complex.I/(sourceMaterialClock:ℂ)) •
    (sourceHamiltonianMaterial pL z*A-A*sourceHamiltonianMaterial pR z)

def sourceMaterialSylvesterResidual (pL pR : PhysicalMomentum) (z : SourceCoordinateSlice)
    (A : FullMaterialMatrix) : FiberOp :=
  (Complex.I/(sourceMaterialClock:ℂ)) •
    materialNormalProduct (sourceHamiltonianMaterial pL z-sourceHamiltonianMaterial pR z) A

theorem source_material_sylvester_generated (pL pR : PhysicalMomentum) (z : SourceCoordinateSlice)
    (A : FullMaterialMatrix) :
    sourceMaterialSylvester pL pR z A=
      GaussQuantumMultiplier.quantizer (sourceMaterialSylvesterMatrix pL pR z A)+
        sourceMaterialSylvesterResidual pL pR z A := by
  unfold sourceMaterialSylvester sourceMaterialSylvesterMatrix sourceMaterialSylvesterResidual
  rw [material_two_momentum_sylvester,map_smul,smul_add]

/-- The exact original raw-current symbol is fed to the complete CAR Sylvester before its actual N3 preparation is read. -/
theorem actual_current_material_sylvester (leg : CompositeLeg) (reader : Field289)
    (pL pR : PhysicalMomentum) (z : SourceCoordinateSlice) :
    inner ℂ (actualElectronPhysicalSeed leg)
      (GaussFockLift.lift
        (sourceMaterialSylvester pL pR z (rawActionSymbol reader pR (sourceState z)))
        (actualElectronPhysicalSeed leg))=
      (1/2:ℂ)*inner ℂ (candidate leg.dual)
        ((GaussQuantumMultiplier.quantizer
          (sourceMaterialSylvesterMatrix pL pR z (rawActionSymbol reader pR (sourceState z)))+
          sourceMaterialSylvesterResidual pL pR z (rawActionSymbol reader pR (sourceState z)))
          (candidate leg.dual)) := by
  rw [actual_material_source_contraction,source_material_sylvester_generated]

end LowEnergy.GaussComposite.ActualSourcePreparationBridge
