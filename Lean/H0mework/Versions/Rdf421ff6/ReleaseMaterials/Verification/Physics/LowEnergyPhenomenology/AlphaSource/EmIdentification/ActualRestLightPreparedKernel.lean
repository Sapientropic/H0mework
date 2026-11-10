import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightMaterialFrame
import Mathlib.Data.Matrix.Basis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceLightCircuit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussFockLift GaussQuantumMultiplier ActualSourcePreparationBridge
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open PreparationVacuumElectromagneticIdentity PreparationVacuumMixedFieldReturn
open MixedSpectatorCandidate ActualElectronPhysicalNormalization
open ActualCompositeFieldCurrent ActualElectronPhysicalJointInverse
open scoped BigOperators InnerProductSpace
attribute [local irreducible] candidate actualElectronPhysicalSeed

/-- Fixed CAR coefficients from the original source preparation columns, not arbitrary one-body matrix coordinates. -/
def sourceRestCARCoefficient (block : RestBlock) (row column : Fin 4) : FiberOp :=
  quantizer (restBlockLift block (Matrix.single row column 1))

def sourceRestCandidateCovariance (dual : Bool) (block : RestBlock) : RestMatterMatrix :=
  fun row column=>inner ℂ (candidate dual) (sourceRestCARCoefficient block row column (candidate dual))

private theorem rest_entry_expansion (B : RestMatterMatrix) :
    B=∑row : Fin 4,∑column : Fin 4,B row column • Matrix.single row column 1 := by
  calc
    B=∑row : Fin 4,∑column : Fin 4,Matrix.single row column (B row column) :=Matrix.matrix_eq_sum_single B
    _=_ := by
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro column _
      simp

private theorem rest_lift_sum {ι : Type*} [Fintype ι] (block : RestBlock) (B : ι→RestMatterMatrix) :
    restBlockLift block (∑i,B i)=∑i,restBlockLift block (B i) := by
  simp only [restBlockLift,Matrix.mul_sum,Matrix.sum_mul]

/-- The original full-CAR light current needs exactly the source four-state coefficients in every generated frame. -/
theorem source_rest_light_CAR_expansion (A : FullMaterialMatrix) :
    quantizer (sourceRestLightMatrix A)=
      ∑block : RestBlock,∑row : Fin 4,∑column : Fin 4,
        sourceRestLight (restBlockRestriction block A) row column • sourceRestCARCoefficient block row column := by
  unfold sourceRestLightMatrix restBlockLightMatrix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro block _
  conv_lhs => rw [rest_entry_expansion (sourceRestLight (restBlockRestriction block A))]
  rw [rest_lift_sum,map_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [rest_lift_sum,map_sum]
  apply Finset.sum_congr rfl
  intro column _
  rw [rest_block_lift_smul,map_smul]
  rfl

def sourceRestLightCandidateRead (dual : Bool) (A : FullMaterialMatrix) : ℂ :=
  ∑block : RestBlock,∑row : Fin 4,∑column : Fin 4,
    sourceRestLight (restBlockRestriction block A) row column*sourceRestCandidateCovariance dual block row column

/-- All source choices in the scalar input profile disappear from this finite material kernel. -/
theorem source_rest_light_candidate_kernel (dual : Bool) (A : FullMaterialMatrix) :
    inner ℂ (candidate dual) (quantizer (sourceRestLightMatrix A) (candidate dual))=
      sourceRestLightCandidateRead dual A := by
  rw [source_rest_light_CAR_expansion]
  simp only [sum_apply,smul_apply,inner_sum,inner_smul_right,
    sourceRestLightCandidateRead,sourceRestCandidateCovariance]

/-- The exact actual N3 preparation consumes the generated source light matrix with its already generated scalar Gram 1/2. -/
theorem actual_material_light_finite_kernel (leg : CompositeLeg) (A : FullMaterialMatrix) :
    inner ℂ (actualElectronPhysicalSeed leg)
      (GaussFockLift.lift (quantizer (sourceRestLightMatrix A)) (actualElectronPhysicalSeed leg))=
      (1/2 : ℂ)*sourceRestLightCandidateRead leg.dual A := by
  rw [actual_material_source_contraction,source_rest_light_candidate_kernel]

end LowEnergy.GaussComposite.ActualSourceLightCircuit
