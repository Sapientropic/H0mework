import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceRestResolvent
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightNoetherPartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMovingSourceLight
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open ActualSourcePreparationBridge ActualSourceLightCircuit
open PreparationVacuumMixedFieldReturn PreparationVacuumFullFieldRiesz
open PreparationVacuumElectromagneticIdentity MixedSpectatorCandidate
open PreparationVacuumActualFieldQuantization
open GaussQuantumMultiplier ActualCompositeFieldCurrent ActualElectronPhysicalNormalization
open ActualElectronPhysicalJointInverse
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
local instance instDecidableEqMode_actualSourceMovingCARCoefficients : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance movingCellFinite : FiniteDimensional ℂ FullMaterialMatrix:=Matrix.finiteDimensional
attribute [local irreducible] candidate restBlockFrame sourceHSCoordinates

def sourceHSCell (input : HSIndex) : HS:=
  sourceHSCoordinates (Matrix.single input.1 input.2 1)

/-- These coefficients use the original source four-state CAR columns on every independent branch. -/
def sourceMovingCARCellMap (block : RestBlock) (output input : HSIndex) :
    FullMaterialMatrix→L[ℂ]FullMaterialMatrix:=
  (show FullMaterialMatrix→ₗ[ℂ]FullMaterialMatrix from
    {toFun:=fun A=>restBlockRestriction block A input.1 input.2 •
        restBlockLift block (Matrix.single output.1 output.2 1)
     map_add':=by
       intro A B
       rw [rest_block_restriction_add]
       exact add_smul _ _ _
     map_smul':=by
       intro q A
       rw [rest_block_restriction_smul]
       exact mul_smul _ _ _}).toContinuousLinearMap

def sourceHSOperatorCell (output input : HSIndex) : HSOperator→L[ℂ]ℂ:=
  (PiLp.proj 2 (fun _ : HSIndex=>ℂ) output).comp
    (ContinuousLinearMap.apply ℂ HS (sourceHSCell input))

def sourceMovingMaterialMatrix (projector : RestBlock→HSOperator) (A : FullMaterialMatrix) : FullMaterialMatrix:=
  ∑block : RestBlock,restBlockLift block
    (sourceHSCoordinates.symm (projector block (sourceHSCoordinates (restBlockRestriction block A))))

def sourceMovingMaterialCandidateRead (projector : RestBlock→HSOperator) (dual : Bool)
    (A : FullMaterialMatrix) : ℂ:=
  ∑block : RestBlock,∑output : HSIndex,
    (projector block (sourceHSCoordinates (restBlockRestriction block A))) output*
      sourceRestCandidateCovariance dual block output.1 output.2

theorem source_moving_CAR_cell_value (block : RestBlock) (output input : HSIndex) (A : FullMaterialMatrix) :
    quantizer (sourceMovingCARCellMap block output input A)=
      restBlockRestriction block A input.1 input.2 • sourceRestCARCoefficient block output.1 output.2:=by
  change quantizer (restBlockRestriction block A input.1 input.2 •
    restBlockLift block (Matrix.single output.1 output.2 1))=_
  rw [map_smul]
  rfl

private theorem moving_rest_entry_expansion (B : RestMatterMatrix) :
    B=∑input : HSIndex,B input.1 input.2 • Matrix.single input.1 input.2 1:=by
  rw [Fintype.sum_prod_type]
  calc
    B=∑row : Fin 4,∑column : Fin 4,Matrix.single row column (B row column):=Matrix.matrix_eq_sum_single B
    _=_:=by simp

theorem source_HS_input_expansion (B : RestMatterMatrix) :
    sourceHSCoordinates B=∑input : HSIndex,B input.1 input.2 • sourceHSCell input:=by
  conv_lhs=>rw [moving_rest_entry_expansion B]
  simp only [map_sum,map_smul,sourceHSCell]

theorem source_HS_operator_cell_expansion (projector : HSOperator) (B : RestMatterMatrix) (output : HSIndex) :
    projector (sourceHSCoordinates B) output=
      ∑input : HSIndex,B input.1 input.2*sourceHSOperatorCell output input projector:=by
  rw [source_HS_input_expansion]
  rw [map_sum]
  change (PiLp.proj (𝕜:=ℂ) 2 (fun _ : HSIndex=>ℂ) output)
    (∑input : HSIndex,projector (B input.1 input.2 • sourceHSCell input))=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [map_smul,map_smul]
  rfl

/-- All sixteen output covariances, including the source off-diagonal entries, survive a moving projector. -/
theorem source_moving_material_CAR_expansion (projector : RestBlock→HSOperator) (A : FullMaterialMatrix) :
    quantizer (sourceMovingMaterialMatrix projector A)=
      ∑block : RestBlock,∑output : HSIndex,
        (projector block (sourceHSCoordinates (restBlockRestriction block A))) output •
          sourceRestCARCoefficient block output.1 output.2:=by
  unfold sourceMovingMaterialMatrix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro block _
  conv_lhs=>rw [moving_rest_entry_expansion (sourceHSCoordinates.symm
    (projector block (sourceHSCoordinates (restBlockRestriction block A))))]
  simp only [restBlockLift,Matrix.mul_sum,Matrix.sum_mul,map_sum,Matrix.mul_smul,Matrix.smul_mul,map_smul]
  simp only [sourceHSCoordinates,sourceRestCARCoefficient,restBlockLift]
  rfl

theorem source_moving_material_candidate_kernel (projector : RestBlock→HSOperator)
    (dual : Bool) (A : FullMaterialMatrix) :
    inner ℂ (candidate dual) (quantizer (sourceMovingMaterialMatrix projector A) (candidate dual))=
      sourceMovingMaterialCandidateRead projector dual A:=by
  rw [source_moving_material_CAR_expansion]
  simp only [sum_apply,smul_apply,inner_sum,inner_smul_right,
    sourceMovingMaterialCandidateRead,sourceRestCandidateCovariance]

/-- The moving source CAR operator is reconstructed from the same fixed source columns that enter each original Noether integral. -/
theorem source_moving_material_CAR_cells (projector : RestBlock→HSOperator) (A : FullMaterialMatrix) :
    quantizer (sourceMovingMaterialMatrix projector A)=
      ∑cell : RestBlock×(HSIndex×HSIndex),
        sourceHSOperatorCell cell.2.1 cell.2.2 (projector cell.1) •
          quantizer (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2 A):=by
  rw [source_moving_material_CAR_expansion]
  conv_rhs=>rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro block _
  conv_rhs=>rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro output _
  rw [source_HS_operator_cell_expansion]
  calc
    _=∑input : HSIndex,((restBlockRestriction block A) input.1 input.2*
      sourceHSOperatorCell output input (projector block)) • sourceRestCARCoefficient block output.1 output.2:=
      Finset.sum_smul
    _=_:=by
      apply Finset.sum_congr rfl
      intro input _
      rw [source_moving_CAR_cell_value,smul_smul]
      rw [mul_comm]

theorem actual_material_moving_finite_kernel (projector : RestBlock→HSOperator)
    (leg : CompositeLeg) (A : FullMaterialMatrix) :
    inner ℂ (actualElectronPhysicalSeed leg)
      (GaussFockLift.lift (quantizer (sourceMovingMaterialMatrix projector A)) (actualElectronPhysicalSeed leg))=
      (1/2 : ℂ)*sourceMovingMaterialCandidateRead projector leg.dual A:=by
  rw [actual_material_source_contraction,source_moving_material_candidate_kernel]

end LowEnergy.GaussComposite.ActualMovingSourceLight
