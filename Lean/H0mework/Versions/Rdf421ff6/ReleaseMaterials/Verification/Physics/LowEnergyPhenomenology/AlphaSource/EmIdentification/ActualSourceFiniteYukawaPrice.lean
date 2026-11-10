import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualQuantitativePreparedFrame
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceQuantumCARBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceFiniteYukawaPriceOwn
open SaturationMonoid.PhysicsCore
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussYukawaCoefficient GaussQuantumMultiplier
open ActualQuantitativePreparedFrameOwn
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq ScalarBasisIndex := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
abbrev OneParticleIndex := SaturationMonoid.PhysicsCore.LowEnergy.Quantum.Index

theorem original_scalar_basis_coordinate (a : ScalarBasisIndex) :
    scalarCoordinateEquiv (su7ExteriorBasis 4 a) = EuclideanSpace.single a 1 := by
  apply PiLp.ext
  intro b
  change (su7ExteriorBasis 4).repr (su7ExteriorBasis 4 a) b = (EuclideanSpace.single a (1 : ℂ)) b
  simp [EuclideanSpace.single, Finsupp.single_apply, eq_comm]

theorem original_vacuum_four_channel :
    SourceQuantumScalarChart.vacuum = ∑ output : Fin 2, ∑ input : Fin 2,
      EuclideanSpace.single (finiteGenerationScalarIndex output input) 1 := by
  rw [SourceQuantumScalarChart.vacuum, sourceGeneratedVacuumCoordinates,
    positive_sourceGeneratedVacuumBase, finiteGenerationJointBreakingScalar, map_sum]
  simp only [map_sum, finiteGenerationBreakingTensor, original_scalar_basis_coordinate]

theorem original_vacuum_norm_bound : ‖SourceQuantumScalarChart.vacuum‖ ≤ 4 := by
  rw [original_vacuum_four_channel]
  calc
    _ ≤ ∑ output : Fin 2, ∑ input : Fin 2,
        ‖EuclideanSpace.single (finiteGenerationScalarIndex output input) (1 : ℂ)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun output _ => norm_sum_le _ _)
    _ = 4 := by norm_num [PiLp.norm_single]

-- Fixed original scalar-to-one-particle Yukawa coefficients, prior to full CAR quantization.
def sourceTensor (a : ScalarBasisIndex) (i j : OneParticleIndex) : ℂ :=
  GaussYukawaCoefficient.primal (EuclideanSpace.single a 1) i j
def tensorEntryPrice (a : ScalarBasisIndex) (i j : OneParticleIndex) : ℝ :=
  |(sourceTensor a i j).re| + |(sourceTensor a i j).im|
def sourceTensorPrice : ℝ := ∑ a : ScalarBasisIndex, ∑ i : OneParticleIndex,
  ∑ j : OneParticleIndex, tensorEntryPrice a i j

theorem sourceTensorPrice_nonnegative : 0 ≤ sourceTensorPrice := by
  unfold sourceTensorPrice tensorEntryPrice
  positivity

theorem original_scalar_expansion (phi : Scalar) :
    phi = ∑ a : ScalarBasisIndex, phi a • EuclideanSpace.single a 1 := by
  apply PiLp.ext
  intro a
  simp [WithLp.ofLp_sum, Finset.sum_apply, EuclideanSpace.single, Pi.single_apply]

theorem original_primal_entry_bound (phi : Scalar) (i j : OneParticleIndex) :
    ‖GaussYukawaCoefficient.primal phi i j‖ ≤
      ∑ a : ScalarBasisIndex, ‖phi‖ * tensorEntryPrice a i j := by
  have expansion : GaussYukawaCoefficient.primal phi i j =
      ∑ a : ScalarBasisIndex, phi a * sourceTensor a i j := by
    conv_lhs => rw [original_scalar_expansion phi]
    simp only [map_sum, Matrix.sum_apply, map_smul, Matrix.smul_apply, smul_eq_mul, sourceTensor]
  rw [expansion]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [norm_mul]
  exact mul_le_mul (PiLp.norm_apply_le phi a) (Complex.norm_le_abs_re_add_abs_im _)
    (norm_nonneg _) (norm_nonneg _)

theorem original_primal_l1_bound (phi : Scalar) :
    (∑ i : OneParticleIndex, ∑ j : OneParticleIndex, ‖GaussYukawaCoefficient.primal phi i j‖) ≤
      ‖phi‖ * sourceTensorPrice := by
  calc
    _ ≤ ∑ i : OneParticleIndex, ∑ j : OneParticleIndex, ∑ a : ScalarBasisIndex,
        ‖phi‖ * tensorEntryPrice a i j :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => original_primal_entry_bound phi i j
    _ = ∑ a : ScalarBasisIndex, ∑ i : OneParticleIndex, ∑ j : OneParticleIndex,
        ‖phi‖ * tensorEntryPrice a i j := by
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by simp only [sourceTensorPrice, Finset.mul_sum]

theorem original_full_matrix_l1 (phi : Scalar) :
    (∑ i : Mode, ∑ j : Mode, ‖GaussYukawaCoefficient.fullMatrix phi i j‖) =
      2 * (∑ i : OneParticleIndex, ∑ j : OneParticleIndex, ‖GaussYukawaCoefficient.primal phi i j‖) := by
  have source : GaussYukawaCoefficient.fullMatrix phi =
      SourceRealScalarFock.branches (GaussYukawaCoefficient.primal phi) := rfl
  rw [source]
  simp [SourceRealScalarFock.branches, Fintype.sum_sum_type, Matrix.fromBlocks, two_mul]

theorem finite_quantized_operator_price {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) :
    ‖(quantizedFiber A).toContinuousLinearMap‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound ((quantizedFiber A).toContinuousLinearMap)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)
  intro psi
  exact SourceCARBound.quantized_norm_le_sum A psi

theorem original_sourceMap_point_price (phi : Scalar) :
    ‖GaussYukawaCoefficient.sourceMap phi‖ ≤ 2 * sourceTensorPrice * ‖phi‖ := by
  have matrixPrice : ‖GaussYukawaCoefficient.sourceMap phi‖ ≤
      ∑ i : Mode, ∑ j : Mode, ‖GaussYukawaCoefficient.fullMatrix phi i j‖ := by
    have source : GaussYukawaCoefficient.sourceMap phi =
        (quantizedFiber (GaussYukawaCoefficient.fullMatrix phi)).toContinuousLinearMap := rfl
    rw [source]
    exact finite_quantized_operator_price _
  rw [original_full_matrix_l1] at matrixPrice
  exact matrixPrice.trans ((mul_le_mul_of_nonneg_left (original_primal_l1_bound phi)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

theorem original_sourceMap_finite_price :
    ‖GaussYukawaCoefficient.sourceMap‖ ≤ 2 * sourceTensorPrice :=
  ContinuousLinearMap.opNorm_le_bound GaussYukawaCoefficient.sourceMap
    (mul_nonneg (by norm_num) sourceTensorPrice_nonnegative) original_sourceMap_point_price

theorem original_fullY_B_finite_price : GaussYukawaCoefficient.bound ≤ 12 * sourceTensorPrice := by
  unfold GaussYukawaCoefficient.bound
  calc
    _ ≤ (2 * sourceTensorPrice) * (4 + 2) := mul_le_mul original_sourceMap_finite_price
      (add_le_add original_vacuum_norm_bound (le_refl (2 : ℝ))) (by positivity)
      (mul_nonneg (by norm_num) sourceTensorPrice_nonnegative)
    _ = _ := by ring

theorem actual_fullY_finite_coefficient_binary_error (epsilon : ℝ) (precision : 0 < epsilon) (bits : ℕ) :
    ‖actualFullY epsilon precision - FullYSourceCutoffVolterra.cutoff (916 * bits)
      (actualPrepared epsilon precision)‖ ≤ 10992 * sourceTensorPrice * (1 / 2 : ℝ) ^ bits := by
  calc
    _ ≤ 916 * GaussYukawaCoefficient.bound * (1 / 2 : ℝ) ^ bits :=
      actualFullY_binary_error epsilon precision bits
    _ ≤ 916 * (12 * sourceTensorPrice) * (1 / 2 : ℝ) ^ bits :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left original_fullY_B_finite_price
        (by norm_num)) (pow_nonneg (by norm_num) _)
    _ = _ := by ring

end LowEnergy.ActualSourceFiniteYukawaPriceOwn
