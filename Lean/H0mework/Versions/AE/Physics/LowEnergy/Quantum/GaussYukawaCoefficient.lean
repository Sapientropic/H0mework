import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussGradedRetarded

/-! The original full independent-dual Yukawa map, normalized by its source radius. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussYukawaCoefficient
open SaturationMonoid.PhysicsCore
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open DiracExteriorMatterAction StageNineDiracDualFormNativeConjugateMatterVariation
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussNativePotential
open GaussHistoryHilbert SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

def primal : Scalar →ₗ[ℂ] Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ where
  toFun phi := LowEnergy.Quantum.operatorMatrix
    (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi))
  map_add' phi psi := by
    simp only [map_add, LowEnergy.FullQuantum.yukawaHamiltonian,
      diracDualRightChiralYukawaAction_add, LinearMap.comp_add, smul_add]
  map_smul' c phi := by
    simp only [map_smul, LowEnergy.FullQuantum.yukawaHamiltonian,
      diracDualRightChiralYukawaAction_smul, LinearMap.comp_smul, smul_smul, mul_comm, RingHom.id_apply]

private def branchesReal {ι : Type*} : Matrix ι ι ℂ →ₗ[ℝ] Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ where
  toFun A := Matrix.fromBlocks A 0 0 (-(A.map star))
  map_add' A B := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.map_apply, add_comm]
  map_smul' c A := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.map_apply]

def fullMatrix : Scalar →ₗ[ℝ] Matrix Mode Mode ℂ := branchesReal.comp (primal.restrictScalars ℝ)

def sourceLinear : Scalar →ₗ[ℝ] FockFiber →L[ℂ] FockFiber :=
  (quantizer.restrictScalars ℝ).comp fullMatrix

def sourceMap : Scalar →L[ℝ] FockFiber →L[ℂ] FockFiber := sourceLinear.toContinuousLinearMap

theorem source_map_return (phi : Scalar) : sourceMap phi = quantized
    (SourceRealScalarFock.branches (LowEnergy.Quantum.operatorMatrix
      (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi)))) := rfl

def radius (z : SourceCoordinateSlice) : ℝ := Real.sqrt (1 + ‖(z.2.1 : Scalar)‖^2/4)

theorem radius_pos (z : SourceCoordinateSlice) : 0 < radius z := by unfold radius; positivity

theorem radius_smooth : ContDiff ℝ ∞ radius := by
  apply ContDiff.sqrt
  · exact contDiff_const.add
      ((scalarSlice.subtypeL.contDiff.comp (contDiff_fst.comp contDiff_snd)).norm_sq ℝ |>.div_const 4)
  · intro z; positivity

theorem scalar_bound (z : SourceCoordinateSlice) :
    ‖scalarField z‖ ≤ (‖vacuum‖+2)*radius z := by
  have hr := Real.sq_sqrt (show 0 ≤ 1+‖(z.2.1 : Scalar)‖^2/4 by positivity)
  change (radius z)^2 = _ at hr
  have hpos := radius_pos z
  have h1 : 1 ≤ radius z := by nlinarith [sq_nonneg ‖(z.2.1 : Scalar)‖]
  have hx : ‖(z.2.1 : Scalar)‖ ≤ 2*radius z := by nlinarith [norm_nonneg (z.2.1 : Scalar)]
  have hv := norm_add_le vacuum (z.2.1 : Scalar)
  change ‖vacuum+(z.2.1 : Scalar)‖ ≤ _
  nlinarith [norm_nonneg vacuum]

def normalizedScalar (z : SourceCoordinateSlice) : Scalar := (radius z)⁻¹ • scalarField z

theorem normalized_scalar_bound (z : SourceCoordinateSlice) : ‖normalizedScalar z‖ ≤ ‖vacuum‖+2 := by
  rw [normalizedScalar, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (radius_pos z)]
  exact (inv_mul_le_iff₀ (radius_pos z)).mpr (by simpa only [mul_comm] using scalar_bound z)

theorem normalized_scalar_smooth : ContDiff ℝ ∞ normalizedScalar :=
  (radius_smooth.inv (fun z => (radius_pos z).ne')).smul scalarField_smooth

def normalized (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber := sourceMap (normalizedScalar z)
def bound : ℝ := ‖sourceMap‖*(‖vacuum‖+2)

theorem normalized_smooth : ContDiff ℝ ∞ normalized := sourceMap.contDiff.comp normalized_scalar_smooth

theorem normalized_bound (z : SourceCoordinateSlice) (f : FockFiber) : ‖normalized z f‖ ≤ bound*‖f‖ := by
  have hM : ‖normalized z‖ ≤ bound :=
    (sourceMap.le_opNorm (normalizedScalar z)).trans
      (mul_le_mul_of_nonneg_left (normalized_scalar_bound z) (norm_nonneg sourceMap))
  exact ((normalized z).le_opNorm f).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg f))

theorem radius_return (z : SourceCoordinateSlice) : (radius z) • normalized z = sourceMap (scalarField z) := by
  change (radius z) • sourceMap ((radius z)⁻¹ • scalarField z) = _
  rw [← map_smul, smul_smul, mul_inv_cancel₀ (radius_pos z).ne', one_smul]

theorem normalized_commutes (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (normalized z) := by
  change Commute _ (sourceMap (normalizedScalar z))
  rw [source_map_return]
  exact weight_commute w _

theorem bound_nonneg : 0 ≤ bound := by unfold bound; positivity

def action : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier normalized (fun _ => normalized_smooth.contDiffAt)

#print axioms source_map_return
#print axioms normalized_bound
#print axioms radius_return
end LowEnergy.GaussYukawaCoefficient
