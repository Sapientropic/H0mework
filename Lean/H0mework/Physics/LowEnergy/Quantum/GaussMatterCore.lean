import H0mework.Physics.LowEnergy.Quantum.GaussCoframeSpin

/-! The original zero-shift Dirac spatial matter action, retaining the independent dual. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussMatterCore
open SaturationMonoid.PhysicsCore
open DiracCliffordRepresentation DiracExteriorMatterAction StageNineHolonomicField
open SU7MotherLieAlgebra
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open GaussNativeEnergy GaussNativePotential GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussFockPair
open GaussNativeMatter GaussQuantumMultiplier
open scoped ContDiff Matrix
local instance : DecidableEq Mode := Classical.decEq _

theorem spin_native_commute (S : DiracMatrix) (a : NativeLie) :
    GaussCoframeSpin.spinLift S * nativePrimal a = nativePrimal a * GaussCoframeSpin.spinLift S := by
  rw [← GaussCoframeSpin.spinLift_source]
  change LowEnergy.Quantum.operatorMatrix (diracMatrixMatterAction S) *
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a))) =
    LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a))) *
      LowEnergy.Quantum.operatorMatrix (diracMatrixMatterAction S)
  rw [← LowEnergy.Quantum.matrix_composition, ← LowEnergy.Quantum.matrix_composition]
  exact congrArg LowEnergy.Quantum.operatorMatrix (diracMatrixMatterAction_commutes_internal S _)

theorem boost_native_commute (b : Fin 3) (a : NativeLie) :
    GaussCoframeSpin.full (Fin.castAdd 4 b) * nativeFull a =
      nativeFull a * GaussCoframeSpin.full (Fin.castAdd 4 b) := by
  have hb : (Fin.castAdd 4 b).val < 3 := b.isLt
  have hp := spin_native_commute (GaussCoframeSpin.sourceSpin (Fin.castAdd 4 b)) a
  let B := GaussCoframeSpin.primal (Fin.castAdd 4 b)
  let R := nativePrimal a
  have hB : GaussCoframeSpin.full (Fin.castAdd 4 b) =
      Matrix.fromBlocks B 0 0 (B.map (starRingEnd ℂ)) := by
    simp only [GaussCoframeSpin.full, hb, if_true]
    rfl
  change GaussCoframeSpin.full (Fin.castAdd 4 b) *
      Matrix.fromBlocks R 0 0 (R.map (starRingEnd ℂ)) =
    Matrix.fromBlocks R 0 0 (R.map (starRingEnd ℂ)) * GaussCoframeSpin.full (Fin.castAdd 4 b)
  rw [hB, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  have hd : B.map (starRingEnd ℂ) * R.map (starRingEnd ℂ) =
      R.map (starRingEnd ℂ) * B.map (starRingEnd ℂ) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ =>
      M.map (starRingEnd ℂ)) hp
  exact congrArg₂ (fun X Y : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ =>
    Matrix.fromBlocks X 0 0 Y) hp hd

def matrixTerm (b : Fin 3) : NativeLie →ₗ[ℝ] Matrix Mode Mode ℂ :=
  (LinearMap.mulLeft ℝ (Complex.I • GaussCoframeSpin.full (Fin.castAdd 4 b))).comp nativeFull

theorem matrixTerm_hermitian (b : Fin 3) (a : NativeLie) :
    (matrixTerm b a).conjTranspose = matrixTerm b a := by
  change ((Complex.I • GaussCoframeSpin.full (Fin.castAdd 4 b)) * nativeFull a).conjTranspose =
    (Complex.I • GaussCoframeSpin.full (Fin.castAdd 4 b)) * nativeFull a
  simp only [Matrix.smul_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    nativeFull_skew, GaussCoframeSpin.full_hermitian, Complex.star_def, Complex.conj_I,
    Matrix.neg_mul, neg_smul, smul_neg, neg_neg]
  rw [boost_native_commute]

def quantumTerm (b : Fin 3) : NativeLie →ₗ[ℝ] SourceQuantumFockGauge.FockFiber →L[ℂ] SourceQuantumFockGauge.FockFiber :=
  (quantizer.restrictScalars ℝ).comp (matrixTerm b)

def coefficient (i b : Fin 3) (z : SourceCoordinateSlice) : ℝ :=
  2*sourceTime 0*triadInverse z.1 i b

theorem coefficient_smooth (i b : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (coefficient i b) z.val := contDiffAt_const.mul (triadInverse_smooth i b z)

def localMatrix (i b : Fin 3) (z : SourceCoordinateSlice) : Matrix Mode Mode ℂ :=
  (coefficient i b z : ℂ) • matrixTerm b (connectionField z i)

theorem local_hermitian (i b : Fin 3) (z : SourceCoordinateSlice) :
    (localMatrix i b z).conjTranspose = localMatrix i b z := by
  rw [localMatrix, Matrix.conjTranspose_smul, matrixTerm_hermitian]
  simp

theorem local_smooth (i b : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => quantized (localMatrix i b w)) z.val := by
  have hq := (quantumTerm b).toContinuousLinearMap.contDiff.contDiffAt.comp z.val
    (connectionField_smooth i).contDiffAt
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (coefficient_smooth i b z)
  have h := hc.smul hq
  convert h using 1
  funext w
  exact map_smul quantizer _ _

def matterAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  ∑ i : Fin 3, ∑ b : Fin 3, action (localMatrix i b) (local_smooth i b)

theorem matter_pair (f g : QuantumTest) : sourcePair f (matterAction g) = sourcePair (matterAction f) g := by
  simp only [matterAction, LinearMap.sum_apply, sourcePair, map_sum, inner_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  exact action_pair _ _ (local_hermitian i b) f g

#print axioms spin_native_commute
#print axioms matrixTerm_hermitian
#print axioms matter_pair
end LowEnergy.GaussMatterCore
