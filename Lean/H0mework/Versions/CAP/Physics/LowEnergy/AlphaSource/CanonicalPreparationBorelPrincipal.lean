import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrincipalFactor
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationNativeCutoff
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSquareCutoff

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationActualFactor
open GaussHistoryHilbert SourceQuantumGaugeSliceCoordinates
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationScalarCoordinates
open scoped BigOperators ContDiff

-- Fin 100 is the original lex70/R61/rawGauge33 chart, not a selected basis.
def flatCovectorLinear (p : PhysicalMomentum) : FlatConfiguration →ₗ[ℝ] ℝ where
  toFun x := ∑ i : Fin 100, p i*x i
  map_add' x y := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

def flatCovector (p : PhysicalMomentum) : FlatConfiguration →L[ℝ] ℝ :=
  (flatCovectorLinear p).toContinuousLinearMap

def nativeCovector (p : PhysicalMomentum) : Cotangent :=
  (flatCovector p).comp fullCoordinates.toContinuousLinearMap

theorem nativeCovector_apply (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    nativeCovector p z = ∑ i : Fin 100, p i*fullCoordinates z i := rfl

def nativeCovectorLinear : PhysicalMomentum →ₗ[ℝ] Cotangent where
  toFun := nativeCovector
  map_add' p q := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [nativeCovector_apply,PiLp.add_apply,add_apply,
      add_mul,Finset.sum_add_distrib]
  map_smul' r p := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [nativeCovector_apply,PiLp.smul_apply,smul_apply,smul_eq_mul,Finset.mul_sum,
      RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

def nativeCovectorMap : PhysicalMomentum →L[ℝ] Cotangent :=
  nativeCovectorLinear.toContinuousLinearMap

def nativePhase (zp : FlatConfiguration × PhysicalMomentum) : SourceCoordinateSlice × Cotangent :=
  (fullCoordinates.symm zp.1,nativeCovector zp.2)

theorem nativePhase_smooth : ContDiff ℝ ∞ nativePhase := by
  have smooth : ContDiff ℝ ∞ (fun p : PhysicalMomentum => nativeCovectorMap p) := by
    simpa using! ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := PhysicalMomentum)
      (F := Cotangent) (n := ∞) nativeCovectorMap
  exact (fullCoordinates.symm.contDiff.comp contDiff_fst).prodMk
    (smooth.comp contDiff_snd)

def b1 (zp : FlatConfiguration × PhysicalMomentum) : ℝ :=
  factorWeight zp*principalFactor (nativePhase zp).1 (nativePhase zp).2

theorem b1_literal (zp : FlatConfiguration × PhysicalMomentum) :
    b1 zp = Real.sqrt (sourceTheta zp.1 (normalizedMomentum zp.2))*
      Real.sqrt (sourceChi (2*‖zp.2‖))*
        Real.sqrt (T (fullCoordinates.symm zp.1) (nativeCovector zp.2) /
          Real.sqrt (T (fullCoordinates.symm zp.1) (nativeCovector zp.2) /
            (2*A (fullCoordinates.symm zp.1) (nativeCovector zp.2)))) := by
  simp only [b1,factorWeight,sourceThetaRoot_literal,radialRoot,
    principalFactor,h2,C,nativePhase]

theorem b1_square (zp : FlatConfiguration × PhysicalMomentum)
    (cone : nativePhase zp ∈ positiveCone) :
    b1 zp^2 = sourceTheta zp.1 (normalizedMomentum zp.2)*sourceChi (2*‖zp.2‖)*
      h2 (fullCoordinates.symm zp.1) (nativeCovector zp.2) := by
  rw [b1,mul_pow,factorWeight_square,principalFactor_square cone]
  rfl

theorem b1_smooth_at (zp : FlatConfiguration × PhysicalMomentum)
    (cone : nativePhase zp ∈ positiveCone) : ContDiffAt ℝ ∞ b1 zp :=
  factorWeight_smooth.contDiffAt.mul
    ((principalFactor_smooth (nativePhase zp) cone).comp zp nativePhase_smooth.contDiffAt)

theorem b1_zero_low (zp : FlatConfiguration × PhysicalMomentum) (low : ‖zp.2‖ ≤ 1/2) :
    b1 zp=0 := by
  rw [b1,factorWeight_zero low,zero_mul]

theorem actual_source_native_phase :
    nativePhase (fullCoordinates GaussHistoryHilbert.sourcePoint.val,sourceMomentum) =
      (GaussHistoryHilbert.sourcePoint.val,nativeCovector sourceMomentum) := by
  simp only [nativePhase,ContinuousLinearEquiv.symm_apply_apply]

theorem b1_actual_source_cutoff :
    b1 (flatSource,sourceMomentum) =
      principalFactor (fullCoordinates.symm flatSource) (nativeCovector sourceMomentum) := by
  rw [b1,factorWeight_at_source,one_mul]
  rfl

theorem source_flat_center : fullCoordinates GaussHistoryHilbert.sourcePoint.val=flatSource :=
  actual_flat_source

theorem b1_actual_source : b1 (flatSource,sourceMomentum) =
    principalFactor GaussHistoryHilbert.sourcePoint.val (nativeCovector sourceMomentum) := by
  rw [b1_actual_source_cutoff,←source_flat_center,fullCoordinates.symm_apply_apply]

theorem normalized_native_covector (p : PhysicalMomentum) :
    nativeCovector ((‖p‖⁻¹ : ℝ) • p)=‖p‖⁻¹ • nativeCovector p :=
  nativeCovectorLinear.map_smul _ _

theorem b1_radial_readback (zp : FlatConfiguration × PhysicalMomentum) (nonzero : zp.2 ≠ 0) :
    b1 zp = factorWeight zp*‖zp.2‖*
      principalFactor (fullCoordinates.symm zp.1)
        (nativeCovector ((‖zp.2‖⁻¹ : ℝ) • zp.2)) := by
  rw [normalized_native_covector]
  have scale := principalFactor_order_one (fullCoordinates.symm zp.1)
    (nativeCovector ((‖zp.2‖⁻¹ : ℝ) • zp.2)) ‖zp.2‖ (norm_pos_iff.mpr nonzero)
  rw [normalized_native_covector,smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr nonzero),one_smul] at scale
  rw [b1,nativePhase,scale]
  ring

end LowEnergy.PreparationActualFactor
