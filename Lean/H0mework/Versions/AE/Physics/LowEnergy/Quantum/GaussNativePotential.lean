import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussNativeEnergy
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceQuantumGaugeCenterMagnetic
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCartanCubic

/-! The scalar and magnetic potential from the same source form action. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussNativePotential
open GaussNativeEnergy GaussHistoryHilbert SourceQuantumScalarChart
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumGaugeCenterMagnetic
open SaturationMonoid.PhysicsCore StageNineHolonomicField
open StageNineP286GaugeConnectionVariationDensity
open scoped ContDiff RealInnerProductSpace Matrix

def scalarField (z : SourceCoordinateSlice) : Scalar := vacuum + (z.2.1 : Scalar)
def connectionField (z : SourceCoordinateSlice) (i : Fin 3) : NativeLie :=
  SourceCartanCubic.gaugeCoordinate i (z.2.2 : Gauge)

def scalarGradient (z : SourceCoordinateSlice) (i : Fin 3) : Scalar :=
  scalarP286ActionBilinear (connectionField z i) (scalarField z)

def magneticField (z : SourceCoordinateSlice) (i : Fin 3) : NativeLie :=
  magneticOfConnection (connectionField z) i

theorem scalarField_smooth : ContDiff ℝ ∞ scalarField := by
  exact contDiff_const.add (scalarSlice.subtypeL.contDiff.comp (contDiff_fst.comp contDiff_snd))

theorem connectionField_smooth (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : SourceCoordinateSlice => connectionField z i) := by
  exact (SourceCartanCubic.gaugeCoordinate i).toContinuousLinearMap.contDiff.comp
    (coordinateSlice.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd))

theorem scalarGradient_smooth (i : Fin 3) :
    ContDiff ℝ ∞ (fun z => scalarGradient z i) := by
  let B0 : NativeLie →ₗ[ℝ] Scalar →ₗ[ℝ] Scalar := scalarP286ActionBilinear
  let B : NativeLie →L[ℝ] Scalar →L[ℝ] Scalar := B0.toContinuousBilinearMap
  have hB : ContDiff ℝ ∞ B :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := NativeLie) (F := Scalar →L[ℝ] Scalar) B
  exact (hB.comp (connectionField_smooth i)).clm_apply scalarField_smooth

theorem magneticField_smooth (i : Fin 3) :
    ContDiff ℝ ∞ (fun z => magneticField z i) := by
  let B : NativeLie →L[ℝ] NativeLie →L[ℝ] NativeLie :=
    SourceCartanCubic.nativeBracket.toContinuousBilinearMap
  have hB : ContDiff ℝ ∞ B :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := NativeLie) (F := NativeLie →L[ℝ] NativeLie) B
  have h (j k : Fin 3) : ContDiff ℝ ∞
      (fun z : SourceCoordinateSlice => B (connectionField z j) (connectionField z k)) :=
    (hB.comp (connectionField_smooth j)).clm_apply (connectionField_smooth k)
  fin_cases i
  · exact h 1 2
  · exact h 2 0
  · exact h 0 1

def scalarPotential (z : SourceCoordinateSlice) : ℝ :=
  sourceTime 0*volume z*⟪(z.2.1 : Scalar), (z.2.1 : Scalar)⟫ -
    sourceTime 0*volume z/2 * ∑ i : Fin 3, ∑ j : Fin 3,
      inverseSpatial z i j * ⟪scalarGradient z i, scalarGradient z j⟫

def magneticPotential (z : SourceCoordinateSlice) : ℝ :=
  volume z/(2*sourceSigma*sourceTime 0) * ∑ i : Fin 3, ∑ j : Fin 3,
    inverseSpatial z i j * ⟪magneticField z i, magneticField z j⟫

def potential (z : SourceCoordinateSlice) : ℝ := scalarPotential z + magneticPotential z

def originalScalarPotential (z : SourceCoordinateSlice) : ℝ :=
  (coframe sourceTime z.1).det * ⟪scalarField z-vacuum,scalarField z-vacuum⟫ -
    (1/2 : ℝ)*∑ i : Fin 3, ∑ j : Fin 3,
      scalarMetric z (Fin.succ i) (Fin.succ j) * ⟪scalarGradient z i,scalarGradient z j⟫

def originalMagneticPotential (z : SourceCoordinateSlice) : ℝ :=
  -(1/2 : ℝ)*∑ i : Fin 3, ∑ j : Fin 3,
    sourceBFKernel sourceTime z.1 (Fin.natAdd 3 i) (Fin.natAdd 3 j) *
      ⟪magneticField z i,magneticField z j⟫

theorem scalar_potential_source (z : physicalChart) :
    originalScalarPotential z.val = scalarPotential z.val := by
  simp only [originalScalarPotential, coframe_determinant, source_scalar_spatial,
    scalarField, add_sub_cancel_left, scalarPotential, volume]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem magnetic_potential_source (z : physicalChart) :
    originalMagneticPotential z.val = magneticPotential z.val := by
  simp only [originalMagneticPotential, source_magnetic_kernel, magneticPotential, mul_assoc,
    ← Finset.mul_sum]
  ring

theorem inverseSpatial_smooth (i j : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => inverseSpatial w i j) z.val := by
  simp only [inverseSpatial, Matrix.mul_apply, Matrix.transpose_apply]
  exact ContDiffAt.sum (fun k _ => (triadInverse_smooth i k z).mul (triadInverse_smooth j k z))

theorem potential_smooth (z : physicalChart) : ContDiffAt ℝ ∞ potential z.val := by
  have hscalar := fun (i j : Fin 3) =>
    (inverseSpatial_smooth i j z).mul
      ((scalarGradient_smooth i).contDiffAt.inner ℝ (scalarGradient_smooth j).contDiffAt)
  have hmagnetic := fun (i j : Fin 3) =>
    (inverseSpatial_smooth i j z).mul
      ((magneticField_smooth i).contDiffAt.inner ℝ (magneticField_smooth j).contDiffAt)
  have hs : ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => ⟪(w.2.1 : Scalar),(w.2.1 : Scalar)⟫) z.val := by
    have hv := scalarSlice.subtypeL.contDiff.comp
      (contDiff_fst.comp (contDiff_snd : ContDiff ℝ ∞
        (Prod.snd : SourceCoordinateSlice → scalarSlice × coordinateSlice)))
    exact hv.contDiffAt.inner ℝ hv.contDiffAt
  exact ((contDiffAt_const.mul volume_smooth.contDiffAt).mul hs |>.sub
    (((contDiffAt_const.mul volume_smooth.contDiffAt).div_const 2).mul
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => hscalar i j))).add
    ((volume_smooth.contDiffAt.div_const _).mul
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => hmagnetic i j))

#print axioms scalar_potential_source
#print axioms magnetic_potential_source
#print axioms potential_smooth
end LowEnergy.GaussNativePotential
