import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceBrokenBasis

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceMatrixInverse
open PreparationVacuumSourceChartBudget PreparationChartGuard PreparationPhaseScalar
open PreparationScalarCoordinates PreparationCoordinates SourceQuantumScalarChart SourceQuantumNativeDimensions
open SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice
open GaussLiveMomentum
open CanonicalPreparationCutoff
open scoped BigOperators Matrix RealInnerProductSpace

def brokenPart (a : NativeLie) : broken := broken.orthogonalProjectionOnto a

theorem brokenPart_residual (a : NativeLie) : a-(brokenPart a).val ∈ stabilizer := by
  have original := broken.sub_starProjection_mem_orthogonal a
  simpa only [brokenPart,Submodule.coe_orthogonalProjectionOnto_apply,broken,
    Submodule.orthogonal_orthogonal] using original

theorem affine_orbit_pairing_projection (sigma : scalarSlice) (a : NativeLie) (i : Fin 9) :
    inner ℝ (orbit (normalBuild (sourceNormal i))) (action (vacuum+(sigma : Scalar)) a)=
    inner ℝ (orbit (normalBuild (sourceNormal i)))
      (action (vacuum+(sigma : Scalar)) (brokenPart a).val) := by
  let residual : stabilizer := ⟨a-(brokenPart a).val,brokenPart_residual a⟩
  have orthogonal := (Submodule.mem_orthogonal _ _).mp (stabilizer_affine_action residual sigma)
    (orbit (normalBuild (sourceNormal i))) ⟨_,rfl⟩
  change inner ℝ (orbit (normalBuild (sourceNormal i)))
    (action (vacuum+(sigma : Scalar)) (a-(brokenPart a).val))=0 at orthogonal
  rw [map_sub,inner_sub_right,sub_eq_zero] at orthogonal
  exact orthogonal

def orbitPairing (xi : Scalar) : Fin 9 → ℝ :=
  fun i => inner ℝ (orbit (normalBuild (sourceNormal i))) xi

def ambientInverseLie (z : SourceCoordinateSlice) (xi : Scalar) (eta : Gauge) : NativeLie :=
  (inverseL z (xi,eta)).1

def ambientInverseScalar (z : SourceCoordinateSlice) (xi : Scalar) (eta : Gauge) : scalarSlice :=
  (inverseL z (xi,eta)).2.1

def ambientInverseGauge (z : SourceCoordinateSlice) (xi : Scalar) (eta : Gauge) : coordinateSlice :=
  (inverseL z (xi,eta)).2.2

theorem ambient_scalar_inverse_equation (z : GaussHistoryHilbert.physicalChart)
    (xi : Scalar) (eta : Gauge) :
    action (vacuum+(z.val.2.1 : Scalar)) (ambientInverseLie z.val xi eta)+
      (ambientInverseScalar z.val xi eta : Scalar)=xi :=
  congrArg Prod.fst (inverse_right z (xi,eta))

theorem ambient_gauge_inverse_equation (z : GaussHistoryHilbert.physicalChart)
    (xi : Scalar) (eta : Gauge) :
    nativeGauge (ambientInverseLie z.val xi eta) z.val.2.2.val+
      (ambientInverseGauge z.val xi eta : Gauge)=eta :=
  congrArg Prod.snd (inverse_right z (xi,eta))

def inverseBrokenCoordinates (z : GaussHistoryHilbert.physicalChart)
    (xi : Scalar) (eta : Gauge) : Fin 9 → ℝ :=
  fun i => brokenCoordinates (brokenPart (ambientInverseLie z.val xi eta)) i

theorem actual_D9_equation (z : GaussHistoryHilbert.physicalChart) (xi : Scalar) (eta : Gauge) :
    (sourceD9 (vacuum+(z.val.2.1 : Scalar))).mulVec
      (inverseBrokenCoordinates z xi eta)=orbitPairing xi := by
  ext i
  have equation := congrArg (fun v : Scalar => inner ℝ (orbit (normalBuild (sourceNormal i))) v)
    (ambient_scalar_inverse_equation z xi eta)
  have residual := (Submodule.mem_orthogonal _ _).mp (ambientInverseScalar z.val xi eta).property
    (orbit (normalBuild (sourceNormal i))) ⟨_,rfl⟩
  rw [inner_add_right,residual,add_zero] at equation
  calc
    _=inner ℝ (orbit (normalBuild (sourceNormal i)))
        (action (vacuum+(z.val.2.1 : Scalar)) (brokenPart (ambientInverseLie z.val xi eta)).val) :=
      (sourceD9_pair_coordinates _ _ i).symm
    _=inner ℝ (orbit (normalBuild (sourceNormal i)))
        (action (vacuum+(z.val.2.1 : Scalar)) (ambientInverseLie z.val xi eta)) :=
      (affine_orbit_pairing_projection _ _ i).symm
    _=orbitPairing xi i := equation

theorem actual_D9_inverse_coefficients (z : FlatConfiguration)
    (box : ∀ i,|z i-CanonicalPreparationCutoff.flatSource i| ≤ CanonicalPreparationCutoff.sourceRadius)
    (xi : Scalar) (eta : Gauge) :
    inverseBrokenCoordinates (phaseChart z box) xi eta=
      ((sourceD9 (vacuum+((fullCoordinates.symm z).2.1 : Scalar)))⁻¹).mulVec (orbitPairing xi) := by
  let D := sourceD9 (vacuum+((fullCoordinates.symm z).2.1 : Scalar))
  have positive : 0<D.det := by have guard := sourceD9_j15 z box; change (1/15 : ℝ)≤D.det at guard; linarith
  have regular : IsUnit D.det := isUnit_iff_ne_zero.mpr positive.ne'
  have equation := actual_D9_equation (phaseChart z box) xi eta
  change D.mulVec (inverseBrokenCoordinates (phaseChart z box) xi eta)=orbitPairing xi at equation
  rw [←equation,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ regular,Matrix.one_mulVec]

end LowEnergy.PreparationVacuumSourceMatrixInverse
