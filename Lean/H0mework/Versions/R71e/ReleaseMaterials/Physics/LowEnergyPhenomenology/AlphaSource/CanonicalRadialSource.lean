import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPhysicalForce
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussFullHamiltonian

/-! The actual SpinPair radial connection inside the original Gauss100 core.
This is a restriction of the existing field coordinates, not a reducing
quantum sector or a new preparation. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualRadial
open SaturationMonoid.PhysicsCore
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussLiveMomentum GaussCoreDifferential
open GaussNativePotential GaussNativeEnergy GaussCoreHilbert GaussFockPair
open scoped ContDiff Topology RealInnerProductSpace

def sourceG : ℝ := gaugeScale/2
theorem sourceG_pos : 0 < sourceG := half_pos gaugeScale_pos

def axis : coordinateSlice := sourceG⁻¹ •
  (⟨SourceQuantumConfigurationHilbert.sourceGauge, sourceGauge_mem_coordinateSlice⟩ : coordinateSlice)
def sliceDirection : Slice := (0, axis)
def ambientDirection : Ambient := sliceMap sliceDirection
def shift : SourceCoordinateSlice := (0, sliceDirection)

def B (i : Fin 3) : NativeLie := SourceCartanCubic.gaugeCoordinate i (axis : Gauge)

theorem B_original (i : Fin 3) :
    B i = (2 : ℝ) • SourceQuantumResidualGaugeSlice.colorGenerator i := by
  change SourceQuantumResidualGaugeSlice.gaugeCoordinates
    (sourceG⁻¹ • SourceQuantumResidualGaugeSlice.sourceGauge) i = _
  rw [map_smul]
  change sourceG⁻¹ • SourceQuantumResidualGaugeSlice.gaugeCoordinates
    SourceQuantumResidualGaugeSlice.sourceGauge i = _
  rw [SourceQuantumResidualGaugeSlice.sourceGauge_apply, smul_smul]
  congr 1
  unfold sourceG
  field_simp [gaugeScale_pos.ne']

private def nativeComponent (j : Fin 8) : NativeLie →ₗ[ℝ] ℝ :=
  ((LinearMap.proj j).comp (LinearMap.fst ℝ (Fin 8 → ℝ) ((Fin 3 → ℝ) × ℝ))).comp
    SourceQuantumNativeDimensions.nativeCoordinates.toLinearMap

def gaugeRead : Gauge →ₗ[ℝ] ℝ := (1/3 : ℝ) •
  ((nativeComponent 1).comp (SourceCartanCubic.gaugeCoordinate 0) +
   (nativeComponent 0).comp (SourceCartanCubic.gaugeCoordinate 1) +
   (nativeComponent 6).comp (SourceCartanCubic.gaugeCoordinate 2))

def gLinear : SourceCoordinateSlice →ₗ[ℝ] ℝ :=
  gaugeRead.comp (coordinateSlice.subtype.comp
    ((LinearMap.snd ℝ scalarSlice coordinateSlice).comp
      (LinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice))))
def g : SourceCoordinateSlice → ℝ := gLinear

theorem g_smooth : ContDiff ℝ ∞ g := gLinear.toContinuousLinearMap.contDiff

theorem gaugeRead_axis : gaugeRead (axis : Gauge) = 1 := by
  change (1/3 : ℝ) *
    ((SourceQuantumNativeDimensions.nativeCoordinates (B 0)).1 1 +
     (SourceQuantumNativeDimensions.nativeCoordinates (B 1)).1 0 +
     (SourceQuantumNativeDimensions.nativeCoordinates (B 2)).1 6) = 1
  simp only [B_original, map_smul]
  norm_num [SourceQuantumResidualGaugeSlice.colorGenerator_coordinates, Matrix.cons_val_two]
  change (1/3 : ℝ)*(2+1)=1
  norm_num

theorem g_shift : g shift = 1 := gaugeRead_axis

theorem g_source : g (sourceCoframe, (0,
    (⟨SourceQuantumConfigurationHilbert.sourceGauge, sourceGauge_mem_coordinateSlice⟩ : coordinateSlice))) =
    sourceG := by
  have h := gaugeRead_axis
  change gaugeRead (sourceG⁻¹ • SourceQuantumConfigurationHilbert.sourceGauge) = 1 at h
  rw [map_smul] at h
  change sourceG⁻¹ * gaugeRead SourceQuantumConfigurationHilbert.sourceGauge = 1 at h
  change gaugeRead SourceQuantumConfigurationHilbert.sourceGauge = sourceG
  field_simp [sourceG_pos.ne'] at h
  exact h

def translate (z : SourceCoordinateSlice) (r : ℝ) : SourceCoordinateSlice := z+r • shift

@[simp] theorem translate_coframe (z : SourceCoordinateSlice) (r : ℝ) :
    (translate z r).1=z.1 := by simp [translate, shift]
@[simp] theorem translate_scalar (z : SourceCoordinateSlice) (r : ℝ) :
    (translate z r).2.1=z.2.1 := by simp [translate, shift, sliceDirection]

theorem g_translate (z : SourceCoordinateSlice) (r : ℝ) : g (translate z r)=g z+r := by
  change gLinear (z+r • shift) = _
  rw [map_add, map_smul]
  change g z+r*g shift=g z+r
  rw [g_shift, mul_one]

theorem connection_translate (z : SourceCoordinateSlice) (r : ℝ) (i : Fin 3) :
    connectionField (translate z r) i = connectionField z i+r • B i := by
  change SourceCartanCubic.gaugeCoordinate i ((z.2.2 : Gauge)+r • (axis : Gauge)) = _
  rw [map_add, map_smul]
  rfl

theorem translate_derivative (z : SourceCoordinateSlice) :
    HasDerivAt (translate z) shift 0 := by
  simpa only [one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const shift).const_add z

def Q : QuantumTest →ₗ[ℂ] QuantumTest := GaussNativeForm.multiply g (fun _ => g_smooth.contDiffAt)
def P : QuantumTest →ₗ[ℂ] QuantumTest := covariantMomentum ambientDirection
def Psharp : QuantumTest →ₗ[ℂ] QuantumTest := GaussMomentumAdjoint.adjoint ambientDirection

theorem P_original (z : physicalChart) (f : QuantumTest) :
    P f z.val=(-Complex.I) • fderiv ℝ f z.val shift :=
  covariantMomentum_slice z sliceDirection f

theorem P_pair (f h : QuantumTest) : sourcePair f (P h)=sourcePair (Psharp f) h :=
  GaussMomentumAdjoint.momentum_pair ambientDirection f h

theorem Q_original (f : QuantumTest) (z : SourceCoordinateSlice) : Q f z=(g z : ℂ) • f z := rfl

def scalarSlope (z : SourceCoordinateSlice) (i : Fin 3) : Scalar :=
  StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (B i) (scalarField z)

theorem scalarGradient_translate (z : SourceCoordinateSlice) (r : ℝ) (i : Fin 3) :
    scalarGradient (translate z r) i=scalarGradient z i+r • scalarSlope z i := by
  simp only [scalarGradient, scalarField, scalarSlope, translate_scalar, connection_translate,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_add]
  abel

def curvatureSlope (z : SourceCoordinateSlice) : Fin 3 → NativeLie :=
  ![SourceCartanCubic.nativeBracket (B 1) (connectionField z 2)+
      SourceCartanCubic.nativeBracket (connectionField z 1) (B 2),
    SourceCartanCubic.nativeBracket (B 2) (connectionField z 0)+
      SourceCartanCubic.nativeBracket (connectionField z 2) (B 0),
    SourceCartanCubic.nativeBracket (B 0) (connectionField z 1)+
      SourceCartanCubic.nativeBracket (connectionField z 0) (B 1)]

def curvatureAxis : Fin 3 → NativeLie :=
  ![SourceCartanCubic.nativeBracket (B 1) (B 2),
    SourceCartanCubic.nativeBracket (B 2) (B 0),
    SourceCartanCubic.nativeBracket (B 0) (B 1)]

private theorem bracket_translate (a b u v : NativeLie) (r : ℝ) :
    SourceCartanCubic.nativeBracket (a+r • u) (b+r • v)=
      SourceCartanCubic.nativeBracket a b+
      r • (SourceCartanCubic.nativeBracket u b+SourceCartanCubic.nativeBracket a v)+
      r^2 • SourceCartanCubic.nativeBracket u v := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_add, smul_smul, pow_two]
  abel

theorem magneticField_translate (z : SourceCoordinateSlice) (r : ℝ) (i : Fin 3) :
    magneticField (translate z r) i=magneticField z i+r • curvatureSlope z i+r^2 • curvatureAxis i := by
  simp only [magneticField, SourceQuantumGaugeCenterMagnetic.magneticOfConnection,
    curvatureSlope, curvatureAxis, connection_translate]
  fin_cases i
  all_goals exact bracket_translate _ _ _ _ r

theorem scalarGradient_derivative (z : SourceCoordinateSlice) (i : Fin 3) :
    HasDerivAt (fun r : ℝ => scalarGradient (translate z r) i) (scalarSlope z i) 0 := by
  simp only [scalarGradient_translate]
  simpa only [one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const (scalarSlope z i)).const_add _

theorem magneticField_derivative (z : SourceCoordinateSlice) (i : Fin 3) :
    HasDerivAt (fun r : ℝ => magneticField (translate z r) i) (curvatureSlope z i) 0 := by
  simp only [magneticField_translate]
  simpa only [id_eq, Pi.pow_apply, Nat.reduceSub, one_smul, Nat.cast_ofNat, pow_one,
    mul_zero, mul_one, zero_smul, add_zero, Pi.add_apply] using!
    ((((hasDerivAt_id (0 : ℝ)).smul_const (curvatureSlope z i)).const_add
      (magneticField z i)).add (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (curvatureAxis i)))

def scalarSlopePotential (z : SourceCoordinateSlice) : ℝ :=
  -(sourceTime 0*volume z/2)*∑ i : Fin 3, ∑ j : Fin 3,
    inverseSpatial z i j *
      (⟪scalarSlope z i, scalarGradient z j⟫+⟪scalarGradient z i, scalarSlope z j⟫)

def magneticSlopePotential (z : SourceCoordinateSlice) : ℝ :=
  volume z/(2*sourceSigma*sourceTime 0)*∑ i : Fin 3, ∑ j : Fin 3,
    inverseSpatial z i j *
      (⟪curvatureSlope z i, magneticField z j⟫+⟪magneticField z i, curvatureSlope z j⟫)

theorem scalarPotential_derivative (z : SourceCoordinateSlice) :
    HasDerivAt (fun r : ℝ => scalarPotential (translate z r)) (scalarSlopePotential z) 0 := by
  have h := (HasDerivAt.fun_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    HasDerivAt.fun_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      ((scalarGradient_derivative z i).inner ℝ (scalarGradient_derivative z j)).const_mul
        (inverseSpatial z i j)).const_mul (sourceTime 0*volume z/2)
  have out := (hasDerivAt_const (0 : ℝ)
    (sourceTime 0*volume z*⟪(z.2.1 : Scalar),(z.2.1 : Scalar)⟫)).sub h
  have shape : (fun r : ℝ => scalarPotential (translate z r)) =
      (fun _ : ℝ => sourceTime 0*volume z*⟪(z.2.1 : Scalar),(z.2.1 : Scalar)⟫) -
        (fun r => sourceTime 0*volume z/2*∑ i : Fin 3, ∑ j : Fin 3,
          inverseSpatial z i j * ⟪scalarGradient (translate z r) i,scalarGradient (translate z r) j⟫) := by
    funext r
    simp only [scalarPotential, volume, inverseSpatial, translate_coframe, translate_scalar, Pi.sub_apply]
  rw [← shape] at out
  apply out.congr_deriv
  simp only [scalarSlopePotential, translate, zero_smul, add_zero, zero_sub, neg_mul, add_comm]

theorem magneticPotential_derivative (z : SourceCoordinateSlice) :
    HasDerivAt (fun r : ℝ => magneticPotential (translate z r)) (magneticSlopePotential z) 0 := by
  have out := (HasDerivAt.fun_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    HasDerivAt.fun_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      ((magneticField_derivative z i).inner ℝ (magneticField_derivative z j)).const_mul
        (inverseSpatial z i j)).const_mul (volume z/(2*sourceSigma*sourceTime 0))
  have shape : (fun r : ℝ => magneticPotential (translate z r)) =
      fun r => volume z/(2*sourceSigma*sourceTime 0)*∑ i : Fin 3, ∑ j : Fin 3,
        inverseSpatial z i j * ⟪magneticField (translate z r) i,magneticField (translate z r) j⟫ := by
    funext r
    simp only [magneticPotential, volume, inverseSpatial, translate_coframe]
  rw [← shape] at out
  apply out.congr_deriv
  simp only [magneticSlopePotential, translate, zero_smul, add_zero, add_comm]

end LowEnergy.ActualRadial
