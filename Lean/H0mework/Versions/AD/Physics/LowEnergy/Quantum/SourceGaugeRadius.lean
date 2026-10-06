import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCornerWeight
import H0mework.Physics.GaugeStanding.GaugeBFAlgebra

/-! The original P286 metric makes the full gauge radius orthogonal to all twelve orbit rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceGaugeRadius
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineCoframeGravityGaugeRegularity
open StageNineP286GaugeAuxiliaryVariation StageNineP286LinkedActiveGaugeBFAlgebra
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumResidualGaugeSlice GaussLiveMomentum GaussHistoryHilbert
open GaussNativeEnergy GaussNativePotential SourceCornerWeight
open scoped ContDiff Topology RealInnerProductSpace
local instance : CompleteSpace NativeLie := FiniteDimensional.complete ℝ NativeLie
local instance : CompleteSpace Gauge := inferInstance

def nativeAdjoint (a : NativeLie) : NativeLie →ₗ[ℝ] NativeLie where
  toFun b := jointP286CoordinateLieBracket a b
  map_add' b c := jointP286CoordinateLieBracket_add_right b c a
  map_smul' r b := jointP286CoordinateLieBracket_smul_right r b a

theorem native_adjoint_skew (a b c : NativeLie) :
    ⟪nativeAdjoint a b,c⟫+⟪b,nativeAdjoint a c⟫=0 := by
  change p286CoordinateLiePairing (jointP286CoordinateLieBracket a b) c+
    p286CoordinateLiePairing b (jointP286CoordinateLieBracket a c)=0
  exact p286CoordinateLiePairing_adjoint_skew a b c

private theorem native_adjoint_self (a b : NativeLie) : ⟪b,nativeAdjoint a b⟫=0 := by
  have h := native_adjoint_skew a b b
  have hs := real_inner_comm (nativeAdjoint a b) b
  linarith

def gaugeRowMap (q : Coframe) (i : Fin 3) : Gauge →L[ℝ] NativeLie :=
  ∑ j : Fin 3, (triad q i j) • (SourceCartanCubic.gaugeCoordinate j).toContinuousLinearMap

theorem gauge_row_map (z : SourceCoordinateSlice) (i : Fin 3) :
    gaugeRowMap z.1 i (z.2.2 : Gauge)=gaugeRow z i := by
  rw [gauge_row_source]
  simp only [gaugeRowMap, sum_apply, smul_apply]
  rfl

theorem gauge_row_native_adjoint (q : Coframe) (i : Fin 3) (a : NativeLie) (A : Gauge) :
    gaugeRowMap q i (nativeGauge a A)=nativeAdjoint a (gaugeRowMap q i A) := by
  simp only [gaugeRowMap, sum_apply, smul_apply]
  change (∑ j : Fin 3, triad q i j • nativeAdjoint a (gaugeCoordinates A j)) =
    nativeAdjoint a (∑ j : Fin 3, triad q i j • gaugeCoordinates A j)
  rw [map_sum]
  simp only [map_smul]

def ambientGaugeSquare (q : Coframe) (A : Gauge) : ℝ :=
  ∑ i : Fin 3, ⟪gaugeRowMap q i A,gaugeRowMap q i A⟫

theorem gauge_square_ambient (z : SourceCoordinateSlice) :
    ambientGaugeSquare z.1 (z.2.2 : Gauge)=gaugeSquare z := by
  unfold ambientGaugeSquare gaugeSquare
  simp only [gauge_row_map]

def gaugeGradient (z : SourceCoordinateSlice) : Gauge :=
  (2 : ℝ) • ∑ i : Fin 3, (gaugeRowMap z.1 i).adjoint (gaugeRow z i)

theorem gauge_gradient_pair (z : SourceCoordinateSlice) (v : Gauge) :
    ⟪gaugeGradient z,v⟫=2*∑ i : Fin 3, ⟪gaugeRow z i,gaugeRowMap z.1 i v⟫ := by
  simp only [gaugeGradient, real_inner_smul_left, sum_inner,
    ContinuousLinearMap.adjoint_inner_left]

private theorem ambient_square_derivative (q : Coframe) (A v : Gauge) :
    fderiv ℝ (ambientGaugeSquare q) A v=
      2*∑ i : Fin 3, ⟪gaugeRowMap q i A,gaugeRowMap q i v⟫ := by
  have hd (i : Fin 3) : DifferentiableAt ℝ
      (fun B : Gauge => ⟪gaugeRowMap q i B,gaugeRowMap q i B⟫) A :=
    (gaugeRowMap q i).differentiableAt.inner ℝ (gaugeRowMap q i).differentiableAt
  unfold ambientGaugeSquare
  rw [fderiv_fun_sum (fun i _ => hd i), sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_inner_apply ℝ (gaugeRowMap q i).differentiableAt
    (gaugeRowMap q i).differentiableAt, ContinuousLinearMap.fderiv]
  have hs := real_inner_comm (gaugeRowMap q i v) (gaugeRowMap q i A)
  linarith

theorem gauge_square_derivative (z : SourceCoordinateSlice) (v : Gauge) :
    fderiv ℝ (ambientGaugeSquare z.1) (z.2.2 : Gauge) v=⟪gaugeGradient z,v⟫ := by
  rw [ambient_square_derivative, gauge_gradient_pair]
  simp only [gauge_row_map]

theorem gauge_gradient_orbit_zero (z : SourceCoordinateSlice) (a : NativeLie) :
    ⟪gaugeGradient z,nativeGauge a (z.2.2 : Gauge)⟫=0 := by
  rw [gauge_gradient_pair]
  simp only [gauge_row_native_adjoint, gauge_row_map, native_adjoint_self,
    Finset.sum_const_zero, mul_zero]

theorem gauge_square_orbit_derivative_zero (z : SourceCoordinateSlice) (a : NativeLie) :
    fderiv ℝ (ambientGaugeSquare z.1) (z.2.2 : Gauge)
      (nativeGauge a (z.2.2 : Gauge))=0 := by
  rw [gauge_square_derivative, gauge_gradient_orbit_zero]

theorem inverse_gauge_gradient (z : physicalChart) (v : Ambient) :
    ⟪gaugeGradient z.val,((inverseL z.val v).2.2 : Gauge)⟫=
      ⟪gaugeGradient z.val,v.2⟫ := by
  have h := congrArg Prod.snd (inverse_right z v)
  change nativeGauge (inverseL z.val v).1 (z.val.2.2 : Gauge)+
    ((inverseL z.val v).2.2 : Gauge)=v.2 at h
  have hi := congrArg (fun A : Gauge => ⟪gaugeGradient z.val,A⟫) h
  rw [inner_add_right, gauge_gradient_orbit_zero, zero_add] at hi
  exact hi

theorem inverse_gauge_euler (z : physicalChart) :
    inverseL z.val (0,(z.val.2.2 : Gauge))=(0,(0,z.val.2.2)) := by
  have h : splitMap z.val (0,(0,z.val.2.2))=(0,(z.val.2.2 : Gauge)) := by
    simp [splitMap, sliceMap]
  rw [←h, inverse_left]

theorem gauge_gradient_euler (z : SourceCoordinateSlice) :
    ⟪gaugeGradient z,(z.2.2 : Gauge)⟫=2*gaugeSquare z := by
  rw [gauge_gradient_pair]
  simp only [gauge_row_map]
  rfl

end LowEnergy.SourceGaugeRadius
