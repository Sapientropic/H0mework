import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussLiveMomentum
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCartanCubic

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussInverseSecond
open GaussLiveMomentum GaussHistoryHilbert
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumResidualGaugeSlice
open SaturationMonoid.PhysicsCore StageNineHolonomicField
open StageNineP286BracketCalculus StageNineP286LinkedActiveLieRepresentation
open StageNineP286GaugeConnectionVariationDensity
open scoped ContDiff

def nativeBracket (a b : NativeLie) : NativeLie := coordinateBracket a b

def ambientAction (a : NativeLie) : Ambient →ₗ[ℝ] Ambient :=
  (scalarP286ActionBilinear a).prodMap (nativeGauge a)

def sourceBase (z : SourceCoordinateSlice) : Ambient := (vacuum + (z.2.1 : Scalar), (z.2.2 : Gauge))

theorem orbit_is_action (z : SourceCoordinateSlice) (a : NativeLie) :
    orbitMap z a = ambientAction a (sourceBase z) := rfl

theorem ambient_bracket (a b : NativeLie) (v : Ambient) :
    ambientAction (nativeBracket a b) v = ambientAction a (ambientAction b v) -
      ambientAction b (ambientAction a v) := by
  apply Prod.ext
  · exact scalarP286ActionBilinear_coordinateBracket a b v.1
  · apply gaugeCoordinates.injective
    funext i
    change coordinateBracket (coordinateBracket a b) (gaugeCoordinates v.2 i) =
      coordinateBracket a (coordinateBracket b (gaugeCoordinates v.2 i)) -
        coordinateBracket b (coordinateBracket a (gaugeCoordinates v.2 i))
    have h := SourceCartanCubic.bracket_derivation a b (gaugeCoordinates v.2 i)
    exact eq_sub_of_add_eq h.symm

def forwardCurvature (z : SourceCoordinateSlice) (u v : Split) : Ambient :=
  ambientAction u.1 (sliceMap v.2) + ambientAction v.1 (sliceMap u.2) +
    (1/2 : ℝ) • (ambientAction u.1 (ambientAction v.1 (sourceBase z)) +
      ambientAction v.1 (ambientAction u.1 (sourceBase z)))

def inverseCurvature (z : physicalChart) (v w : Ambient) : Split :=
  -inverseL z.val (forwardCurvature z.val (inverseL z.val v) (inverseL z.val w))

theorem inverseCurvature_symmetric (z : physicalChart) (v w : Ambient) :
    inverseCurvature z v w = inverseCurvature z w v := by
  apply congrArg (fun x : Ambient => -inverseL z.val x)
  unfold forwardCurvature
  module

theorem inverse_curvature_equation (z : physicalChart) (v w : Ambient) :
    splitMap z.val (inverseCurvature z v w) +
      forwardCurvature z.val (inverseL z.val v) (inverseL z.val w) = 0 := by
  rw [inverseCurvature, map_neg, inverse_right, neg_add_cancel]

theorem varying_slice (h : Slice) (u : Split) :
    variationL (0, h) u = ambientAction u.1 (sliceMap h) := rfl

theorem inverse_curvature_transport (z : physicalChart) (v w : Ambient) :
    inverseCurvature z v w =
      fderiv ℝ inverseL z.val (0, (inverseL z.val v).2) w -
      inverseL z.val (ambientAction (inverseL z.val v).1 w) +
      ((1/2 : ℝ) • nativeBracket (inverseL z.val v).1 (inverseL z.val w).1, 0) := by
  rw [inverse_derivative, varying_slice]
  apply (splitEquiv z).injective
  change splitMap z.val (inverseCurvature z v w) = splitMap z.val _
  rw [inverseCurvature, map_neg, inverse_right, map_add, map_sub, map_neg,
    inverse_right, inverse_right]
  have horbit : splitMap z.val
      ((1/2 : ℝ) • nativeBracket (inverseL z.val v).1 (inverseL z.val w).1, 0) =
      (1/2 : ℝ) • ambientAction (nativeBracket (inverseL z.val v).1 (inverseL z.val w).1)
        (sourceBase z.val) := by
    change orbitMap z.val ((1/2 : ℝ) • nativeBracket (inverseL z.val v).1 (inverseL z.val w).1) + sliceMap 0 = _
    rw [map_zero, add_zero, map_smul, orbit_is_action]
  rw [horbit, ambient_bracket]
  have hw : w = ambientAction (inverseL z.val w).1 (sourceBase z.val) +
      sliceMap (inverseL z.val w).2 := (inverse_right z w).symm
  conv_rhs => arg 1; arg 2; rw [hw, map_add]
  unfold forwardCurvature
  module

def orbitCurve (z : SourceCoordinateSlice) (u : Split) (t : ℝ) : Ambient :=
  NormedSpace.exp (t • (ambientAction u.1).toContinuousLinearMap)
    (sourceBase z + t • sliceMap u.2)

def orbitCurveFirst (z : SourceCoordinateSlice) (u : Split) (t : ℝ) : Ambient :=
  ambientAction u.1 (orbitCurve z u t) +
    NormedSpace.exp (t • (ambientAction u.1).toContinuousLinearMap) (sliceMap u.2)

theorem orbit_curve_derivative (z : SourceCoordinateSlice) (u : Split) (t : ℝ) :
    HasDerivAt (orbitCurve z u) (orbitCurveFirst z u t) t := by
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ)
    (𝔸 := Ambient →L[ℝ] Ambient) (ambientAction u.1).toContinuousLinearMap t
  have hb : HasDerivAt (fun r : ℝ => sourceBase z + r • sliceMap u.2) (sliceMap u.2) t := by
    simpa using ((hasDerivAt_id t).smul_const (sliceMap u.2)).const_add (sourceBase z)
  exact he.clm_apply hb

theorem orbit_curve_first_source (z : SourceCoordinateSlice) (u : Split) :
    orbitCurveFirst z u 0 = splitMap z u := by
  have hz : (0 : ℝ) • (ambientAction u.1).toContinuousLinearMap = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    exact zero_smul ℝ (ambientAction u.1 v)
  have he : NormedSpace.exp ((0 : ℝ) • (ambientAction u.1).toContinuousLinearMap) = 1 := by
    rw [hz, NormedSpace.exp_zero]
  simp only [orbitCurveFirst, orbitCurve, he, one_apply_eq_self, zero_smul, add_zero]
  rfl

theorem orbit_curve_second (z : SourceCoordinateSlice) (u : Split) :
    HasDerivAt (fun t => deriv (orbitCurve z u) t) (forwardCurvature z u u) 0 := by
  have de := hasDerivAt_exp_smul_const' (𝕂 := ℝ)
    (𝔸 := Ambient →L[ℝ] Ambient) (ambientAction u.1).toContinuousLinearMap (0 : ℝ)
  have ha := (ambientAction u.1).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    0 (orbit_curve_derivative z u 0)
  have hb := de.clm_apply (hasDerivAt_const (0 : ℝ) (sliceMap u.2))
  have hc := ha.add hb
  have hd : (fun t => deriv (orbitCurve z u) t) = orbitCurveFirst z u :=
    funext (fun t => (orbit_curve_derivative z u t).deriv)
  rw [hd]
  have hz : (0 : ℝ) • (ambientAction u.1).toContinuousLinearMap = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    exact zero_smul ℝ (ambientAction u.1 v)
  have he : NormedSpace.exp ((0 : ℝ) • (ambientAction u.1).toContinuousLinearMap) = 1 := by
    rw [hz, NormedSpace.exp_zero]
  convert hc using 1 <;> try rfl
  rw [orbit_curve_first_source, he, mul_one, map_zero, add_zero]
  change ambientAction u.1 (sliceMap u.2) + ambientAction u.1 (sliceMap u.2) +
      (1/2 : ℝ) • (ambientAction u.1 (ambientAction u.1 (sourceBase z)) +
        ambientAction u.1 (ambientAction u.1 (sourceBase z))) =
    ambientAction u.1 (ambientAction u.1 (sourceBase z) + sliceMap u.2) +
      ambientAction u.1 (sliceMap u.2)
  rw [map_add]
  module

#print axioms ambient_bracket
#print axioms inverse_curvature_transport
#print axioms orbit_curve_derivative
#print axioms orbit_curve_second
end LowEnergy.GaussInverseSecond
