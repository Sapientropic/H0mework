import H0mework.Versions.R2.Physics.Helicity.Source
import H0mework.Versions.R2.Physics.CompositeSpectrum.Parity

/-! P and C act on the actual gauge jet. C here is the pure gauge
transpose-conjugation law; no fermionic charge-conjugation map is asserted. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation
open SU7ExteriorMatterRepresentation Stage9C.Material.SpinPair Stage9DEF

noncomputable section

abbrev MotherMatrix := Matrix SU7MotherIndex SU7MotherIndex ℂ

def connectionMatrix (point : BasePoint) (axis : Fin 3) : MotherMatrix :=
  p286LieBlockEmbed (Runtime.configuration.gaugeConnection point axis.succ)

def bracket (first second : MotherMatrix) : MotherMatrix := first * second - second * first

def bracketCurl (connection field : Fin 3 → MotherMatrix) : Fin 3 → MotherMatrix :=
  ![bracket (connection 1) (field 2) - bracket (connection 2) (field 1),
    bracket (connection 2) (field 0) - bracket (connection 0) (field 2),
    bracket (connection 0) (field 1) - bracket (connection 1) (field 0)]

def homogeneousHelicity (connection field : Fin 3 → MotherMatrix) : ℂ :=
  ∑ axis : Fin 3, (field axis * bracketCurl connection field axis).trace

theorem covariantDerivative_bracket (point : BasePoint) (direction axis : Fin 3) :
    covariantDerivative point direction axis =
      p286LieBracket (Runtime.configuration.gaugeConnection point direction.succ) (magnetic point axis) := by
  rw [covariantDerivative_eq, Runtime.configuration_eq, Compatibility.actual_connection_source,
    magnetic_eq, p286LieBracket_smul_left, p286LieBracket_smul_right, smul_smul]
  congr 1
  ring

theorem motherDerivative_bracket (point : BasePoint) (direction axis : Fin 3) :
    (p286LieBlockEmbed (covariantDerivative point direction axis) : MotherMatrix) =
      bracket (connectionMatrix point direction) (motherMagnetic point axis) := by
  rw [covariantDerivative_bracket, p286LieBlockEmbed_bracket]
  rfl

theorem motherCurl_bracket (point : BasePoint) (axis : Fin 3) :
    motherCurl point axis = bracketCurl (connectionMatrix point) (motherMagnetic point) axis := by
  fin_cases axis <;>
    simp [motherCurl, covariantCurl, bracketCurl, p286LieBlockEmbed_sub, motherDerivative_bracket]

theorem value_homogeneous (point : BasePoint) :
    value point = homogeneousHelicity (connectionMatrix point) (motherMagnetic point) := by
  simp only [value, homogeneousHelicity, motherCurl_bracket]

def charge (matrix : MotherMatrix) : MotherMatrix := -matrix.transpose

theorem charge_involutive (matrix : MotherMatrix) : charge (charge matrix) = matrix := by
  simp [charge]

theorem charge_bracket (first second : MotherMatrix) :
    bracket (charge first) (charge second) = charge (bracket first second) := by
  simp [charge, bracket, Matrix.transpose_mul, Matrix.transpose_sub]

theorem charge_curl (connection field : Fin 3 → MotherMatrix) (axis : Fin 3) :
    bracketCurl (fun i => charge (connection i)) (fun i => charge (field i)) axis =
      charge (bracketCurl connection field axis) := by
  fin_cases axis <;> simp [bracketCurl, charge, bracket, Matrix.transpose_sub, Matrix.transpose_mul] <;> abel

theorem charge_trace_pair (first second : MotherMatrix) :
    (charge first * charge second).trace = (first * second).trace := by
  simp only [charge, _root_.neg_mul_neg, ← Matrix.transpose_mul, Matrix.trace_transpose]
  exact Matrix.trace_mul_comm _ _

theorem charge_even (connection field : Fin 3 → MotherMatrix) :
    homogeneousHelicity (fun i => charge (connection i)) (fun i => charge (field i)) =
      homogeneousHelicity connection field := by
  simp only [homogeneousHelicity, charge_curl, charge_trace_pair]

theorem parity_bracket (first second : MotherMatrix) : bracket (-first) second = -bracket first second := by
  simp [bracket]
  abel

theorem parity_curl (connection field : Fin 3 → MotherMatrix) (axis : Fin 3) :
    bracketCurl (fun i => -connection i) field axis = -bracketCurl connection field axis := by
  unfold bracketCurl
  fin_cases axis <;> simp [parity_bracket] <;> abel

theorem parity_odd (connection field : Fin 3 → MotherMatrix) :
    homogeneousHelicity (fun i => -connection i) field = -homogeneousHelicity connection field := by
  simp only [homogeneousHelicity, parity_curl, Matrix.mul_neg, Matrix.trace_neg, Finset.sum_neg_distrib]

def parityConnection (point : BasePoint) (axis : Fin 3) : MotherMatrix :=
  p286LieBlockEmbed (parityGaugePullback.gaugeConnection point axis.succ)

def parityMagnetic (point : BasePoint) (axis : Fin 3) : MotherMatrix :=
  p286LieBlockEmbed (holonomicGaugeCurvature parityGaugePullback point (magneticPair axis))

theorem parityConnection_eq (point : BasePoint) (axis : Fin 3) :
    parityConnection point axis = -connectionMatrix point axis := by
  simp only [parityConnection, parityGaugePullback_connection, connectionMatrix,
    Runtime.configuration_eq, Compatibility.actual_connection_source]
  fin_cases axis <;> simp [gaugePotential, p286LieBlockEmbed_real_smul, SetLike.val_smul]

theorem parityMagnetic_eq (point : BasePoint) (axis : Fin 3) :
    parityMagnetic point axis = motherMagnetic point axis := by
  rw [parityMagnetic, parityGaugePullback_curvature]
  rfl

theorem actual_parity_odd (point : BasePoint) :
    homogeneousHelicity (parityConnection point) (parityMagnetic point) = -value point := by
  have connection : parityConnection point = fun axis => -connectionMatrix point axis :=
    funext (parityConnection_eq point)
  have field : parityMagnetic point = motherMagnetic point := funext (parityMagnetic_eq point)
  rw [connection, field, parity_odd, value_homogeneous]

theorem actual_charge_even (point : BasePoint) :
    homogeneousHelicity (fun i => charge (connectionMatrix point i))
      (fun i => charge (motherMagnetic point i)) = value point := by
  rw [charge_even, value_homogeneous]

def gaugeMap (element : SU7MotherGroup) : MotherMatrix ≃⋆ₐ[ℂ] MotherMatrix :=
  Unitary.conjStarAlgAut ℂ MotherMatrix
    ⟨element.val, Matrix.specialUnitaryGroup_le_unitaryGroup element.property⟩

theorem gaugeMap_trace (element : SU7MotherGroup) (matrix : MotherMatrix) :
    (gaugeMap element matrix).trace = matrix.trace := by
  change ((element : MotherMatrix) * matrix * star (element : MotherMatrix)).trace = _
  rw [Matrix.trace_mul_cycle,
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup element.property), Matrix.one_mul]

theorem gauge_curl (element : SU7MotherGroup) (connection field : Fin 3 → MotherMatrix) (axis : Fin 3) :
    bracketCurl (fun i => gaugeMap element (connection i)) (fun i => gaugeMap element (field i)) axis =
      gaugeMap element (bracketCurl connection field axis) := by
  fin_cases axis <;> simp [bracketCurl, bracket]

theorem gauge_invariant (element : SU7MotherGroup) (connection field : Fin 3 → MotherMatrix) :
    homogeneousHelicity (fun i => gaugeMap element (connection i)) (fun i => gaugeMap element (field i)) =
      homogeneousHelicity connection field := by
  simp only [homogeneousHelicity, gauge_curl, ← map_mul, gaugeMap_trace]

theorem actual_fullGauge_invariant (element : SU7MotherGroup) (point : BasePoint) :
    homogeneousHelicity (fun i => gaugeMap element (connectionMatrix point i))
      (fun i => gaugeMap element (motherMagnetic point i)) = value point := by
  rw [gauge_invariant, value_homogeneous]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
