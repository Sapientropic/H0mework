import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussYukawaRetarded
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussFullHamiltonian
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussRadialRetarded

/-! Literal original Y and independent Y-adjoint insertions in the retarded core. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussOriginalYRetarded
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussGradedUnitary GaussFullHamiltonian
open GaussYukawaCoefficient GaussYukawaOperator
open GaussUnitaryHistory (HistorySpace inclusion)
open GaussRadialRetarded
open scoped Topology InnerProductSpace ContDiff

def response (t : ℝ) (f g : QuantumTest) : ℂ :=
  inner ℂ (time t (inclusion (embed f))) (inclusion (embed (originalAction g)))

def dualResponse (t : ℝ) (f g : QuantumTest) : ℂ :=
  inner ℂ (time t (inclusion (embed (adjointAction f)))) (inclusion (embed g))

theorem response_left (t : ℝ) (f g : QuantumTest) :
    HasDerivAt (fun u => response u f g)
      (inner ℂ ((-Complex.I) • time t (inclusion (embed (diagonalAction f))))
        (inclusion (embed (originalAction g)))) t := by
  have h := GaussGradedUnitary.core_derivative (GaussRadialRetarded.diagTest f) t
  have hp := h.inner ℂ (hasDerivAt_const t (inclusion (embed (originalAction g))))
  simpa only [response, GaussRadialRetarded.diagTest_apply,
    GaussRadialRetarded.diagTest_action, GaussGradedUnitary.time_inclusion,
    inner_zero_right, add_zero, zero_add] using hp

theorem dual_response_left (t : ℝ) (f g : QuantumTest) :
    HasDerivAt (fun u => dualResponse u f g)
      (inner ℂ ((-Complex.I) • time t (inclusion (embed (diagonalAction (adjointAction f)))))
        (inclusion (embed g))) t := by
  have h := GaussGradedUnitary.core_derivative (GaussRadialRetarded.diagTest (adjointAction f)) t
  have hp := h.inner ℂ (hasDerivAt_const t (inclusion (embed g)))
  simpa only [dualResponse, GaussRadialRetarded.diagTest_apply,
    GaussRadialRetarded.diagTest_action, GaussGradedUnitary.time_inclusion,
    inner_zero_right, add_zero, zero_add] using hp

theorem response_zero (f g : QuantumTest) :
    response 0 f g = inner ℂ (embed f) (embed (originalAction g)) := by
  unfold response
  rw [GaussGradedUnitary.time_zero]
  simp only [one_apply_eq_self]
  exact inclusion.inner_map_map _ _

theorem dual_response_zero (f g : QuantumTest) :
    dualResponse 0 f g = inner ℂ (embed (adjointAction f)) (embed g) := by
  unfold dualResponse
  rw [GaussGradedUnitary.time_zero]
  simp only [one_apply_eq_self]
  exact inclusion.inner_map_map _ _

theorem retarded_source (f g : QuantumTest) (eta eta' : ℝ → ℂ)
    (differentiable : ∀ t, HasDerivAt eta (eta' t) t) (derivative_continuous : Continuous eta')
    (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ),
      eta' t * response t f g +
      eta t * inner ℂ ((-Complex.I) • time t (inclusion (embed (diagonalAction f))))
        (inclusion (embed (originalAction g)))) =
      -eta 0 * inner ℂ (embed f) (embed (originalAction g)) := by
  let c := fun t => response t f g
  let k := fun t => inner ℂ ((-Complex.I) • time t (inclusion (embed (diagonalAction f))))
    (inclusion (embed (originalAction g)))
  have hc : Continuous c := by
    unfold c response
    exact (GaussGradedUnitary.source_continuous (embed f)).inner continuous_const
  have hk : Continuous k := by
    unfold k
    exact Continuous.inner (𝕜 := ℂ)
      ((GaussGradedUnitary.source_continuous (embed (diagonalAction f))).const_smul (-Complex.I))
      (continuous_const : Continuous (fun _ : ℝ => inclusion (embed (originalAction g))))
  have he : Continuous eta := continuous_iff_continuousAt.mpr
    (fun t => (differentiable t).continuousAt)
  have hd (t : ℝ) : HasDerivAt (fun u => eta u * c u)
      (eta' t*c t+eta t*k t) t :=
    (differentiable t).mul (response_left t f g)
  have integrable := ((derivative_continuous.mul hc).add (he.mul hk)).intervalIntegrable
      (μ := MeasureTheory.volume) 0 (b : ℝ)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) integrable
  simpa only [c, k, end_zero, zero_mul, response_zero, one_apply_eq_self, zero_sub, neg_mul] using identity

theorem dual_retarded_source (f g : QuantumTest) (eta eta' : ℝ → ℂ)
    (differentiable : ∀ t, HasDerivAt eta (eta' t) t) (derivative_continuous : Continuous eta')
    (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ),
      eta' t * dualResponse t f g +
      eta t * inner ℂ ((-Complex.I) • time t (inclusion (embed (diagonalAction (adjointAction f)))))
        (inclusion (embed g))) =
      -eta 0 * inner ℂ (embed (adjointAction f)) (embed g) := by
  let c := fun t => dualResponse t f g
  let k := fun t => inner ℂ ((-Complex.I) • time t (inclusion (embed (diagonalAction (adjointAction f)))))
    (inclusion (embed g))
  have hc : Continuous c := by
    unfold c dualResponse
    exact (GaussGradedUnitary.source_continuous (embed (adjointAction f))).inner continuous_const
  have hk : Continuous k := by
    unfold k
    exact Continuous.inner (𝕜 := ℂ)
      ((GaussGradedUnitary.source_continuous (embed (diagonalAction (adjointAction f)))).const_smul (-Complex.I))
      (continuous_const : Continuous (fun _ : ℝ => inclusion (embed g)))
  have he : Continuous eta := continuous_iff_continuousAt.mpr
    (fun t => (differentiable t).continuousAt)
  have hd (t : ℝ) : HasDerivAt (fun u => eta u * c u)
      (eta' t*c t+eta t*k t) t :=
    (differentiable t).mul (dual_response_left t f g)
  have integrable := ((derivative_continuous.mul hc).add (he.mul hk)).intervalIntegrable
      (μ := MeasureTheory.volume) 0 (b : ℝ)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) integrable
  simpa only [c, k, end_zero, zero_mul, dual_response_zero, one_apply_eq_self, zero_sub, neg_mul] using identity

#print axioms response_left
#print axioms dual_response_left
#print axioms retarded_source
#print axioms dual_retarded_source
end LowEnergy.GaussOriginalYRetarded
