import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussOriginalYRetarded
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussRadialRetarded

/-! The complete native H=H0+Y retarded equation keeps literal Y as a source term. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussFullRetarded
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussGradedUnitary
open GaussFullHamiltonian GaussYukawaOperator GaussYukawaCoefficient
open GaussUnitaryHistory (HistorySpace inclusion)
open scoped Topology InnerProductSpace ContDiff

def response (t : ℝ) (f g : QuantumTest) : ℂ :=
  inner ℂ (time t (inclusion (embed f))) (inclusion (embed g))

theorem diagonal_as_full_source (f : QuantumTest) :
    diagonalAction f = fullAction f-originalAction f := by
  simp only [fullAction, LinearMap.add_apply]
  abel

theorem diagonal_time_split (f : QuantumTest) (t : ℝ) :
    time t (inclusion (embed (diagonalAction f))) =
      time t (inclusion (embed (fullAction f)))-time t (inclusion (embed (originalAction f))) := by
  rw [diagonal_as_full_source]
  simp only [map_sub]

theorem response_zero (f g : QuantumTest) :
    response 0 f g = inner ℂ (embed f) (embed g) := by
  unfold response
  rw [GaussGradedUnitary.time_zero]
  simp only [one_apply_eq_self]
  exact inclusion.inner_map_map _ _

theorem response_left (t : ℝ) (f g : QuantumTest) :
    HasDerivAt (fun u => response u f g)
      (inner ℂ ((-Complex.I) •
        (time t (inclusion (embed (fullAction f)))-time t (inclusion (embed (originalAction f)))))
        (inclusion (embed g))) t := by
  have h := GaussGradedUnitary.core_derivative (GaussRadialRetarded.diagTest f) t
  rw [GaussRadialRetarded.diagTest_action] at h
  rw [diagonal_time_split] at h
  have hp := h.inner ℂ (hasDerivAt_const t (inclusion (embed g)))
  simpa only [response, GaussRadialRetarded.diagTest_apply,
    GaussGradedUnitary.time_inclusion, inner_zero_right, add_zero, zero_add] using hp

theorem retarded_source (f g : QuantumTest) (eta eta' : ℝ → ℂ)
    (differentiable : ∀ t, HasDerivAt eta (eta' t) t) (derivative_continuous : Continuous eta')
    (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ),
      eta' t * response t f g +
      eta t * inner ℂ ((-Complex.I) •
        (time t (inclusion (embed (fullAction f)))-time t (inclusion (embed (originalAction f)))))
        (inclusion (embed g))) =
      -eta 0 * inner ℂ (embed f) (embed g) := by
  let c := fun t => response t f g
  let k := fun t => inner ℂ ((-Complex.I) •
    (time t (inclusion (embed (fullAction f)))-time t (inclusion (embed (originalAction f)))))
    (inclusion (embed g))
  have hc : Continuous c := by
    unfold c response
    exact (GaussGradedUnitary.source_continuous (embed f)).inner continuous_const
  have hk : Continuous k := by
    unfold k
    exact Continuous.inner (𝕜 := ℂ)
      (((GaussGradedUnitary.source_continuous (embed (fullAction f))).sub
        (GaussGradedUnitary.source_continuous (embed (originalAction f)))).const_smul (-Complex.I))
      (continuous_const : Continuous (fun _ : ℝ => inclusion (embed g)))
  have he : Continuous eta := continuous_iff_continuousAt.mpr
    (fun t => (differentiable t).continuousAt)
  have hd (t : ℝ) : HasDerivAt (fun u => eta u * c u)
      (eta' t*c t+eta t*k t) t :=
    (differentiable t).mul (response_left t f g)
  have integrable := ((derivative_continuous.mul hc).add (he.mul hk)).intervalIntegrable
      (μ := MeasureTheory.volume) 0 (b : ℝ)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) integrable
  simpa only [c, k, end_zero, zero_mul, response_zero, one_apply_eq_self,
    zero_sub, neg_mul, inclusion.inner_map_map] using identity

#print axioms diagonal_time_split
#print axioms response_left
#print axioms retarded_source
end LowEnergy.GaussFullRetarded
