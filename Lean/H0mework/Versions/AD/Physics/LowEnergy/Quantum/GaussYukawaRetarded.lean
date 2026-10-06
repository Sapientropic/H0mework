import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussYukawaInteraction
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussGradedUnitary

/-! The source-generated bounded Y/r readout enters the common retarded kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussYukawaRetarded
open GaussCoreHilbert GaussDiagonalHistory GaussGradedUnitary GaussYukawaOperator
open GaussYukawaInteraction
open GaussUnitaryHistory (HistorySpace inclusion reader)
open scoped Topology InnerProductSpace ContDiff

def response (t s : ℝ) (x y : diagonal.domain) : ℂ :=
  GaussGradedUnitary.response bounded t s x y

def next (x : diagonal.domain) : diagonal.domain :=
  ⟨diagonal x, diagonal_invariant x⟩

theorem response_left (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => response u s x y)
      (Complex.I * response t s (next x) y) t := by
  simpa only [response, next] using GaussGradedUnitary.response_left bounded t s x y

theorem response_right (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => response t u x y)
      (-Complex.I * response t s x (next y)) s := by
  simpa only [response, next] using GaussGradedUnitary.response_right bounded t s x y

theorem response_zero (x y : diagonal.domain) :
    response 0 0 x y = inner ℂ (x : H) (bounded (y : H)) := by
  unfold response GaussGradedUnitary.response
  rw [GaussGradedUnitary.time_zero]
  simp only [one_apply_eq_self]
  rw [GaussUnitaryHistory.reader_inclusion]
  exact inclusion.inner_map_map _ _

theorem source_retarded (x y : diagonal.domain) (eta eta' : ℝ → ℂ)
    (differentiable : ∀ t, HasDerivAt eta (eta' t) t) (derivative_continuous : Continuous eta')
    (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ),
      eta' t * response t 0 x y +
      eta t * (Complex.I * response t 0 (next x) y)) =
      -eta 0 * inner ℂ (x : H) (bounded (y : H)) := by
  let c := fun t => response t 0 x y
  let k := fun t => response t 0 (next x) y
  have hc : Continuous c := by
    unfold c response
    exact (GaussGradedUnitary.source_continuous (x : H)).inner continuous_const
  have hk : Continuous k := by
    unfold k response
    exact (GaussGradedUnitary.source_continuous (diagonal x)).inner continuous_const
  have he : Continuous eta := continuous_iff_continuousAt.mpr
    (fun t => (differentiable t).continuousAt)
  have hd (t : ℝ) : HasDerivAt (fun u => eta u * c u)
      (eta' t*c t+eta t*(Complex.I*k t)) t :=
    (differentiable t).mul (by simpa only [c] using response_left t 0 x y)
  have integrable := ((derivative_continuous.mul hc).add
    (he.mul ((continuous_const : Continuous (fun _ : ℝ => Complex.I)).mul hk))).intervalIntegrable
      (μ := MeasureTheory.volume) 0 (b : ℝ)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) integrable
  simpa only [c, k, end_zero, zero_mul, response_zero, one_apply_eq_self, zero_sub, neg_mul] using identity

#print axioms response_left
#print axioms response_right
#print axioms source_retarded
end LowEnergy.GaussYukawaRetarded
