import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussRadialHamiltonian
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussGradedUnitary

/-! Dynamic retarded readback of the radial source commutator. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussRadialRetarded
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussGradedUnitary
open GaussRadialDomain GaussRadialMomentum GaussRadialHamiltonian GaussHistoryHilbert
open GaussUnitaryHistory (HistorySpace inclusion reader)
open scoped Topology InnerProductSpace ContDiff

def diagTest (f : QuantumTest) : diagonal.domain :=
  ⟨embed f, embed_mem_core f⟩

theorem diagTest_apply (f : QuantumTest) : (diagTest f : H)=embed f := rfl

theorem diagTest_action (f : QuantumTest) : diagonal (diagTest f)=embed (diagonalAction f) := by
  change embed (diagonalAction (coreEquiv.symm (coreEquiv f))) = _
  rw [coreEquiv.symm_apply_apply]

theorem inverse_diagTest (f : QuantumTest) :
    inverseRadius (diagTest f : H) = (diagTest (inverseAction f) : H) := by
  rw [diagTest_apply,inverse_core]
  rfl

theorem radial_diagTest (f : QuantumTest) :
    radialAction f = radialAction f := rfl

theorem diagonal_radial_core (f : QuantumTest) :
    diagonalAction (inverseAction f) = inverseAction (diagonalAction f)+radialAction f := by
  have h := LinearMap.congr_fun GaussRadialHamiltonian.diagonal_commutator f
  change diagonalAction (inverseAction f)=inverseAction (diagonalAction f)+radialAction f at h
  simpa only [inverse_core] using h

theorem radial_response_left (f g : QuantumTest) (t : ℝ) :
    HasDerivAt (fun u => inner ℂ (time u (inclusion (embed (inverseAction f)))) (inclusion (embed g)))
      (inner ℂ (time t (inclusion (embed (inverseAction (diagonalAction f))))) (0 : HistorySpace) +
        inner ℂ ((-Complex.I) • (time t (inclusion (embed (inverseAction (diagonalAction f))))+
          time t (inclusion (embed (radialAction f))))) (inclusion (embed g))) t := by
  have h := GaussGradedUnitary.core_derivative (diagTest (inverseAction f)) t
  have h0 := GaussGradedUnitary.core_derivative (diagTest f) t
  have hc := diagonal_radial_core f
  have he : diagonal (diagTest (inverseAction f)) =
      diagTest (inverseAction (diagonalAction f))+diagTest (radialAction f) := by
    rw [diagTest_action]
    simp only [diagTest]
    change embed (diagonalAction (inverseAction f)) =
      embed (inverseAction (diagonalAction f))+embed (radialAction f)
    rw [hc, map_add]
  rw [he] at h
  have hpair := h.inner ℂ (hasDerivAt_const t (inclusion (embed g)))
  simpa only [diagTest_apply, inner_zero_right, GaussGradedUnitary.time_inclusion,
    inner_add_left, map_add] using hpair

theorem radial_retarded_source (f g : QuantumTest) (eta eta' : ℝ → ℂ)
    (differentiable : ∀ t, HasDerivAt eta (eta' t) t) (derivative_continuous : Continuous eta')
    (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ),
      eta' t * inner ℂ (time t (inclusion (embed (inverseAction f)))) (inclusion (embed g)) +
      eta t * (inner ℂ (time t (inclusion (embed (inverseAction (diagonalAction f))))) (0 : HistorySpace) +
        inner ℂ ((-Complex.I) • (time t (inclusion (embed (inverseAction (diagonalAction f))))+
          time t (inclusion (embed (radialAction f))))) (inclusion (embed g)))) =
      -eta 0 * inner ℂ (embed (inverseAction f)) (embed g) := by
  let c := fun t => inner ℂ (time t (inclusion (embed (inverseAction f)))) (inclusion (embed g))
  let k := fun t => inner ℂ (time t (inclusion (embed (inverseAction (diagonalAction f))))) (0 : HistorySpace) +
    inner ℂ ((-Complex.I) • (time t (inclusion (embed (inverseAction (diagonalAction f))))+
      time t (inclusion (embed (radialAction f))))) (inclusion (embed g))
  have hc : Continuous c := (GaussGradedUnitary.source_continuous _).inner continuous_const
  have hk : Continuous k := by
    have h₁ := Continuous.inner (𝕜 := ℂ)
      (GaussGradedUnitary.source_continuous (embed (inverseAction (diagonalAction f))))
      (continuous_const : Continuous (fun _ : ℝ => (0 : HistorySpace)))
    have h₂ := GaussGradedUnitary.source_continuous (embed (inverseAction (diagonalAction f)))
    have h₃ := GaussGradedUnitary.source_continuous (embed (radialAction f))
    have hs := h₂.add h₃
    have hsmul := hs.const_smul (-Complex.I)
    exact h₁.add (Continuous.inner (𝕜 := ℂ) hsmul
      (continuous_const : Continuous (fun _ : ℝ => inclusion (embed g))))
  have he : Continuous eta := continuous_iff_continuousAt.mpr
    (fun t => (differentiable t).continuousAt)
  have hd (t : ℝ) : HasDerivAt (fun u => eta u * c u)
      (eta' t*c t+eta t*k t) t :=
    (differentiable t).mul (radial_response_left f g t)
  have integrable := ((derivative_continuous.mul hc).add (he.mul hk)).intervalIntegrable
      (μ := MeasureTheory.volume) 0 (b : ℝ)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) integrable
  simpa only [c, k, end_zero, zero_mul, GaussGradedUnitary.time_zero,
    one_apply_eq_self, zero_sub, neg_mul, inclusion.inner_map_map] using identity

#print axioms diagTest_action
#print axioms diagonal_radial_core
#print axioms radial_response_left
#print axioms radial_retarded_source
end LowEnergy.GaussRadialRetarded
