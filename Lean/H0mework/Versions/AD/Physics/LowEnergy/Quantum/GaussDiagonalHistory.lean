import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussCoframeForm
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussMatterCore
import H0mework.Physics.LowEnergy.Quantum.WeakCoreEvolution

/-! The concrete original H0 consumes the Gauss100 time-kernel constructor. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussDiagonalHistory
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert
open SymmetricGraphClosure WeakCoreEvolution
open scoped Topology Interval

def diagonalAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  GaussNativeForm.nativeAction + GaussCoframeForm.coframeAction + GaussMatterCore.matterAction

theorem diagonalAction_pair (f g : QuantumTest) :
    sourcePair f (diagonalAction g) = sourcePair (diagonalAction f) g := by
  simp only [diagonalAction, LinearMap.add_apply, sourcePair, map_add, inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (GaussNativeForm.nativeAction_pair f g) (GaussCoframeForm.coframeAction_pair f g))
    (GaussMatterCore.matter_pair f g)

def diagonal : H →ₗ.[ℂ] H := realize diagonalAction

theorem diagonal_pair : FormalAdjointPair diagonal diagonal := by
  intro f g
  obtain ⟨f, rfl⟩ := coreEquiv.surjective f
  obtain ⟨g, rfl⟩ := coreEquiv.surjective g
  change inner ℂ (embed (diagonalAction (coreEquiv.symm (coreEquiv f)))) (embed g) =
    inner ℂ (embed f) (embed (diagonalAction (coreEquiv.symm (coreEquiv g))))
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply]
  exact (diagonalAction_pair f g).symm

theorem diagonal_dense : Dense (diagonal.domain : Set H) := realize_dense diagonalAction

theorem diagonal_invariant (f : diagonal.domain) : diagonal f ∈ diagonal.domain :=
  realize_preserves_core diagonalAction f

def history (t : ℝ) : H →L[ℂ] H := weakEvolution diagonal diagonal_pair t

theorem history_zero : history 0 = 1 := weak_evolution_zero diagonal diagonal_pair

theorem history_continuous (f : H) : Continuous (fun t => history t f) :=
  weak_evolution_continuous diagonal diagonal_pair diagonal_dense f

theorem history_contraction (t : ℝ) (f : H) : ‖history t f‖ ≤ ‖f‖ :=
  weak_evolution_contraction diagonal diagonal_pair t f

theorem history_derivative (f : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun u => history u (f : H)) ((-Complex.I) • history t (diagonal f)) t :=
  weak_evolution_core_derivative diagonal diagonal_pair f (diagonal_invariant f) t

theorem history_left_equation (f g : diagonal.domain) (t : ℝ) :
    inner ℂ (history t (f : H)) (diagonal g) = inner ℂ (history t (diagonal f)) (g : H) :=
  weak_evolution_original_pairing diagonal diagonal_pair f g (diagonal_invariant f) (diagonal_invariant g) t

theorem retarded_source (f g : diagonal.domain) (eta eta' : ℝ → ℂ)
    (differentiable : ∀ t, HasDerivAt eta (eta' t) t) (derivative_continuous : Continuous eta')
    (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ),
      eta' t * inner ℂ (history t (f : H)) (g : H) +
      eta t * (Complex.I * inner ℂ (history t (f : H)) (diagonal g))) =
      -eta 0 * inner ℂ (f : H) (g : H) :=
  retarded_test_identity diagonal diagonal_pair diagonal_dense f g
    (diagonal_invariant f) (diagonal_invariant g) eta eta' differentiable derivative_continuous b end_zero

#print axioms diagonal_pair
#print axioms history
#print axioms history_derivative
#print axioms retarded_source
end LowEnergy.GaussDiagonalHistory
