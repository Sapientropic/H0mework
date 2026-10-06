import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussDiagonalGrade
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The original retarded history enters its generated adjoint graph and time-jet tower. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussAdjointHistory
open GaussCoreHilbert GaussDiagonalHistory
open scoped ContDiff Topology

abbrev evolution := GaussDiagonalGrade.history

def graph : Submodule ℂ (H × H) where
  carrier := {p | ∀ d : diagonal.domain, inner ℂ p.1 (diagonal d) = inner ℂ p.2 (d : H)}
  zero_mem' := by intro d; simp
  add_mem' := by
    intro p q hp hq d
    change inner ℂ (p.1+q.1) (diagonal d) = inner ℂ (p.2+q.2) (d : H)
    rw [inner_add_left, inner_add_left, hp d, hq d]
  smul_mem' := by
    intro c p hp d
    change inner ℂ (c • p.1) (diagonal d) = inner ℂ (c • p.2) (d : H)
    rw [inner_smul_left, inner_smul_left, hp d]

theorem graph_closed : IsClosed (graph : Set (H × H)) := by
  rw [show (graph : Set (H × H)) = ⋂ d : diagonal.domain,
    {p : H × H | inner ℂ p.1 (diagonal d) = inner ℂ p.2 (d : H)} by
      ext p
      simp [graph]]
  exact isClosed_iInter (fun d =>
    isClosed_eq (continuous_fst.inner continuous_const) (continuous_snd.inner continuous_const))

theorem graph_zero (p : H × H) (hp : p ∈ graph) (zero : p.1=0) : p.2=0 := by
  have h : Set.EqOn (fun z : H => inner ℂ p.2 z) (fun _ => 0) (diagonal.domain : Set H) := by
    intro z hz
    have he := hp ⟨z,hz⟩
    rw [zero, inner_zero_left] at he
    exact he.symm
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp
    (h.closure (continuous_const.inner continuous_id) continuous_const (diagonal_dense p.2))

def maximalAdjoint : H →ₗ.[ℂ] H := graph.toLinearPMap

theorem maximalAdjoint_graph : maximalAdjoint.graph = graph := graph.toLinearPMap_graph_eq graph_zero

theorem original_extends : diagonal ≤ maximalAdjoint := by
  apply LinearPMap.le_of_le_graph
  rw [maximalAdjoint_graph]
  intro p hp
  obtain ⟨x,rfl⟩ := diagonal.mem_graph_iff'.mp hp
  intro d
  exact (diagonal_pair x d).symm

theorem history_graph (x : diagonal.domain) (t : ℝ) :
    (evolution t (x : H), evolution t (diagonal x)) ∈ graph := by
  intro d
  exact NativeHistoryGrade.history_original_pairing diagonal diagonal_pair
    GaussDiagonalGrade.stable GaussDiagonalGrade.diagonal_commutes x d
    (diagonal_invariant x) (diagonal_invariant d) t

theorem history_domain (x : diagonal.domain) (t : ℝ) : evolution t (x : H) ∈ maximalAdjoint.domain :=
  Submodule.mem_map.mpr ⟨(evolution t (x : H), evolution t (diagonal x)), history_graph x t, rfl⟩

theorem adjoint_history (x : diagonal.domain) (t : ℝ) :
    maximalAdjoint ⟨evolution t (x : H), history_domain x t⟩ = evolution t (diagonal x) := by
  have hg : (evolution t (x : H), evolution t (diagonal x)) ∈ maximalAdjoint.graph := by
    rw [maximalAdjoint_graph]
    exact history_graph x t
  obtain ⟨u,hu,hvalue⟩ := maximalAdjoint.mem_graph_iff.mp hg
  calc
    _ = maximalAdjoint u := congrArg (fun d : maximalAdjoint.domain => maximalAdjoint d) (Subtype.ext hu.symm)
    _ = _ := hvalue

theorem graph_bound (x : diagonal.domain) (t : ℝ) :
    ‖evolution t (x : H)‖^2 + ‖maximalAdjoint ⟨evolution t (x : H), history_domain x t⟩‖^2 ≤
      ‖(x : H)‖^2 + ‖diagonal x‖^2 := by
  rw [adjoint_history]
  exact add_le_add
    (pow_le_pow_left₀ (norm_nonneg _) (NativeHistoryGrade.history_contraction diagonal diagonal_pair t (x : H)) 2)
    (pow_le_pow_left₀ (norm_nonneg _) (NativeHistoryGrade.history_contraction diagonal diagonal_pair t (diagonal x)) 2)

theorem generated_domain_equation (x : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun u => evolution u (x : H))
      ((-Complex.I) • maximalAdjoint ⟨evolution t (x : H), history_domain x t⟩) t := by
  rw [adjoint_history]
  exact GaussDiagonalGrade.history_derivative x t

def coreStep : diagonal.domain →ₗ[ℂ] diagonal.domain :=
  diagonal.toFun.codRestrict diagonal.domain diagonal_invariant

def iterate (n : ℕ) (x : diagonal.domain) : diagonal.domain := (coreStep^n) x

theorem iterate_step (n : ℕ) (x : diagonal.domain) : diagonal (iterate n x) = (iterate (n+1) x : H) := by
  simp only [iterate, pow_succ', Module.End.mul_apply]
  rfl

def jet (n : ℕ) (t : ℝ) (x : diagonal.domain) : H := evolution t (iterate n x : H)

theorem jet_graph (n : ℕ) (t : ℝ) (x : diagonal.domain) : (jet n t x, jet (n+1) t x) ∈ graph := by
  have h := history_graph (iterate n x) t
  rw [iterate_step] at h
  exact h

theorem jet_derivative (n : ℕ) (t : ℝ) (x : diagonal.domain) :
    HasDerivAt (fun u => jet n u x) ((-Complex.I) • jet (n+1) t x) t := by
  have h := GaussDiagonalGrade.history_derivative (iterate n x) t
  rw [iterate_step] at h
  exact h

theorem jet_bound (n : ℕ) (t : ℝ) (x : diagonal.domain) : ‖jet n t x‖ ≤ ‖(iterate n x : H)‖ :=
  NativeHistoryGrade.history_contraction diagonal diagonal_pair t (iterate n x : H)

theorem history_smooth (x : diagonal.domain) : ContDiff ℝ ∞ (fun t => evolution t (x : H)) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing x with
  | zero =>
      exact contDiff_zero.mpr (NativeHistoryGrade.history_continuous diagonal diagonal_pair diagonal_dense x)
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun t => (GaussDiagonalGrade.history_derivative x t).differentiableAt, ?_, ?_⟩
      · simp
      · have hd : deriv (fun t => evolution t (x : H)) = fun t => (-Complex.I) • evolution t (diagonal x) :=
          funext (fun t => (GaussDiagonalGrade.history_derivative x t).deriv)
        rw [hd]
        exact (ih (coreStep x)).const_smul (-Complex.I)

def twoLeg (n m : ℕ) (t s : ℝ) (x y : diagonal.domain) : ℂ :=
  inner ℂ (jet n t x) (jet m s y)

theorem twoLeg_left (n m : ℕ) (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => twoLeg n m u s x y) (Complex.I * twoLeg (n+1) m t s x y) t := by
  have h := (jet_derivative n t x).inner ℂ (hasDerivAt_const t (jet m s y))
  simpa [twoLeg, inner_smul_left] using h

theorem twoLeg_right (n m : ℕ) (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => twoLeg n m t u x y) (-Complex.I * twoLeg n (m+1) t s x y) s := by
  have h := (hasDerivAt_const s (jet n t x)).inner ℂ (jet_derivative m s y)
  simpa [twoLeg, inner_smul_right] using h

#print axioms maximalAdjoint_graph
#print axioms graph_closed
#print axioms history_domain
#print axioms adjoint_history
#print axioms jet_graph
#print axioms history_smooth
#print axioms twoLeg_left
#print axioms twoLeg_right
end LowEnergy.GaussAdjointHistory
