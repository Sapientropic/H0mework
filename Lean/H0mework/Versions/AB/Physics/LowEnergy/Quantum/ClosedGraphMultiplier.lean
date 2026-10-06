import H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure

/-! Bounded commutators carry the original graph closure into itself. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ClosedGraphMultiplier
open SymmetricGraphClosure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem closure_preserved (T : E →ₗ.[ℂ] E) (S K : E →L[ℂ] E)
    (core : ∀ x : T.domain, (S (x : E), S (T x)+K (x : E)) ∈ T.graph)
    {p : E × E} (hp : p ∈ closedGraph T) :
    (S p.1, S p.2+K p.1) ∈ closedGraph T := by
  let F : E × E → E × E := fun q => (S q.1, S q.2+K q.1)
  have hc : Continuous F := (S.continuous.comp continuous_fst).prodMk
    ((S.continuous.comp continuous_snd).add (K.continuous.comp continuous_fst))
  have h : closure (T.graph : Set (E × E)) ⊆ F ⁻¹' (closedGraph T : Set (E × E)) := by
    apply closure_minimal
    · intro q hq
      obtain ⟨x,rfl⟩ := T.mem_graph_iff'.mp hq
      exact T.graph.le_topologicalClosure (core x)
    · exact T.graph.isClosed_topologicalClosure.preimage hc
  exact h hp

theorem closed_preserved (T R : E →ₗ.[ℂ] E)
    (dense : Dense (R.domain : Set E)) (pair : FormalAdjointPair T R)
    (S K : E →L[ℂ] E)
    (core : ∀ x : T.domain, (S (x : E), S (T x)+K (x : E)) ∈ T.graph)
    (x : (closedExtension T R dense pair).domain) :
    (S (x : E), S (closedExtension T R dense pair x)+K (x : E)) ∈
      (closedExtension T R dense pair).graph := by
  rw [closed_extension_graph]
  apply closure_preserved T S K core (p := ((x : E), closedExtension T R dense pair x))
  simpa only [closed_extension_graph] using (closedExtension T R dense pair).mem_graph x

theorem closed_value (T : E →ₗ.[ℂ] E) (S K : E →L[ℂ] E) (x : T.domain)
    (graph : (S (x : E), S (T x)+K (x : E)) ∈ T.graph) :
    ∃ h : S (x : E) ∈ T.domain,
      T ⟨S (x : E),h⟩ = S (T x)+K (x : E) := by
  obtain ⟨y,hy,hvalue⟩ := T.mem_graph_iff.mp graph
  change (y : E) = S (x : E) at hy
  change T y = _ at hvalue
  refine ⟨hy ▸ y.property, ?_⟩
  exact (congrArg (fun v : T.domain => T v) (Subtype.ext hy.symm)).trans hvalue

theorem graph_bound (T : E →ₗ.[ℂ] E) (S K : E →L[ℂ] E)
    (boundS : ∀ x, ‖S x‖ ≤ ‖x‖) (C : ℝ) (boundK : ∀ x, ‖K x‖ ≤ C*‖x‖)
    (x : T.domain) (h : S (x : E) ∈ T.domain)
    (value : T ⟨S (x : E),h⟩ = S (T x)+K (x : E)) :
    ‖T ⟨S (x : E),h⟩‖ ≤ ‖T x‖+C*‖(x : E)‖ := by
  rw [value]
  exact (norm_add_le _ _).trans (add_le_add (boundS _) (boundK _))

#print axioms closure_preserved
#print axioms closed_preserved
end LowEnergy.ClosedGraphMultiplier
