import H0mework.Physics.LowEnergy.Quantum.SourceFamilyHilbert

/-! Uniformly bounded pointwise operators descend through the same family inner product. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.SourceFamilyOperator
open SourceFamilyHilbert Filter
open scoped Topology InnerProductSpace
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

structure Operator (I E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  component : I → E →L[ℂ] E
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, ‖component i x‖ ≤ C*‖x‖

def bound (A : Operator I E) : ℝ := A.bounded.choose
theorem bound_nonneg (A : Operator I E) : 0 ≤ bound A := A.bounded.choose_spec.1
theorem bound_apply (A : Operator I E) (i : I) (x : E) :
    ‖A.component i x‖ ≤ bound A * ‖x‖ := A.bounded.choose_spec.2 i x

def act (u : Ultrafilter I) (A : Operator I E) : Family E u →ₗ[ℂ] Family E u where
  toFun f := ⟨fun i => A.component i (value f i), by
    obtain ⟨D, hD, hf⟩ := f.property
    exact ⟨bound A * D, mul_nonneg (bound_nonneg A) hD, fun i =>
      (bound_apply A i _).trans (mul_le_mul_of_nonneg_left (hf i) (bound_nonneg A))⟩⟩
  map_add' f g := by
    apply Family.ext
    funext i
    exact map_add (A.component i) (value f i) (value g i)
  map_smul' c f := by
    apply Family.ext
    funext i
    exact map_smul (A.component i) c (value f i)

theorem act_bound (u : Ultrafilter I) (A : Operator I E) (f : Family E u) :
    ‖act u A f‖ ≤ bound A * ‖f‖ := by
  have h : ‖act u A f‖^2 ≤ (bound A)^2 * ‖f‖^2 := by
    apply le_of_tendsto_of_tendsto (square_tendsto u (act u A f))
      ((square_tendsto u f).const_mul ((bound A)^2))
    apply Filter.Eventually.of_forall
    intro i
    have hb := bound_apply A i (value f i)
    change ‖A.component i (value f i)‖^2 ≤ (bound A)^2 * ‖value f i‖^2
    nlinarith [norm_nonneg (A.component i (value f i)), norm_nonneg (value f i), bound_nonneg A]
  nlinarith [norm_nonneg (act u A f), mul_nonneg (bound_nonneg A) (norm_nonneg f)]

def core (u : Ultrafilter I) (A : Operator I E) : Family E u →L[ℂ] Family E u :=
  (act u A).mkContinuous (bound A) (act_bound u A)

def lift (u : Ultrafilter I) (A : Operator I E) : Hilbert E u →L[ℂ] Hilbert E u :=
  (UniformSpace.Completion.toComplL.comp (core u A)).extend UniformSpace.Completion.toComplL

theorem lift_coe (u : Ultrafilter I) (A : Operator I E) (f : Family E u) :
    lift u A (f : Hilbert E u) = (act u A f : Hilbert E u) :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) f

theorem ext (u : Ultrafilter I) (A B : Hilbert E u →L[ℂ] Hilbert E u)
    (h : ∀ f : Family E u, A (f : Hilbert E u) = B (f : Hilbert E u)) : A = B := by
  apply ContinuousLinearMap.ext
  exact congrFun (UniformSpace.Completion.denseRange_coe.equalizer A.continuous B.continuous (funext h))

def constant (A : E →L[ℂ] E) : Operator I E :=
  ⟨fun _ => A, ‖A‖, norm_nonneg A, fun _ => A.le_opNorm⟩

def comp (A B : Operator I E) : Operator I E :=
  ⟨fun i => (A.component i).comp (B.component i), bound A * bound B,
    mul_nonneg (bound_nonneg A) (bound_nonneg B), fun i x => by
      calc
        ‖A.component i (B.component i x)‖ ≤ bound A * ‖B.component i x‖ := bound_apply A i _
        _ ≤ bound A * (bound B * ‖x‖) :=
          mul_le_mul_of_nonneg_left (bound_apply B i x) (bound_nonneg A)
        _ = (bound A * bound B) * ‖x‖ := (mul_assoc _ _ _).symm⟩

def add (A B : Operator I E) : Operator I E :=
  ⟨fun i => A.component i + B.component i, bound A + bound B,
    add_nonneg (bound_nonneg A) (bound_nonneg B), fun i x => by
      change ‖A.component i x + B.component i x‖ ≤ _
      calc
        _ ≤ ‖A.component i x‖ + ‖B.component i x‖ := norm_add_le _ _
        _ ≤ bound A*‖x‖ + bound B*‖x‖ := add_le_add (bound_apply A i x) (bound_apply B i x)
        _ = (bound A + bound B)*‖x‖ := (add_mul _ _ _).symm⟩

theorem lift_comp (u : Ultrafilter I) (A B : Operator I E) :
    lift u (comp A B) = (lift u A).comp (lift u B) := by
  apply ext u
  intro f
  rw [ContinuousLinearMap.comp_apply, lift_coe, lift_coe, lift_coe]
  rfl

theorem lift_add (u : Ultrafilter I) (A B : Operator I E) :
    lift u (add A B) = lift u A + lift u B := by
  apply ext u
  intro f
  rw [add_apply, lift_coe, lift_coe, lift_coe, ← UniformSpace.Completion.coe_add]
  rfl

theorem lift_congr (u : Ultrafilter I) (A B : Operator I E)
    (h : ∀ i, A.component i = B.component i) : lift u A = lift u B := by
  apply ext u
  intro f
  rw [lift_coe, lift_coe]
  congr 1
  apply Family.ext
  funext i
  change A.component i (value f i) = B.component i (value f i)
  rw [h i]

theorem lift_identity (u : Ultrafilter I) : lift u (constant (1 : E →L[ℂ] E)) = 1 := by
  apply ext u
  intro f
  rw [lift_coe]
  rfl

theorem lift_constant_embed (u : Ultrafilter I) (A : E →L[ℂ] E) (x : E) :
    lift u (constant A) (embed u x) = embed u (A x) := by
  change lift u (constant A) ((SourceFamilyHilbert.constant u x) : Hilbert E u) = _
  rw [lift_coe]
  rfl

theorem lift_pair (u : Ultrafilter I) (A B : Operator I E)
    (h : ∀ i x y, inner ℂ (A.component i x) y = inner ℂ x (B.component i y))
    (f g : Hilbert E u) : inner ℂ (lift u A f) g = inner ℂ f (lift u B g) := by
  refine UniformSpace.Completion.induction_on₂ f g
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a b
  rw [lift_coe, lift_coe, inner_coe, inner_coe]
  apply tendsto_nhds_unique (pair_tendsto u (act u A a) b)
  convert pair_tendsto u a (act u B b) using 1
  funext i
  exact h i (value a i) (value b i)

theorem lift_isometry (u : Ultrafilter I) (A : Operator I E)
    (h : ∀ i x, ‖A.component i x‖ = ‖x‖) (f : Hilbert E u) : ‖lift u A f‖ = ‖f‖ := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [lift_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  apply tendsto_nhds_unique (norm_tendsto u (act u A a))
  convert norm_tendsto u a using 1
  funext i
  exact h i (value a i)

theorem constant_mul (u : Ultrafilter I) (A B : E →L[ℂ] E) :
    lift u (constant (A*B)) = lift u (constant A) * lift u (constant B) :=
  (lift_congr u _ (comp (constant A) (constant B)) (fun _ => rfl)).trans (lift_comp u _ _)

theorem constant_add (u : Ultrafilter I) (A B : E →L[ℂ] E) :
    lift u (constant (A+B)) = lift u (constant A) + lift u (constant B) :=
  (lift_congr u _ (add (constant A) (constant B)) (fun _ => rfl)).trans (lift_add u _ _)

theorem lift_zero (u : Ultrafilter I) : lift u (constant (0 : E →L[ℂ] E)) = 0 := by
  apply ext u
  intro f
  rw [lift_coe]
  exact UniformSpace.Completion.coe_zero

theorem constant_smul (u : Ultrafilter I) (c : ℂ) (A : E →L[ℂ] E) :
    lift u (constant (c • A)) = c • lift u (constant A) := by
  apply ext u
  intro f
  rw [smul_apply, lift_coe, lift_coe, ← UniformSpace.Completion.coe_smul]
  rfl

theorem orbit_difference {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (J : E →ₗᵢ[ℂ] K) (U V : K →L[ℂ] K)
    (hU : ∀ x, ‖U x‖ = ‖x‖) (hV : ∀ x, ‖V x‖ = ‖x‖) (x y : E) :
    ‖U (J x)-V (J x)‖ ≤ 2*‖x-y‖ + ‖U (J y)-V (J y)‖ := by
  have hi : U (J x)-V (J x) = (U (J (x-y))+(U (J y)-V (J y))) + -(V (J (x-y))) := by
    simp only [map_sub]
    abel
  rw [hi]
  have h := (norm_add_le (U (J (x-y))+(U (J y)-V (J y))) (-(V (J (x-y))))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_neg, hU, hV, J.norm_map] at h
  linarith

end LowEnergy.SourceFamilyOperator
