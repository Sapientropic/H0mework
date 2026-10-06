import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussRadialMomentum
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.ClosedGraphMultiplier

/-! The literal native momenta consume the source radial bounded commutator. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussRadialMomentumDomain
open GaussCoreHilbert GaussCoreDifferential GaussLiveMomentum GaussMomentumAdjoint
open GaussRadialDomain GaussRadialMomentum SymmetricGraphClosure
open GaussFockPair GaussNativeForm

def closedMomentum (v : Ambient) : H →ₗ.[ℂ] H :=
  closedExtension (GaussCoreHilbert.momentum v) (realizedAdjoint v)
    GaussHistoryHilbert.fockTestDomain_dense (original_formal_adjoint v)

theorem core_graph (v : Ambient) (x : Core) :
    (inverseRadius (x : H), inverseRadius (GaussCoreHilbert.momentum v x)+boundedCommutator v (x : H)) ∈
      (GaussCoreHilbert.momentum v).graph := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective x
  change (inverseRadius (embed f), inverseRadius (GaussCoreHilbert.momentum v (coreEquiv f))+
    boundedCommutator v (embed f)) ∈ _
  rw [momentum_on_test, inverse_core, inverse_core, boundedCommutator_core, ← map_add, ← core_commutator]
  have h := (GaussCoreHilbert.momentum v).mem_graph (coreEquiv (inverseAction f))
  rw [momentum_on_test] at h
  exact h

theorem closed_graph (v : Ambient) (x : (closedMomentum v).domain) :
    (inverseRadius (x : H), inverseRadius (closedMomentum v x)+boundedCommutator v (x : H)) ∈
      (closedMomentum v).graph :=
  ClosedGraphMultiplier.closed_preserved (GaussCoreHilbert.momentum v) (realizedAdjoint v)
    GaussHistoryHilbert.fockTestDomain_dense (original_formal_adjoint v)
    inverseRadius (boundedCommutator v) (core_graph v) x

theorem closed_domain (v : Ambient) (x : (closedMomentum v).domain) :
    inverseRadius (x : H) ∈ (closedMomentum v).domain :=
  (ClosedGraphMultiplier.closed_value _ _ _ x (closed_graph v x)).choose

theorem closed_commutator (v : Ambient) (x : (closedMomentum v).domain) :
    closedMomentum v ⟨inverseRadius (x : H),closed_domain v x⟩ =
      inverseRadius (closedMomentum v x)+boundedCommutator v (x : H) :=
  (ClosedGraphMultiplier.closed_value _ _ _ x (closed_graph v x)).choose_spec

theorem inverse_contraction (x : H) : ‖inverseRadius x‖ ≤ ‖x‖ := by
  have h := GaussBoundedMultiplier.extension_norm inverseFiber (fun _ => inverse_smooth.contDiffAt)
    (fun z => inverse_commutes z) 1 zero_le_one (fun z => inverse_bound z)
  exact ((inverseRadius).le_opNorm x).trans ((mul_le_mul_of_nonneg_right h (norm_nonneg x)).trans_eq (one_mul _))

theorem closed_graph_bound (v : Ambient) (x : (closedMomentum v).domain) :
    ‖closedMomentum v ⟨inverseRadius (x : H),closed_domain v x⟩‖ ≤
      ‖closedMomentum v x‖+(‖v.1‖/2)*‖(x : H)‖ :=
  ClosedGraphMultiplier.graph_bound (closedMomentum v) inverseRadius (boundedCommutator v)
    inverse_contraction (‖v.1‖/2)
    (fun y => ((boundedCommutator v).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (boundedCommutator_norm v) (norm_nonneg y)))
    x (closed_domain v x) (closed_commutator v x)

theorem gauge_commutator_zero (v : Ambient) (hv : v.1=0) : boundedCommutator v=0 := by
  apply norm_le_zero_iff.mp
  simpa only [hv,norm_zero,zero_div] using boundedCommutator_norm v

theorem gauge_closed_commutes (v : Ambient) (hv : v.1=0) (x : (closedMomentum v).domain) :
    closedMomentum v ⟨inverseRadius (x : H),closed_domain v x⟩ = inverseRadius (closedMomentum v x) := by
  rw [closed_commutator,gauge_commutator_zero v hv,zero_apply,add_zero]

theorem commutatorAction_pair (v : Ambient) (f g : QuantumTest) :
    sourcePair f (commutatorAction v g) = -sourcePair (commutatorAction v f) g := by
  have hK : commutatorAction v = (-Complex.I) •
      multiply (radialDerivative v) (fun _ => (radialDerivative_smooth v).contDiffAt) := by
    apply LinearMap.ext
    intro a
    apply DFunLike.ext
    intro z
    apply PiLp.ext
    intro word
    change ((-Complex.I)*(radialDerivative v z : ℂ))*a z word =
      (-Complex.I)*((radialDerivative v z : ℂ)*a z word)
    exact mul_assoc _ _ _
  rw [hK]
  change inner ℂ (embed f) (embed ((-Complex.I) • _)) =
    -inner ℂ (embed ((-Complex.I) • _)) (embed g)
  rw [map_smul,map_smul,inner_smul_right,inner_smul_left]
  change (-Complex.I)*sourcePair f (multiply _ _ g) = _
  rw [multiply_pair]
  simp only [map_neg,Complex.conj_I,neg_neg,neg_mul]
  rfl

private theorem test_pair_ext (f g : QuantumTest)
    (h : ∀ a, sourcePair a f=sourcePair a g) : f=g := by
  have hz : inner ℂ (embed (f-g)) (embed (f-g)) = 0 := by
    calc
      _ = sourcePair (f-g) f-sourcePair (f-g) g := by
        conv_lhs => rw [show embed (f-g)=embed f-embed g from map_sub embed f g]
        exact inner_sub_right _ _ _
      _ = 0 := sub_eq_zero.mpr (h (f-g))
  have he := (inner_self_eq_zero (𝕜 := ℂ)).mp hz
  apply sub_eq_zero.mp
  exact embed_injective (he.trans (map_zero embed).symm)

theorem adjoint_core_commutator (v : Ambient) (g : QuantumTest) :
    adjoint v (inverseAction g) = inverseAction (adjoint v g)+commutatorAction v g := by
  apply test_pair_ext
  intro f
  have h1 := adjoint_pair v f (inverseAction g)
  have h2 := multiply_pair reciprocal (fun _ => reciprocal_smooth.contDiffAt) (covariantMomentum v f) g
  have h3 := adjoint_pair v (inverseAction f) g
  have h4 := multiply_pair reciprocal (fun _ => reciprocal_smooth.contDiffAt) f (adjoint v g)
  have h5 := commutatorAction_pair v f g
  rw [core_commutator] at h3
  change sourcePair (inverseAction f) (adjoint v g) =
    inner ℂ (embed (inverseAction (covariantMomentum v f)+commutatorAction v f)) (embed g) at h3
  rw [map_add,inner_add_left] at h3
  change sourcePair f (adjoint v (inverseAction g)) =
    inner ℂ (embed f) (embed (inverseAction (adjoint v g)+commutatorAction v g))
  rw [map_add,inner_add_right]
  change _ = sourcePair f (inverseAction (adjoint v g))+sourcePair f (commutatorAction v g)
  change sourcePair (covariantMomentum v f) (inverseAction g) =
    sourcePair (inverseAction (covariantMomentum v f)) g at h2
  change sourcePair f (inverseAction (adjoint v g)) = sourcePair (inverseAction f) (adjoint v g) at h4
  rw [h1,h2,h4,h3,h5]
  unfold sourcePair
  ring

theorem reverse_pair (v : Ambient) :
    FormalAdjointPair (realizedAdjoint v) (GaussCoreHilbert.momentum v) := by
  intro f g
  have h := congrArg (starRingEnd ℂ) (original_formal_adjoint v g f)
  rw [inner_conj_symm,inner_conj_symm] at h
  exact h.symm

def closedAdjoint (v : Ambient) : H →ₗ.[ℂ] H :=
  closedExtension (realizedAdjoint v) (GaussCoreHilbert.momentum v)
    GaussHistoryHilbert.fockTestDomain_dense (reverse_pair v)

private theorem adjoint_on_test (v : Ambient) (f : QuantumTest) :
    realizedAdjoint v (coreEquiv f) = embed (adjoint v f) := by
  change embed (adjoint v (coreEquiv.symm (coreEquiv f))) = _
  rw [coreEquiv.symm_apply_apply]

theorem adjoint_core_graph (v : Ambient) (x : Core) :
    (inverseRadius (x : H), inverseRadius (realizedAdjoint v x)+boundedCommutator v (x : H)) ∈
      (realizedAdjoint v).graph := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective x
  change (inverseRadius (embed f), inverseRadius (realizedAdjoint v (coreEquiv f))+
    boundedCommutator v (embed f)) ∈ _
  rw [adjoint_on_test,inverse_core,inverse_core,boundedCommutator_core,← map_add,← adjoint_core_commutator]
  have h := (realizedAdjoint v).mem_graph (coreEquiv (inverseAction f))
  rw [adjoint_on_test] at h
  exact h

theorem adjoint_closed_graph (v : Ambient) (x : (closedAdjoint v).domain) :
    (inverseRadius (x : H), inverseRadius (closedAdjoint v x)+boundedCommutator v (x : H)) ∈
      (closedAdjoint v).graph :=
  ClosedGraphMultiplier.closed_preserved (realizedAdjoint v) (GaussCoreHilbert.momentum v)
    GaussHistoryHilbert.fockTestDomain_dense (reverse_pair v)
    inverseRadius (boundedCommutator v) (adjoint_core_graph v) x

#print axioms closed_graph
#print axioms closed_commutator
#print axioms closed_graph_bound
#print axioms gauge_closed_commutes
#print axioms adjoint_core_commutator
#print axioms adjoint_closed_graph
end LowEnergy.GaussRadialMomentumDomain
