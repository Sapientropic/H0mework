import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussYukawaOperator

/-! The source reciprocal radius generates a closed domain for the literal unbounded Y. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussRadialDomain
open GaussCoreHilbert GaussCoreDifferential GaussYukawaCoefficient GaussYukawaOperator GaussFockPair
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open GaussHistoryHilbert SourceQuantumGaugeSliceCoordinates
open scoped ContDiff Topology InnerProductSpace

theorem one_le_radius (z : SourceCoordinateSlice) : 1 ≤ radius z := by
  have hr := Real.sq_sqrt (show 0 ≤ 1+‖(z.2.1 : Scalar)‖^2/4 by positivity)
  change (radius z)^2 = _ at hr
  nlinarith [radius_pos z, sq_nonneg ‖(z.2.1 : Scalar)‖]

def reciprocal (z : SourceCoordinateSlice) : ℝ := (radius z)⁻¹
theorem reciprocal_smooth : ContDiff ℝ ∞ reciprocal := radius_smooth.inv (fun z => (radius_pos z).ne')

def inverseFiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (reciprocal z : ℂ) • ContinuousLinearMap.id ℂ FockFiber

theorem inverse_smooth : ContDiff ℝ ∞ inverseFiber :=
  (Complex.ofRealCLM.contDiff.comp reciprocal_smooth).smul contDiff_const

theorem inverse_commutes (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (inverseFiber z) :=
  (Commute.one_right (GaussFockWeights.weight w)).smul_right (reciprocal z : ℂ)

theorem inverse_bound (z : SourceCoordinateSlice) (f : FockFiber) : ‖inverseFiber z f‖ ≤ 1*‖f‖ := by
  have hc : ‖(reciprocal z : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, reciprocal, abs_of_pos (inv_pos.mpr (radius_pos z))]
    exact inv_le_one_of_one_le₀ (one_le_radius z)
  change ‖(reciprocal z : ℂ) • f‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg f)

def inverseAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  GaussNativeForm.multiply reciprocal (fun _ => reciprocal_smooth.contDiffAt)

def inverseRadius : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension inverseFiber (fun _ => inverse_smooth.contDiffAt)
    (fun z => inverse_commutes z) 1 zero_le_one (fun z => inverse_bound z)

theorem inverse_core (f : QuantumTest) : inverseRadius (embed f) = embed (inverseAction f) :=
  GaussBoundedMultiplier.extension_core inverseFiber (fun _ => inverse_smooth.contDiffAt)
    (fun z => inverse_commutes z) 1 zero_le_one (fun z => inverse_bound z) f

theorem inverse_radius_action (f : QuantumTest) : inverseAction (radiusAction f) = f := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (reciprocal z : ℂ) * (radius z • f z word) = f z word
  rw [Complex.real_smul]
  have hr : (radius z : ℂ) ≠ 0 := by exact_mod_cast (radius_pos z).ne'
  simp only [reciprocal, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]

theorem inverse_radius_core (f : QuantumTest) : inverseRadius (embed (radiusAction f)) = embed f := by
  rw [inverse_core, inverse_radius_action]

theorem inverse_pair (x y : H) : inner ℂ (inverseRadius x) y = inner ℂ x (inverseRadius y) := by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  obtain ⟨f,rfl⟩ := coreEquiv.surjective a
  obtain ⟨g,rfl⟩ := coreEquiv.surjective b
  change inner ℂ (inverseRadius (embed f)) (embed g) = inner ℂ (embed f) (inverseRadius (embed g))
  rw [inverse_core, inverse_core]
  exact (GaussNativeForm.multiply_pair reciprocal (fun _ => reciprocal_smooth.contDiffAt) f g).symm

theorem inverse_dense : DenseRange inverseRadius := by
  apply GaussHistoryHilbert.fockTestDomain_dense.mono
  intro x hx
  obtain ⟨f,hf⟩ := embed_surjective_core ⟨x,hx⟩
  exact ⟨embed (radiusAction f), (inverse_radius_core f).trans hf⟩

theorem inverse_zero (x : H) (hx : inverseRadius x = 0) : x = 0 := by
  have hz : inner ℂ x x = 0 := inverse_dense.induction_on (p := fun z => inner ℂ x z = 0) x
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const) (fun y => by
      rw [← inverse_pair x y, hx, inner_zero_left])
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp hz

theorem inverse_injective : Function.Injective inverseRadius := by
  intro x y h
  apply sub_eq_zero.mp
  apply inverse_zero
  rw [map_sub, h, sub_self]

def graph : Submodule ℂ (H × H) where
  carrier := {p | bounded p.1 = inverseRadius p.2}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq; change bounded (p.1+q.1) = inverseRadius (p.2+q.2); rw [map_add,map_add,hp,hq]
  smul_mem' := by intro c p hp; change bounded (c • p.1) = inverseRadius (c • p.2); rw [map_smul,map_smul,hp]

theorem graph_closed : IsClosed (graph : Set (H × H)) :=
  isClosed_eq (bounded.continuous.comp continuous_fst) (inverseRadius.continuous.comp continuous_snd)

theorem graph_zero (p : H × H) (hp : p ∈ graph) (zero : p.1=0) : p.2=0 := by
  apply inverse_zero
  change bounded p.1 = inverseRadius p.2 at hp
  rw [zero, map_zero] at hp
  exact hp.symm

def closedY : H →ₗ.[ℂ] H := graph.toLinearPMap

theorem closedY_graph : closedY.graph = graph := graph.toLinearPMap_graph_eq graph_zero

theorem original_graph (f : QuantumTest) : (embed f, embed (originalAction f)) ∈ graph := by
  change bounded (embed f) = inverseRadius (embed (originalAction f))
  rw [bounded_core, ← radius_action_return, inverse_radius_core]

theorem closedY_dense : Dense (closedY.domain : Set H) := by
  apply GaussHistoryHilbert.fockTestDomain_dense.mono
  intro x hx
  obtain ⟨f,hf⟩ := embed_surjective_core ⟨x,hx⟩
  exact Submodule.mem_map.mpr ⟨(embed f, embed (originalAction f)), original_graph f, hf⟩

theorem closedY_core (f : QuantumTest) :
    ∃ h : embed f ∈ closedY.domain, closedY ⟨embed f,h⟩ = embed (originalAction f) := by
  have hg : (embed f, embed (originalAction f)) ∈ closedY.graph := by rw [closedY_graph]; exact original_graph f
  obtain ⟨x,hx,hvalue⟩ := closedY.mem_graph_iff.mp hg
  change (x : H) = embed f at hx
  change closedY x = embed (originalAction f) at hvalue
  refine ⟨hx ▸ x.property, ?_⟩
  exact (congrArg (fun v : closedY.domain => closedY v) (Subtype.ext hx.symm)).trans hvalue

#print axioms inverse_dense
#print axioms inverse_injective
#print axioms graph_closed
#print axioms closedY_dense
#print axioms closedY_core
end LowEnergy.GaussRadialDomain
