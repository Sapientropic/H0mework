import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussRadialDomain

/-! The literal H0+Y and its independent H0+Y-adjoint consume the generated source domains. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussFullHamiltonian
open GaussCoreHilbert GaussCoreDifferential GaussYukawaCoefficient GaussYukawaOperator
open GaussNativePotential GaussDiagonalHistory GaussFockPair GaussFockWeights GaussDensityCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussHistoryHilbert SourceQuantumGaugeSliceCoordinates SymmetricGraphClosure MeasureTheory
open scoped ContDiff InnerProductSpace

def adjointLinear : SourceQuantumScalarChart.Scalar →ₗ[ℝ] FockFiber →L[ℂ] FockFiber where
  toFun phi := (sourceMap phi).adjoint
  map_add' phi psi := by rw [map_add, map_add]
  map_smul' r phi := by
    rw [map_smul]
    change ((r : ℂ) • sourceMap phi).adjoint = (r : ℂ) • (sourceMap phi).adjoint
    have h := map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := FockFiber) (F := FockFiber)) (r : ℂ) (sourceMap phi)
    have hr : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := by simp
    rw [hr] at h
    exact h

def adjointMap : SourceQuantumScalarChart.Scalar →L[ℝ] FockFiber →L[ℂ] FockFiber :=
  adjointLinear.toContinuousLinearMap

def adjointAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => adjointMap (scalarField z))
    (fun _ => (adjointMap.contDiff.comp scalarField_smooth).contDiffAt)

theorem yukawa_pair (f g : QuantumTest) :
    sourcePair f (adjointAction g) = sourcePair (originalAction f) g := by
  rw [sourcePair_integral, sourcePair_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change inner ℂ (weight (fun N => complexDensity N z) (f z))
    ((sourceMap (scalarField z)).adjoint (g z)) =
      inner ℂ (weight (fun N => complexDensity N z) (sourceMap (scalarField z) (f z))) (g z)
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hc : Commute (weight (fun N => complexDensity N z)) (sourceMap (scalarField z)) := by
    rw [source_map_return]
    exact GaussQuantumMultiplier.weight_commute _ _
  exact congrArg (fun v : FockFiber => inner ℂ v (g z))
    (congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z)) hc.eq).symm

def fullAction : QuantumTest →ₗ[ℂ] QuantumTest := diagonalAction + originalAction
def sharpAction : QuantumTest →ₗ[ℂ] QuantumTest := diagonalAction + adjointAction

theorem full_action_pair (f g : QuantumTest) : sourcePair f (sharpAction g) = sourcePair (fullAction f) g := by
  simp only [sharpAction, fullAction, LinearMap.add_apply, sourcePair, map_add, inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·) (diagonalAction_pair f g) (yukawa_pair f g)

def native : H →ₗ.[ℂ] H := realize fullAction
def sharp : H →ₗ.[ℂ] H := realize sharpAction

theorem formal_pair : FormalAdjointPair native sharp := by
  intro f g
  obtain ⟨f,rfl⟩ := coreEquiv.surjective f
  obtain ⟨g,rfl⟩ := coreEquiv.surjective g
  change inner ℂ (embed (fullAction (coreEquiv.symm (coreEquiv f)))) (embed g) =
    inner ℂ (embed f) (embed (sharpAction (coreEquiv.symm (coreEquiv g))))
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply]
  exact (full_action_pair f g).symm

theorem native_dense : Dense (native.domain : Set H) := realize_dense fullAction
theorem sharp_dense : Dense (sharp.domain : Set H) := realize_dense sharpAction
theorem native_core (f : native.domain) : native f ∈ native.domain := realize_preserves_core fullAction f
theorem sharp_core (f : sharp.domain) : sharp f ∈ sharp.domain := realize_preserves_core sharpAction f

theorem reversed_pair : FormalAdjointPair sharp native := by
  intro f g
  have h := congrArg (starRingEnd ℂ) (formal_pair g f)
  simpa only [inner_conj_symm] using h.symm

def nativeClosed : H →ₗ.[ℂ] H := closedExtension native sharp sharp_dense formal_pair
def sharpClosed : H →ₗ.[ℂ] H := closedExtension sharp native native_dense reversed_pair

theorem nativeClosed_graph : nativeClosed.graph = native.graph.topologicalClosure :=
  closed_extension_graph native sharp sharp_dense formal_pair

theorem sharpClosed_graph : sharpClosed.graph = sharp.graph.topologicalClosure :=
  closed_extension_graph sharp native native_dense reversed_pair

theorem native_extends : native ≤ nativeClosed := extends_original native sharp sharp_dense formal_pair
theorem sharp_extends : sharp ≤ sharpClosed := extends_original sharp native native_dense reversed_pair

theorem closed_pair : FormalAdjointPair nativeClosed sharpClosed := by
  intro f g
  have hp : ((f : H), nativeClosed f) ∈ closedGraph native := by
    rw [show closedGraph native = nativeClosed.graph from nativeClosed_graph.symm]
    exact nativeClosed.mem_graph f
  have h : Set.EqOn (fun q : H × H => inner ℂ (nativeClosed f) q.1)
      (fun q : H × H => inner ℂ (f : H) q.2) (sharp.graph : Set (H × H)) := by
    intro q hq
    obtain ⟨d,rfl⟩ := sharp.mem_graph_iff'.mp hq
    exact closed_graph_pairing native sharp formal_pair hp d
  have hq : ((g : H), sharpClosed g) ∈ sharp.graph.topologicalClosure := by
    rw [← sharpClosed_graph]
    exact sharpClosed.mem_graph g
  exact h.closure (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd) hq

theorem nativeClosed_minimal (T : H →ₗ.[ℂ] H) (hExtends : native ≤ T)
    (closed : IsClosed (T.graph : Set (H × H))) : nativeClosed ≤ T :=
  minimal_closed_extension native sharp sharp_dense formal_pair T hExtends closed

theorem closed_yukawa_consumed (f : QuantumTest) :
    ∃ hy : embed f ∈ GaussRadialDomain.closedY.domain,
      native (coreEquiv f) = diagonal (coreEquiv f) + GaussRadialDomain.closedY ⟨embed f,hy⟩ := by
  obtain ⟨hy,hY⟩ := GaussRadialDomain.closedY_core f
  refine ⟨hy, ?_⟩
  rw [hY]
  change embed (fullAction (coreEquiv.symm (coreEquiv f))) =
    embed (diagonalAction (coreEquiv.symm (coreEquiv f))) + embed (originalAction f)
  rw [coreEquiv.symm_apply_apply]
  exact map_add embed (diagonalAction f) (originalAction f)

#print axioms yukawa_pair
#print axioms formal_pair
#print axioms native_dense
#print axioms native_core
#print axioms sharp_core
#print axioms nativeClosed_graph
#print axioms sharpClosed_graph
#print axioms closed_pair
#print axioms nativeClosed_minimal
#print axioms closed_yukawa_consumed
end LowEnergy.GaussFullHamiltonian
