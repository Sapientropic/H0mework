import H0mework.Versions.R7e4da746.Physics.YangMillsSourceQuantum.Response
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Feature
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Forms.Ground.Lower
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Forms.Symmetry

/-! The original physical-time step is the raw input of the existing energy
graph. Its generated operator is identified with that same physical generator. -/

set_option autoImplicit false
open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.PhysicsCore.YangMills.NativeSource.Energy
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF FullPairing
noncomputable section

def difference : Hilbert →L[ℂ] Hilbert :=
  (Quantum.Time.centered time (-frequency)
    (Multiplicative.ofAdd Observation.darkTime)).toContinuousLinearMap - ContinuousLinearMap.id ℂ Hilbert

def gradient : Hilbert →L[ℂ] Hilbert := (Real.sqrt (frequency / 2) : ℂ) • difference

def differential : Hilbert →ₗ.[ℂ] Hilbert where
  domain := ⊤
  toFun := gradient.toLinearMap.comp (⊤ : Submodule ℂ Hilbert).subtype

theorem differential_closed : differential.IsClosed := by
  have graph : (differential.graph : Set (Hilbert × Hilbert)) =
      {p | p.2 = gradient p.1} := by
    ext p
    constructor
    · intro member
      obtain ⟨v, hv, value⟩ := differential.mem_graph_iff.mp member
      exact value.symm.trans (congrArg gradient hv)
    · intro member
      exact differential.mem_graph_iff.mpr ⟨⟨p.1, Submodule.mem_top⟩, rfl, member.symm⟩
  rw [LinearPMap.IsClosed, graph]
  exact isClosed_eq continuous_snd (gradient.continuous.comp continuous_fst)

theorem differential_dense : Dense (differential.domain : Set Hilbert) := dense_univ

theorem gradient_form (v w : Hilbert) :
    inner ℂ (gradient v) (gradient w) =
      inner ℂ (Quantum.Generator.hamiltonianOperator time (point v) + (frequency : ℂ) • v) w := by
  rw [centered_pairing_response]
  change inner ℂ ((Real.sqrt (frequency/2) : ℂ) • difference v)
    ((Real.sqrt (frequency/2) : ℂ) • difference w) =
      ((frequency/2 : ℝ) : ℂ) * inner ℂ (difference v) (difference w)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, ← pow_two,
    Real.sq_sqrt (div_nonneg Dynamics.frequency_positive.le (by norm_num))]

abbrev hamiltonian := Quantum.Forms.hamiltonian differential differential_closed differential_dense

theorem generated_physical (v : hamiltonian.domain) :
    hamiltonian v = Quantum.Generator.hamiltonianOperator time (point v.val) + (frequency : ℂ) • v.val := by
  apply ext_inner_right ℂ
  intro w
  have source := Quantum.Forms.hamiltonian_form differential differential_closed differential_dense
    v ⟨w, Submodule.mem_top⟩
  have value := Quantum.Forms.derivativePoint_val differential differential_closed differential_dense v
  change inner ℂ (hamiltonian v) w = inner ℂ
    (gradient (Quantum.Forms.derivativePoint differential differential_closed differential_dense v).val)
    (gradient w) at source
  rw [value, gradient_form] at source
  exact source

abbrev resolvent := Quantum.Forms.Graph.resolvent differential differential_closed

theorem gradient_source_zero : gradient normalizedFeature = 0 := by
  have same := Quantum.Time.centered_error time (-frequency) normalizedFeature Observation.darkTime
  have fixed := sub_eq_zero.mp (norm_eq_zero.mp
    (same.trans (normalizedFeature_phase_error Observation.darkTime)))
  change Quantum.Time.centered time (-frequency) (Multiplicative.ofAdd Observation.darkTime)
    normalizedFeature = normalizedFeature at fixed
  change (Real.sqrt (frequency/2) : ℂ) •
    (Quantum.Time.centered time (-frequency) (Multiplicative.ofAdd Observation.darkTime)
      normalizedFeature - normalizedFeature) = 0
  rw [fixed, sub_self, smul_zero]

theorem resolvent_source : resolvent normalizedFeature = normalizedFeature := by
  symm
  apply Quantum.Forms.Graph.Symmetry.solution_unique differential differential_closed
    normalizedFeature ⟨normalizedFeature, Submodule.mem_top⟩
  intro z
  change inner ℂ (normalizedFeature - normalizedFeature) z.val =
    inner ℂ (gradient normalizedFeature) (gradient z.val)
  simp only [sub_self, gradient_source_zero, inner_zero_left]

theorem source_graph_ground :
    ∃ v : hamiltonian.domain, v.val = normalizedFeature ∧ hamiltonian v = 0 := by
  refine ⟨Quantum.Forms.resolventPoint differential differential_closed differential_dense
    normalizedFeature, resolvent_source, ?_⟩
  have generated := Quantum.Forms.resolvent_equation differential differential_closed
    differential_dense normalizedFeature
  rw [resolvent_source] at generated
  exact (add_eq_right.mp generated)

theorem physical_resolvent (v : Hilbert) :
    Quantum.Generator.hamiltonianOperator time (point (resolvent v)) +
      (frequency : ℂ) • resolvent v + resolvent v = v := by
  have generated := Quantum.Forms.resolvent_equation differential differential_closed differential_dense v
  change hamiltonian (Quantum.Forms.resolventPoint differential differential_closed differential_dense v) + resolvent v = v at generated
  rw [generated_physical] at generated
  exact generated

theorem native_approximate (ε : ℝ) (positive : 0 < ε) :
    ∃ v : Hilbert, ‖v‖ = 1 ∧
      ‖Quantum.Generator.hamiltonianOperator time (point v) + (frequency : ℂ) • v -
        (Quantum.Forms.Approximate.energy resolvent : ℂ) • v‖ < ε := by
  obtain ⟨v, unit, small⟩ := Quantum.Forms.Approximate.graph_approximate differential
    differential_closed differential_dense ε positive
  exact ⟨v.val, unit, (generated_physical v) ▸ small⟩

end
end SaturationMonoid.PhysicsCore.YangMills.NativeSource.Energy
