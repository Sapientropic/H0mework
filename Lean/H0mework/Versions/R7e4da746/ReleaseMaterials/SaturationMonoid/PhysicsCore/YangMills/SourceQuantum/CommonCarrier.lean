import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Source.Time
import H0mework.Versions.R7e4da746.Physics.YangMillsSourceQuantum.Time

/-! Full mother-action words, the occupied source and original physical time
share one carrier. This is the original full-matter response carrier; pure
Yang--Mills field content and its spacetime axioms are separate consumers. -/

set_option autoImplicit false
open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.PhysicsCore.YangMills.NativeSource.CommonCarrier
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF
open FullPairing
noncomputable section

abbrev Space := Quantum.Source.Carrier (prepared 0)

def realization : Space ≃ₗᵢ[ℂ] Hilbert :=
  Quantum.Source.realization (prepared 0) (prepared_norm 0)

def vector (A : Mother) : Space := Quantum.Source.vector (prepared 0) (operator A)

theorem vector_readback (A : Mother) : realization (vector A) = operator A (prepared 0) :=
  Quantum.Source.realization_vector (prepared 0) (prepared_norm 0) (operator A)

theorem vector_surjective : Function.Surjective vector := by
  intro x
  obtain ⟨A, rfl⟩ := Quantum.Source.vector_surjective (prepared 0) (prepared_norm 0) x
  refine ⟨fromOperator A, ?_⟩
  rw [vector, operator_fromOperator]

def action (A : Mother) : Space →L[ℂ] Space :=
  Quantum.Source.action (prepared 0) (prepared_norm 0) (operator A)

theorem action_readback (A : Mother) (x : Space) :
    realization (action A x) = operator A (realization x) :=
  Quantum.Source.realization_action (prepared 0) (prepared_norm 0) (operator A) x

def preparation (p : BasePoint) : Space := realization.symm (prepared p)

theorem preparation_readback (p : BasePoint) : realization (preparation p) = prepared p :=
  realization.apply_symm_apply _

theorem source_pairing (p : BasePoint) (A B : Mother) :
    inner ℂ (action A (preparation p)) (action B (preparation p)) =
      State.vectorEvaluation (Stage10.Runtime.tick.answer p)
        (Compatibility.responseMatrix (pairedMother A B)) := by
  rw [← realization.inner_map_map, action_readback, action_readback,
    preparation_readback]
  exact (source_gram p A B).symm

theorem original_mother_response (A : Mother) :
    inner ℂ (preparation 0) (action A (preparation 0)) =
      State.vectorEvaluation (Stage10.Runtime.tick.answer 0) (Compatibility.responseMatrix A) := by
  rw [← realization.inner_map_map, action_readback, preparation_readback]
  exact (origin_response A).symm

theorem all_words (word : List Mother) :
    (word.map action).prod (Quantum.Source.vector (prepared 0) 1) =
      Quantum.Source.vector (prepared 0) (word.map operator).prod := by
  induction word with
  | nil => rfl
  | cons A word ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
      rw [ih]
      exact Quantum.Source.action_vector (prepared 0) (prepared_norm 0) (operator A) _

def evolution : Multiplicative ℝ →* (Space ≃ₗᵢ[ℂ] Space) :=
  Quantum.Source.time (prepared 0) (prepared_norm 0) NativeSource.time

theorem evolution_readback (t : Multiplicative ℝ) (x : Space) :
    realization (evolution t x) = NativeSource.time t (realization x) :=
  Quantum.Source.realization_time (prepared 0) (prepared_norm 0) NativeSource.time t x

theorem evolves_original_preparation (p : BasePoint) (t : ℝ) :
    evolution (Multiplicative.ofAdd t) (preparation p) =
      preparation (p + Dynamics.timeDisplacement t) := by
  apply realization.injective
  rw [evolution_readback, preparation_readback, preparation_readback]
  exact time_prepared p t

theorem evolution_continuous (x : Space) : Continuous (Quantum.Generator.orbit evolution x) :=
  Quantum.Source.time_continuous (prepared 0) (prepared_norm 0) NativeSource.time time_continuous x

theorem original_physical_derivative (p : BasePoint) (t : ℝ) :
    HasDerivAt (fun r => preparation (p + Dynamics.timeDisplacement r))
      (realization.symm (quantumFeature (fun i =>
        Stage10.Runtime.tick.answer (p + Dynamics.timeDisplacement t) i * Dynamics.generator i))) t := by
  let lift := realization.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have carried := lift.hasFDerivAt.comp_hasDerivAt t (original_physical_input p t)
  convert! carried using 1
  funext r
  rw [Stage10.Runtime.tick_vector]
  rfl

def hamiltonian : Space →ₗ.[ℂ] Space := Quantum.Generator.hamiltonianOperator evolution

theorem hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian :=
  Quantum.Generator.hamiltonianOperator_selfAdjoint evolution evolution_continuous

theorem domain_iff (x : Space) :
    realization x ∈ (Quantum.Generator.hamiltonianOperator NativeSource.time).domain ↔
      x ∈ hamiltonian.domain :=
  Quantum.Source.domain_iff (prepared 0) (prepared_norm 0) NativeSource.time x

def domainPoint (x : hamiltonian.domain) : (Quantum.Generator.hamiltonianOperator NativeSource.time).domain :=
  Quantum.Source.domainPoint (prepared 0) (prepared_norm 0) NativeSource.time x

theorem hamiltonian_readback (x : hamiltonian.domain) :
    realization (hamiltonian x) = Quantum.Generator.hamiltonianOperator NativeSource.time (domainPoint x) :=
  Quantum.Source.hamiltonian_readback (prepared 0) (prepared_norm 0) NativeSource.time x

theorem energy_readback (x : hamiltonian.domain) :
    inner ℂ (hamiltonian x) x.val =
      inner ℂ (Quantum.Generator.hamiltonianOperator NativeSource.time (domainPoint x)) (realization x.val) :=
  Quantum.Source.energy_readback (prepared 0) (prepared_norm 0) NativeSource.time x

end
end SaturationMonoid.PhysicsCore.YangMills.NativeSource.CommonCarrier
