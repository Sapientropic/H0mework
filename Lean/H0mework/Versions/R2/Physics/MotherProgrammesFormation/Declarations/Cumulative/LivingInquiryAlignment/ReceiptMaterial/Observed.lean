import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.Source

/-! The original action target contains Receipt : Answer → Type (u+3).
This extension changes only the universes of observation/input carriers.
Every finite program still evaluates the original MotherVisit and the same
MotherPointwiseLaws.finiteLaw on its actual finite real coordinates. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptObserved
open Set Filter UniformSpace MotherStreamLaws MotherFamilyOccurrence Stage9C.Revision
open scoped Topology Uniformity UniformConvergence Classical
noncomputable section

universe u v

variable {Input : Type u} {Observation : Type v}

theorem finite_coordinates (observe : Observation → Input → ℝ)
    (separates : Function.Injective (fun input => fun address => observe address input))
    (inputs : Set Input) (finite : inputs.Finite) :
    ∃ n : ℕ, ∃ addresses : Fin n → Observation,
      inputs.InjOn (fun input => fun index => observe (addresses index) input) := by
  let : Fintype inputs := finite.fintype
  let Pairs := {pair : inputs × inputs // pair.1 ≠ pair.2}
  have available (pair : Pairs) :
      ∃ address : Observation, observe address pair.val.1.val ≠ observe address pair.val.2.val := by
    by_contra absent
    push Not at absent
    exact pair.property (Subtype.ext (separates (funext absent)))
  choose address distinguishes using available
  let positions := Fintype.equivFin Pairs
  refine ⟨Fintype.card Pairs, fun index => address (positions.symm index), ?_⟩
  intro first firstIn last lastIn same
  by_contra different
  let pair : Pairs := ⟨(⟨first, firstIn⟩, ⟨last, lastIn⟩),
    fun equal => different (congrArg Subtype.val equal)⟩
  have sampled := congrFun same (positions pair)
  dsimp only at sampled
  rw [positions.symm_apply_apply] at sampled
  exact distinguishes pair sampled

abbrev Programme (Observation : Type v) := Σ n : ℕ, (Fin n → Observation) × MotherVisit

def finiteLaw (observe : Observation → Input → ℝ)
    (programme : Programme Observation) (input : Input) : Stream :=
  MotherPointwiseLaws.finiteLaw programme.2.2
    (pad programme.1 (fun index => observe (programme.2.1 index) input))

theorem finite_approximation (observe : Observation → Input → ℝ)
    (separates : Function.Injective (fun input => fun address => observe address input))
    (inputs : Set Input) (finite : inputs.Finite) (target : Input → Stream)
    (m : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∃ programme : Programme Observation, ∀ input ∈ inputs, ∀ output < m,
      dist (finiteLaw observe programme input output) (target input output) < ε := by
  obtain ⟨n, addresses, separated⟩ := finite_coordinates observe separates inputs finite
  let feature : Input → Stream :=
    fun input => pad n (fun index => observe (addresses index) input)
  have faithful : inputs.InjOn feature := by
    intro first firstIn last lastIn same
    apply separated firstIn lastIn
    funext index
    have sampled := congrFun same index.val
    simpa only [feature, pad, dif_pos index.isLt] using sampled
  let restricted : inputs → Stream := fun input => feature input.val
  have restrictedFaithful : Function.Injective restricted := by
    intro first last same
    exact Subtype.ext (faithful first.property last.property same)
  let : Finite inputs := finite.to_subtype
  let onImage : Stream → Stream :=
    Function.extend restricted (fun input : inputs => target input.val) (fun _ => 0)
  obtain ⟨code, near⟩ := MotherPointwiseLaws.finite_native_approximation
    (Set.range restricted) (Set.finite_range restricted) onImage m ε positive
  refine ⟨⟨n, addresses, SpinPair.visit (10 + code)⟩, ?_⟩
  intro input inside output bound
  have result := near (restricted ⟨input, inside⟩) (Set.mem_range_self _) output bound
  have recovered : onImage (restricted ⟨input, inside⟩) = target input :=
    restrictedFaithful.extend_apply _ _ ⟨input, inside⟩
  rw [recovered] at result
  exact result

theorem pointwise_uniformity_basis (Input : Type u) :
    (𝓤 (Input → Stream)).HasBasis
      (fun index : Set Input × ℕ × ℝ => index.1.Finite ∧ 0 < index.2.2)
      (fun index => {pair : (Input → Stream) × (Input → Stream) |
        ∀ input ∈ index.1, ∀ i < index.2.1,
          dist (pair.1 input i) (pair.2 input i) < index.2.2}) := by
  have basis := UniformOnFun.hasBasis_uniformity_of_basis Input Stream {s | s.Finite}
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => .union) stream_uniformity_basis
  have same := (UniformOnFun.isUniformEmbedding_toFun_finite Input Stream).comap_uniformity
  change Filter.comap id (𝓤 (Input → Stream)) = _ at same
  rw [Filter.comap_id] at same
  rw [← same] at basis
  exact basis

theorem finiteLaw_dense (observe : Observation → Input → ℝ)
    (separates : Function.Injective (fun input => fun address => observe address input)) :
    DenseRange (finiteLaw observe) := by
  intro target
  rw [mem_closure_iff_nhds_basis (nhds_basis_uniformity (pointwise_uniformity_basis Input))]
  rintro ⟨inputs, m, ε⟩ ⟨finite, positive⟩
  obtain ⟨programme, near⟩ := finite_approximation observe separates inputs finite target m ε positive
  exact ⟨finiteLaw observe programme, ⟨programme, rfl⟩, near⟩

abbrev Raw (observe : Observation → Input → ℝ) := Set.range (finiteLaw observe)
abbrev Formed (observe : Observation → Input → ℝ) := Completion (Raw observe)

def read (observe : Observation → Input → ℝ) : Formed observe → Input → Stream :=
  Completion.extension Subtype.val

theorem read_coe (observe : Observation → Input → ℝ) (raw : Raw observe) :
    read observe (raw : Formed observe) = raw.val :=
  Completion.extension_coe uniformContinuous_subtype_val raw

theorem read_uniformEmbedding (observe : Observation → Input → ℝ) : IsUniformEmbedding (read observe) :=
  (Completion.isUniformInducing_extension
    isUniformEmbedding_subtype_val.isUniformInducing).isUniformEmbedding

theorem read_surjective (observe : Observation → Input → ℝ)
    (separates : Function.Injective (fun input => fun address => observe address input)) :
    Function.Surjective (read observe) := by
  have included : Set.range (finiteLaw observe) ⊆ Set.range (read observe) := by
    rintro _ ⟨programme, rfl⟩
    let raw : Raw observe := ⟨finiteLaw observe programme, ⟨programme, rfl⟩⟩
    exact ⟨(raw : Formed observe), read_coe observe raw⟩
  have closed := (read_uniformEmbedding observe).isClosedEmbedding.isClosed_range
  intro target
  exact closure_minimal included closed (finiteLaw_dense observe separates target)


/-- The universe-zero reader is literally the signed existing reader. -/
theorem original_read {Input Observation : Type} (observe : Observation → Input → ℝ) :
    read observe = MotherArenaFormation.Observed.read observe := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptObserved
