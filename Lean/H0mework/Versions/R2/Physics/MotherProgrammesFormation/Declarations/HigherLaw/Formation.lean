import H0mework.Versions.R2.Physics.MotherDeclarationsType.FormationSource

/-! The existing complete physical law is the operand of a further source-generated law.
Finite programmes observe it through mother material addresses; completion forms the
whole higher function space. This is a subordinate type-formation producer. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHigherLawFormation

open Set Filter UniformSpace MotherStreamLaws MotherFamilyOccurrence Stage9C.Revision
open scoped Topology Uniformity UniformConvergence

noncomputable section

abbrev Base := MotherPhysicalLaws.Law
abbrev Address := MotherTypeFormation.MemberMaterial × ℕ

def observe (address : Address) (base : Base) : ℝ :=
  MotherPhysicalLaws.eval base (MotherTypeFormation.memberInput address.1) address.2

theorem memberInput_surjective : Function.Surjective MotherTypeFormation.memberInput := by
  rintro ⟨current, value⟩
  obtain ⟨currentMaterial, _, currentRead⟩ := MotherRawCurrent.every_current current
  obtain ⟨valueMaterial, valueRead⟩ := MotherStreamFormation.read_surjective value
  refine ⟨(currentMaterial, valueMaterial), ?_⟩
  exact Prod.ext currentRead valueRead

theorem observations_injective :
    Function.Injective (fun base : Base => fun address => observe address base) := by
  intro first last same
  apply MotherPhysicalLaws.lawRead_uniformEmbedding.injective
  funext input index
  obtain ⟨material, formed⟩ := memberInput_surjective input
  have agrees := congrFun same (material, index)
  simpa only [observe, formed, MotherPhysicalLaws.eval_eq] using agrees

theorem finite_coordinates (K : Set Base) (finite : K.Finite) :
    ∃ n : ℕ, ∃ addresses : Fin n → Address,
      K.InjOn (fun base => fun index => observe (addresses index) base) := by
  classical
  let : Fintype K := finite.fintype
  have pairwise (pair : K × K) : ∃ address : Address,
      pair.1.val ≠ pair.2.val → observe address pair.1.val ≠ observe address pair.2.val := by
    by_cases different : pair.1.val ≠ pair.2.val
    · have separated : ∃ address, observe address pair.1.val ≠ observe address pair.2.val := by
        by_contra absent
        push Not at absent
        exact different (observations_injective (funext absent))
      obtain ⟨address, separates⟩ := separated
      exact ⟨address, fun _ => separates⟩
    · obtain ⟨valueMaterial, _⟩ := MotherStreamFormation.read_surjective 0
      exact ⟨((MotherPointwiseLaws.ofVisit (SpinPair.visit 10), valueMaterial), 0),
        fun contradiction => False.elim (different contradiction)⟩
  choose address separatesPair using pairwise
  let positions := Fintype.equivFin (K × K)
  refine ⟨Fintype.card (K × K), fun index => address (positions.symm index), ?_⟩
  intro first firstIn last lastIn same
  by_contra different
  let pair : K × K := (⟨first, firstIn⟩, ⟨last, lastIn⟩)
  have agrees := congrFun same (positions pair)
  dsimp only at agrees
  rw [positions.symm_apply_apply] at agrees
  exact separatesPair pair different agrees

abbrev Programme := Σ n : ℕ, (Fin n → Address) × MotherVisit

def finiteLaw (programme : Programme) (base : Base) : Stream :=
  MotherPointwiseLaws.finiteLaw programme.2.2
    (pad programme.1 (fun index => observe (programme.2.1 index) base))

theorem finite_approximation (K : Set Base) (finite : K.Finite)
    (target : Base → Stream) (m : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∃ programme : Programme, ∀ base ∈ K, ∀ output < m,
      dist (finiteLaw programme base output) (target base output) < ε := by
  obtain ⟨n, addresses, separated⟩ := finite_coordinates K finite
  let feature : Base → Stream := fun base => pad n (fun index => observe (addresses index) base)
  have faithful : K.InjOn feature := by
    intro first firstIn last lastIn same
    apply separated firstIn lastIn
    funext index
    have sampled := congrFun same index.val
    simpa only [feature, pad, dif_pos index.isLt] using sampled
  let restricted : K → Stream := fun base => feature base.val
  have restrictedFaithful : Function.Injective restricted := by
    intro first last same
    exact Subtype.ext (faithful first.property last.property same)
  let : Finite K := finite.to_subtype
  let onImage : Stream → Stream :=
    Function.extend restricted (fun base : K => target base.val) (fun _ => 0)
  obtain ⟨code, near⟩ := MotherPointwiseLaws.finite_native_approximation
    (Set.range restricted) (Set.finite_range restricted) onImage m ε positive
  refine ⟨⟨n, addresses, SpinPair.visit (10 + code)⟩, ?_⟩
  intro base inside output bound
  have result := near (restricted ⟨base, inside⟩) (Set.mem_range_self _) output bound
  have recovered : onImage (restricted ⟨base, inside⟩) = target base :=
    restrictedFaithful.extend_apply _ _ ⟨base, inside⟩
  rw [recovered] at result
  exact result

theorem pointwise_uniformity_basis :
    (𝓤 (Base → Stream)).HasBasis
      (fun index : Set Base × ℕ × ℝ => index.1.Finite ∧ 0 < index.2.2)
      (fun index => {pair : (Base → Stream) × (Base → Stream) |
        ∀ base ∈ index.1, ∀ i < index.2.1,
          dist (pair.1 base i) (pair.2 base i) < index.2.2}) := by
  have basis := UniformOnFun.hasBasis_uniformity_of_basis Base Stream {s | s.Finite}
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => .union) stream_uniformity_basis
  have same := (UniformOnFun.isUniformEmbedding_toFun_finite Base Stream).comap_uniformity
  change Filter.comap id (𝓤 (Base → Stream)) = _ at same
  rw [Filter.comap_id] at same
  rw [← same] at basis
  exact basis

theorem finiteLaw_dense : DenseRange finiteLaw := by
  intro target
  rw [mem_closure_iff_nhds_basis (nhds_basis_uniformity pointwise_uniformity_basis)]
  rintro ⟨K, m, ε⟩ ⟨finite, positive⟩
  obtain ⟨programme, near⟩ := finite_approximation K finite target m ε positive
  exact ⟨finiteLaw programme, ⟨programme, rfl⟩, near⟩

abbrev Raw := Set.range finiteLaw
abbrev Formed := Completion Raw

def read : Formed → (Base → Stream) := Completion.extension Subtype.val

theorem read_coe (raw : Raw) : read (raw : Formed) = raw.val :=
  Completion.extension_coe uniformContinuous_subtype_val raw

theorem read_uniformEmbedding : IsUniformEmbedding read :=
  (Completion.isUniformInducing_extension
    isUniformEmbedding_subtype_val.isUniformInducing).isUniformEmbedding

/-- The completed finite source operations form every whole law-valued-input operation. -/
theorem read_surjective : Function.Surjective read := by
  have included : Set.range finiteLaw ⊆ Set.range read := by
    rintro _ ⟨programme, rfl⟩
    let raw : Raw := ⟨finiteLaw programme, ⟨programme, rfl⟩⟩
    exact ⟨(raw : Formed), read_coe raw⟩
  have closed := read_uniformEmbedding.isClosedEmbedding.isClosed_range
  intro target
  exact closure_minimal included closed (finiteLaw_dense target)

/-- The new source-formed carrier strictly exceeds the previous complete law carrier. -/
theorem strict_growth (enumerate : Base → Formed) : ¬Function.Surjective enumerate := by
  intro all
  obtain ⟨diagonal, formed⟩ := read_surjective (fun base => fun index => read (enumerate base) base index + 1)
  obtain ⟨base, same⟩ := all diagonal
  have differs := congrFun (congrFun formed base) 0
  rw [← same] at differs
  linarith

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHigherLawFormation
