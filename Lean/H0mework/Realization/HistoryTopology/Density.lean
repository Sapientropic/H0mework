import H0mework.Realization.HistoryTopology.Carrier
import H0mework.Realization.ScalarCofinal.FiniteLift

/-!
# Density of the original source in its observation completion

Every observation neighborhood contains a finite coordinate cylinder. The one
Generator representative supplied by finite lifting hits that cylinder in the
existing completion, without selecting a native state or a whole future table.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalTopology

open CategoryTheory SourceGeneratedScalarCofinalKernelCompletion
open Filter Set Topology

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {Carrier : Nat → Type u} [∀ stage, AddCommGroup (Carrier stage)]
variable [∀ stage, Module R (Carrier stage)]
variable (data : Data (R := R) (Generator := Generator) (Carrier := Carrier))
variable (compatible : data.Compatible)

theorem finite_cylinder_of_mem_nhds (point : data.Completion compatible)
    {neighborhood : Set (data.Completion compatible)}
    (near : neighborhood ∈ @nhds _ (observationUniform data compatible).toTopologicalSpace point) :
    ∃ stages : Finset Nat, ∀ value : data.Completion compatible,
      (∀ stage ∈ stages, coordinates data compatible value stage =
        coordinates data compatible point stage) → value ∈ neighborhood := by
  let : ∀ stage, UniformSpace (data.StageQuotient stage) := stageUniform data
  let : UniformSpace (data.Completion compatible) := observationUniform data compatible
  have inducing := (coordinates_isUniformEmbedding data compatible).isUniformInducing.isInducing
  rw [inducing.nhds_eq_comap point] at near
  obtain ⟨ambient, ambientNear, preimage⟩ := Filter.mem_comap.mp near
  rw [nhds_pi] at ambientNear
  obtain ⟨stages, slices, sliceNear, contained⟩ := Filter.mem_pi'.mp ambientNear
  refine ⟨stages, ?_⟩
  intro value agrees
  apply preimage
  apply contained
  intro stage member
  rw [agrees stage (Finset.mem_coe.mp member)]
  exact mem_of_mem_nhds (sliceNear stage)

theorem completionMap_denseRange :
    @DenseRange (data.Completion compatible) (observationUniform data compatible).toTopologicalSpace
      Generator (data.completionMap compatible) := by
  let : UniformSpace (data.Completion compatible) := observationUniform data compatible
  intro point
  apply mem_closure_iff_nhds.mpr
  intro neighborhood near
  obtain ⟨stages, inside⟩ := finite_cylinder_of_mem_nhds data compatible point near
  obtain ⟨source, agreement⟩ := data.finset_lift compatible point stages
  refine ⟨data.completionMap compatible source, ⟨?_, ⟨source, rfl⟩⟩⟩
  apply inside
  intro stage member
  rw [coordinates_source]
  exact agreement stage member

end

end SourceGeneratedScalarCofinalTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
