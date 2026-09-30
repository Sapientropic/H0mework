import H0mework.Physics.MotherProgrammesFormation.Declarations.SmallSupport.Profiles

/-! Exact lift to the completion using only the permitted parents.  This is
a relative mathematical localization theorem; an actual source adapter must
still form the entire finite-parent programme carrier and its reader. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSmallSupport

open Set UniformSpace
open scoped Topology

universe v

noncomputable section

variable {X : Type v} {inside outside : Set X}

def includeRaw (included : inside ⊆ outside) (raw : Raw inside) : Raw outside :=
  ⟨raw.val, by
    obtain ⟨parents, supported, read_eq⟩ := raw.property
    exact ⟨parents, supported.trans included, read_eq⟩⟩

theorem includeRaw_uniformContinuous (included : inside ⊆ outside) :
    UniformContinuous (includeRaw included) :=
  uniformContinuous_subtype_val.subtype_mk _

def includeCompleted (included : inside ⊆ outside) : Formed inside → Formed outside :=
  Completion.map (includeRaw included)

theorem read_includeCompleted (included : inside ⊆ outside) (material : Formed inside) :
    read outside (includeCompleted included material) = read inside material := by
  have same : (fun value => read outside (includeCompleted included value)) = read inside := by
    apply Completion.ext
      (Completion.continuous_extension.comp Completion.continuous_map)
      Completion.continuous_extension
    intro raw
    change read outside (Completion.map (includeRaw included) (raw : Formed inside)) =
      read inside (raw : Formed inside)
    rw [Completion.map_coe (includeRaw_uniformContinuous included), read_coe, read_coe]
    rfl
  exact congrFun same material

/-- The whole original completion value is recovered, not just selected
coordinates of its readout.  Support is the exact condition for this lift. -/
theorem localize (included : inside ⊆ outside) (material : Formed outside)
    (supported : ∀ x, read outside material x = 1 → x ∈ inside) :
    ∃! localMaterial : Formed inside,
      includeCompleted included localMaterial = material := by
  obtain ⟨localMaterial, read_eq, _⟩ := every_supported_profile inside
    (read outside material) ⟨read_binary outside material, supported⟩
  have restored : includeCompleted included localMaterial = material :=
    (read_uniformEmbedding outside).injective
      ((read_includeCompleted included localMaterial).trans read_eq)
  refine ⟨localMaterial, restored, fun other same => ?_⟩
  apply (read_uniformEmbedding inside).injective
  exact (read_includeCompleted included other).symm.trans
    ((congrArg (read outside) same).trans read_eq.symm)

theorem range_includeCompleted (included : inside ⊆ outside) :
    Set.range (includeCompleted included) =
      {material | ∀ x, read outside material x = 1 → x ∈ inside} := by
  ext material
  constructor
  · rintro ⟨localMaterial, rfl⟩ x one
    rw [read_includeCompleted] at one
    by_contra absent
    exact no_new_one inside x absent localMaterial one
  · intro supported
    obtain ⟨localMaterial, restored, _⟩ := localize included material supported
    exact ⟨localMaterial, restored⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSmallSupport
