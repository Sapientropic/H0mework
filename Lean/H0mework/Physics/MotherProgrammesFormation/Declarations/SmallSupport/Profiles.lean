import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Finset.Filter


/-! Support-local completion of finite parent profiles. This module is a
mathematical formation mechanism; the support parameter and ambient ZFSet
do not assert that its raw parent carrier has mother-source provenance. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSmallSupport

open Set UniformSpace
open scoped Topology Classical

universe u v
noncomputable section

section Profiles

variable {X : Type v}

/-- Actual finite membership observation: only the listed parents can read 1. -/
def finiteProfile (parents : Finset X) (x : X) : ℝ := by
  classical
  exact if x ∈ parents then 1 else 0

/-- Finite observations whose actual parents all lie in D. -/
abbrev Raw (D : Set X) :=
  { f : X → ℝ // ∃ parents : Finset X,
      (↑parents : Set X) ⊆ D ∧ finiteProfile parents = f }

abbrev Formed (D : Set X) := Completion (Raw D)

def read (D : Set X) : Formed D → X → ℝ :=
  Completion.extension Subtype.val

theorem read_coe (D : Set X) (raw : Raw D) :
    read D (raw : Formed D) = raw.val :=
  Completion.extension_coe uniformContinuous_subtype_val raw

theorem raw_zero_outside (D : Set X) (raw : Raw D)
    (x : X) (outside : x ∉ D) : raw.val x = 0 := by
  classical
  obtain ⟨parents, inside, same⟩ := raw.property
  have absent : x ∉ parents := fun h => outside (inside h)
  rw [← same]
  simp only [finiteProfile, if_neg absent]

/-- The crucial negative control: completion cannot invent an absent parent. -/
theorem read_zero_outside (D : Set X) (x : X) (outside : x ∉ D)
    (material : Formed D) : read D material x = 0 := by
  have same : (fun value : Formed D => read D value x) =
      (fun _ : Formed D => (0 : ℝ)) := by
    apply Completion.ext
      ((continuous_apply x).comp Completion.continuous_extension)
      continuous_const
    intro raw
    change read D (raw : Formed D) x = 0
    rw [read_coe]
    exact raw_zero_outside D raw x outside
  exact congrFun same material

theorem no_new_one (D : Set X) (x : X) (outside : x ∉ D)
    (material : Formed D) : read D material x ≠ 1 := by
  intro one
  have impossible : (0 : ℝ) = 1 :=
    (read_zero_outside D x outside material).symm.trans one
  exact zero_ne_one impossible

/-- Positive half of support-local density. A target occurs only in this proof.
Every finite observation is matched using parents in B, hence in D. -/
theorem finite_assignment (D B : Set X) (included : B ⊆ D)
    (observed : Finset X) :
    ∃ raw : Raw D, ∀ x ∈ observed,
      raw.val x = (if x ∈ B then (1 : ℝ) else 0) := by
  classical
  let parents := observed.filter (fun x => x ∈ B)
  have inside : (↑parents : Set X) ⊆ D := by
    intro x hx
    exact included (Finset.mem_filter.mp hx).2
  refine ⟨⟨finiteProfile parents, parents, inside, rfl⟩, ?_⟩
  intro x hx
  change finiteProfile parents x = _
  by_cases member : x ∈ B
  · simp [finiteProfile, parents, hx, member]
  · simp [finiteProfile, parents, hx, member]

/-- Completion stays in the closed binary-valued subspace. -/
theorem read_binary (D : Set X) (material : Formed D) (x : X) :
    read D material x = 0 ∨ read D material x = 1 := by
  have continuousEval : Continuous (fun value : Formed D => read D value x) :=
    (continuous_apply x).comp Completion.continuous_extension
  refine Completion.induction_on material ?_ ?_
  · exact (isClosed_eq continuousEval continuous_const).union
      (isClosed_eq continuousEval continuous_const)
  · intro raw
    obtain ⟨parents, _, same⟩ := raw.property
    rw [read_coe, ← same]
    classical
    by_cases member : x ∈ parents
    · exact Or.inr (by simp [finiteProfile, member])
    · exact Or.inl (by simp [finiteProfile, member])

def Allowed (D : Set X) : Set (X → ℝ) :=
  { profile | (∀ x, profile x = 0 ∨ profile x = 1) ∧
    ∀ x, profile x = 1 → x ∈ D }

theorem read_uniformEmbedding (D : Set X) : IsUniformEmbedding (read D) :=
  (Completion.isUniformInducing_extension
    isUniformEmbedding_subtype_val.isUniformInducing).isUniformEmbedding

theorem supported_mem_closure (D : Set X) (profile : X → ℝ)
    (allowed : profile ∈ Allowed D) :
    profile ∈ closure (Set.range (Subtype.val : Raw D → X → ℝ)) := by
  classical
  rw [mem_closure_iff]
  intro neighborhood openNeighborhood contains
  obtain ⟨keys, fibers, localNeighborhood, contained⟩ :=
    isOpen_pi_iff.mp openNeighborhood profile contains
  obtain ⟨raw, matched⟩ := finite_assignment D {x | profile x = 1}
    (fun x one => allowed.2 x one) keys
  refine ⟨raw.val, contained ?_, ⟨raw, rfl⟩⟩
  intro x inside
  rw [matched x inside]
  have profile_eq : (if x ∈ {x | profile x = 1} then (1 : ℝ) else 0) = profile x := by
    rcases allowed.1 x with zero | one
    · simp [zero]
    · simp [one]
  rw [profile_eq]
  exact (localNeighborhood x inside).2

/-- The entire completed image, with both support and binary values retained. -/
theorem read_range (D : Set X) : Set.range (read D) = Allowed D := by
  ext profile
  constructor
  · rintro ⟨material, rfl⟩
    refine ⟨read_binary D material, fun x one => ?_⟩
    by_contra outside
    exact no_new_one D x outside material one
  · intro allowed
    have included : Set.range (Subtype.val : Raw D → X → ℝ) ⊆ Set.range (read D) := by
      rintro _ ⟨raw, rfl⟩
      exact ⟨(raw : Formed D), read_coe D raw⟩
    exact closure_minimal included
      (read_uniformEmbedding D).isClosedEmbedding.isClosed_range
      (supported_mem_closure D profile allowed)

theorem every_supported_profile (D : Set X) (profile : X → ℝ)
    (allowed : profile ∈ Allowed D) :
    ∃! material : Formed D, read D material = profile := by
  obtain ⟨material, recovered⟩ := (Set.ext_iff.mp (read_range D) profile).mpr allowed
  refine ⟨material, recovered, fun other same => ?_⟩
  exact (read_uniformEmbedding D).injective (same.trans recovered.symm)

end Profiles

section SmallCollection

abbrev W := ZFSet.{u}

def selected (D : Set W.{u}) (material : Formed D) : Set W :=
  { x | read D material x = 1 }

/-- Private mathematical assembly. Its indexing type is the support computed
from the completed material, never a caller's arbitrary type or process. -/
def collect (D : Set W.{u}) (material : Formed D)
    (small : Small.{u} (selected D material)) : W.{u} := by
  letI := small
  exact ZFSet.range (fun value : selected D material => value.val)

theorem mem_collect (D : Set W.{u}) (material : Formed D)
    (small : Small.{u} (selected D material)) (x : W.{u}) :
    x ∈ collect D material small ↔ read D material x = 1 := by
  let := small
  change x ∈ ZFSet.range (fun value : selected D material => value.val) ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨value, same⟩
    exact same ▸ value.property
  · intro one
    exact ⟨⟨x, one⟩, rfl⟩

/-- Public candidate receiver: the smallness check is inside the constructor. -/
def formSmall (D : Set W.{u}) (material : Formed D) : Option W.{u} := by
  classical
  exact if small : Small.{u} (selected D material) then
    some (collect D material small)
  else none

theorem formSmall_recovers (D : Set W.{u}) (material : Formed D)
    (small : Small.{u} (selected D material)) :
    formSmall D material = some (collect D material small) := by
  classical
  exact dif_pos small

/-- Entire membership, not merely a cardinal comparison, is retained. -/
theorem collect_uses_only_parents (D : Set W.{u}) (material : Formed D)
    (small : Small.{u} (selected D material)) :
    (collect D material small : Set W.{u}) ⊆ D := by
  intro x member
  by_contra outside
  exact no_new_one D x outside material
    ((mem_collect D material small x).mp member)

theorem successful_formation_uses_only_parents
    (D : Set W.{u}) (material : Formed D) (result : W.{u})
    (formed : formSmall D material = some result) :
    (result : Set W.{u}) ⊆ D := by
  classical
  unfold formSmall at formed
  split at formed
  · rename_i small
    have same := Option.some.inj formed
    rw [← same]
    exact collect_uses_only_parents D material small
  · cases formed

/-- A universe-sized support cannot be shrunk into one small set. This is not
an assertion that a whole source has a fixed carrier. -/
theorem rejects_universal_support (D : Set W.{u}) (material : Formed D)
    (allSelected : ∀ x : W.{u}, read D material x = 1) :
    formSmall D material = none := by
  classical
  have notSmall : ¬ Small.{u} (selected D material) := by
    intro small
    let result := collect D material small
    have selfMember : result ∈ result :=
      (mem_collect D material small result).mpr (allSelected result)
    exact ZFSet.mem_irrefl result selfMember
  exact dif_neg notSmall

end SmallCollection

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSmallSupport
