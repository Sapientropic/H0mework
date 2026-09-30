import H0mework.Physics.MotherProgrammesFormation.Declarations.SmallSupport.Localization

/-! Whole set recovery from its completed member profile.  The target set
occurs only in coverage.  This is a mathematical receiver: the source of the
entire native raw parent carrier remains a separate obligation. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSmallSupport

open Set
open scoped Classical

universe u

noncomputable section

theorem every_supported_set (parents : Set W.{u}) (target : W.{u})
    (supported : (target : Set W.{u}) ⊆ parents) :
    ∃ material : Formed parents,
      (∀ x, read parents material x = 1 ↔ x ∈ target) ∧
      formSmall parents material = some target := by
  let profile : W.{u} → ℝ := fun x => if x ∈ target then 1 else 0
  have allowed : profile ∈ Allowed parents := by
    constructor
    · intro x
      by_cases member : x ∈ target
      · exact Or.inr (if_pos member)
      · exact Or.inl (if_neg member)
    · intro x one
      have member : x ∈ target := by
        by_contra absent
        have zero : profile x = 0 := if_neg absent
        exact zero_ne_one (zero.symm.trans one)
      exact supported member
  obtain ⟨material, read_eq, _⟩ := every_supported_profile parents profile allowed
  have members (x : W.{u}) : read parents material x = 1 ↔ x ∈ target := by
    rw [read_eq]
    simp [profile]
  have selected_eq : selected parents material = (target : Set W.{u}) := by
    ext x
    exact members x
  have small : Small.{u} (selected parents material) := by
    rw [selected_eq]
    exact ZFSet.small_coe target
  have recovered : collect parents material small = target := by
    ext x
    exact (mem_collect parents material small x).trans (members x)
  exact ⟨material, members, (formSmall_recovers parents material small).trans (congrArg some recovered)⟩

/-- A genuine large-profile witness exercises the receiver's size rejection. -/
theorem universal_profile_rejected :
    ∃ material : Formed (Set.univ : Set W.{u}),
      (∀ x, read Set.univ material x = 1) ∧ formSmall Set.univ material = none := by
  obtain ⟨material, read_eq, _⟩ := every_supported_profile (Set.univ : Set W.{u})
    (fun _ => 1) ⟨fun _ => Or.inr rfl, fun _ _ => Set.mem_univ _⟩
  have allSelected : ∀ x, read Set.univ material x = 1 := congrFun read_eq
  exact ⟨material, allSelected, rejects_universal_support Set.univ material allSelected⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSmallSupport
