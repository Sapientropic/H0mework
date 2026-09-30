import H0mework.Physics.MotherProgrammesFormation.Declarations.SmallSupport.Collection

/-! Complete member-dependency trees for the support receiver. These are
mathematical construction data. Interpreting their entire raw programme
carrier in the original mother source is a separate, still open producer. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ParentCompletion
open MotherSmallSupport
open scoped Classical
universe u
noncomputable section

abbrev Material := Formed (Set.univ : Set W.{u})

inductive Build : W.{u} → Type (u + 1)
  | seed : Build ∅
  | completed {result : W.{u}} (material : Material)
      (formed : formSmall Set.univ material = some result)
      (parents : (x : W.{u}) → x ∈ result → Build x) : Build result

/-- The result index is recovered from the actual receiver, including all members. -/
theorem formed_members (material : Material.{u}) (result : W.{u})
    (formed : formSmall Set.univ material = some result) (x : W.{u}) :
    read Set.univ material x = 1 ↔ x ∈ result := by
  unfold formSmall at formed
  split at formed
  · rename_i small
    have same := Option.some.inj formed
    rw [← same]
    exact (mem_collect Set.univ material small x).symm
  · cases formed

/-- This covers mathematical trees, without claiming an interpretation in S. -/
theorem every_set_has_build (target : W.{u}) : Nonempty (Build target) := by
  induction target using ZFSet.inductionOn with
  | h target parents =>
      obtain ⟨material, _, formed⟩ := every_supported_set Set.univ target (Set.subset_univ _)
      exact ⟨.completed material formed (fun x member => Classical.choice (parents x member))⟩

abbrev Parent := Sigma Build.{u}

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ParentCompletion
