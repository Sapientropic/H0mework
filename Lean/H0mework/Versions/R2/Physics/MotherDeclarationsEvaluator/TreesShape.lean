import H0mework.Versions.R2.Physics.MotherProgrammesFormationDiscrete.History
import H0mework.Foundation.Source.AccountedUnfolding
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherEvaluatorTrees

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open MotherFamilyOccurrence Stage9C.Revision

mutual

private def treeToNat : RootedAccountedUnfolding ℕ → ℕ
  | .occur root branches => Nat.pair root (branchesToNat branches)

private def branchesToNat : AccountedBranches ℕ → ℕ
  | .nil => 0
  | .cons head tail => Nat.pair (treeToNat head) (branchesToNat tail) + 1

end

mutual

private def treeFromNat (code : ℕ) : RootedAccountedUnfolding ℕ :=
  .occur code.unpair.1 (branchesFromNat code.unpair.2)
termination_by 2 * code + 1
 decreasing_by
  have bound := Nat.unpair_right_le code
  omega

private def branchesFromNat : ℕ → AccountedBranches ℕ
  | 0 => .nil
  | code + 1 => .cons (treeFromNat code.unpair.1) (branchesFromNat code.unpair.2)
termination_by code => 2 * code
 decreasing_by
  all_goals
    have left := Nat.unpair_left_le code
    have right := Nat.unpair_right_le code
    omega

end

mutual

private theorem tree_roundtrip (tree : RootedAccountedUnfolding ℕ) :
    treeFromNat (treeToNat tree) = tree := by
  cases tree
  simp only [treeToNat, treeFromNat, Nat.unpair_pair, branches_roundtrip]

private theorem branches_roundtrip (branches : AccountedBranches ℕ) :
    branchesFromNat (branchesToNat branches) = branches := by
  cases branches <;>
    simp only [branchesToNat, branchesFromNat, Nat.unpair_pair, tree_roundtrip, branches_roundtrip]

end

/-- Explicit finite constructor code; no instance declaration is exported. -/
@[instance_reducible] def shapeCodec : Encodable (RootedAccountedUnfolding ℕ) :=
  Encodable.ofLeftInverse treeToNat treeFromNat tree_roundtrip

local instance instEncodableRootedAccountedUnfoldingNat_scratch : Encodable (RootedAccountedUnfolding ℕ) := shapeCodec

noncomputable section

def shapeAt (parent : MotherVisit) : RootedAccountedUnfolding ℕ :=
  (Encodable.decode (StageEightDiscreteFormation.codeOf parent)).getD (.zero 0)

theorem every_shape (shape : RootedAccountedUnfolding ℕ) :
    ∃ code : ℕ, shapeAt (SpinPair.visit (10 + code)) = shape := by
  refine ⟨Encodable.encode shape, ?_⟩
  simp only [shapeAt, StageEightDiscreteFormation.code_at, Encodable.encodek, Option.getD_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherEvaluatorTrees
