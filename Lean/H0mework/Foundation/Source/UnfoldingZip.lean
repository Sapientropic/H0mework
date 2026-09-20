import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Canonical zip of two rooted accounted occurrences

Two finite occurrence trees either zip position-by-position, preserving both
complete branch inventories, or expose the two exact tree shapes that cannot
be aligned.  Payload equality is irrelevant; only the source-generated branch
shape is compared.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootedAccountedUnfoldingZip

universe u v

mutual

def zip? {Left : Type u} {Right : Type v} :
    RootedAccountedUnfolding Left → RootedAccountedUnfolding Right →
      Option (RootedAccountedUnfolding (Left × Right))
  | .occur left leftBranches, .occur right rightBranches =>
      match zipBranches? leftBranches rightBranches with
      | some branches => some (.occur (left, right) branches)
      | none => none

def zipBranches? {Left : Type u} {Right : Type v} :
    AccountedBranches Left → AccountedBranches Right →
      Option (AccountedBranches (Left × Right))
  | .nil, .nil => some .nil
  | .cons leftHead leftTail, .cons rightHead rightTail =>
      match zip? leftHead rightHead, zipBranches? leftTail rightTail with
      | some head, some tail => some (.cons head tail)
      | _, _ => none
  | .nil, .cons _ _ => none
  | .cons _ _, .nil => none

end

mutual

theorem zip?_left_projection
    {Left : Type u} {Right : Type v}
    (left : RootedAccountedUnfolding Left)
    (right : RootedAccountedUnfolding Right)
    (zipped : RootedAccountedUnfolding (Left × Right))
    (exact : zip? left right = some zipped) :
    zipped.map Prod.fst = left := by
  cases left with
  | occur left leftBranches =>
      cases right with
      | occur right rightBranches =>
          unfold zip? at exact
          cases branches_eq : zipBranches? leftBranches rightBranches with
          | none =>
              simp only [branches_eq] at exact
              contradiction
          | some zippedBranches =>
              simp only [branches_eq, Option.some.injEq] at exact
              cases exact
              change RootedAccountedUnfolding.occur left
                  (RootedAccountedUnfolding.mapBranches Prod.fst
                    zippedBranches) =
                RootedAccountedUnfolding.occur left leftBranches
              rw [zipBranches?_left_projection leftBranches rightBranches
                zippedBranches branches_eq]

theorem zipBranches?_left_projection
    {Left : Type u} {Right : Type v}
    (left : AccountedBranches Left) (right : AccountedBranches Right)
    (zipped : AccountedBranches (Left × Right))
    (exact : zipBranches? left right = some zipped) :
    RootedAccountedUnfolding.mapBranches Prod.fst zipped = left := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          change (some .nil : Option (AccountedBranches (Left × Right))) =
            some zipped at exact
          cases exact
          rfl
      | cons rightHead rightTail =>
          change (none : Option (AccountedBranches (Left × Right))) =
            some zipped at exact
          contradiction
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          change (none : Option (AccountedBranches (Left × Right))) =
            some zipped at exact
          contradiction
      | cons rightHead rightTail =>
          unfold zipBranches? at exact
          cases head_eq : zip? leftHead rightHead with
          | none =>
              simp only [head_eq] at exact
              contradiction
          | some zippedHead =>
              cases tail_eq : zipBranches? leftTail rightTail with
              | none =>
                  simp only [head_eq, tail_eq] at exact
                  contradiction
              | some zippedTail =>
                  simp only [head_eq, tail_eq, Option.some.injEq] at exact
                  cases exact
                  change AccountedBranches.cons
                      (zippedHead.map Prod.fst)
                      (RootedAccountedUnfolding.mapBranches Prod.fst
                        zippedTail) =
                    AccountedBranches.cons leftHead leftTail
                  rw [zip?_left_projection leftHead rightHead zippedHead
                    head_eq]
                  rw [zipBranches?_left_projection leftTail rightTail
                    zippedTail tail_eq]

end

mutual

theorem zip?_right_projection
    {Left : Type u} {Right : Type v}
    (left : RootedAccountedUnfolding Left)
    (right : RootedAccountedUnfolding Right)
    (zipped : RootedAccountedUnfolding (Left × Right))
    (exact : zip? left right = some zipped) :
    zipped.map Prod.snd = right := by
  cases left with
  | occur left leftBranches =>
      cases right with
      | occur right rightBranches =>
          unfold zip? at exact
          cases branches_eq : zipBranches? leftBranches rightBranches with
          | none =>
              simp only [branches_eq] at exact
              contradiction
          | some zippedBranches =>
              simp only [branches_eq, Option.some.injEq] at exact
              cases exact
              change RootedAccountedUnfolding.occur right
                  (RootedAccountedUnfolding.mapBranches Prod.snd
                    zippedBranches) =
                RootedAccountedUnfolding.occur right rightBranches
              rw [zipBranches?_right_projection leftBranches rightBranches
                zippedBranches branches_eq]

theorem zipBranches?_right_projection
    {Left : Type u} {Right : Type v}
    (left : AccountedBranches Left) (right : AccountedBranches Right)
    (zipped : AccountedBranches (Left × Right))
    (exact : zipBranches? left right = some zipped) :
    RootedAccountedUnfolding.mapBranches Prod.snd zipped = right := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          change (some .nil : Option (AccountedBranches (Left × Right))) =
            some zipped at exact
          cases exact
          rfl
      | cons rightHead rightTail =>
          change (none : Option (AccountedBranches (Left × Right))) =
            some zipped at exact
          contradiction
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          change (none : Option (AccountedBranches (Left × Right))) =
            some zipped at exact
          contradiction
      | cons rightHead rightTail =>
          unfold zipBranches? at exact
          cases head_eq : zip? leftHead rightHead with
          | none =>
              simp only [head_eq] at exact
              contradiction
          | some zippedHead =>
              cases tail_eq : zipBranches? leftTail rightTail with
              | none =>
                  simp only [head_eq, tail_eq] at exact
                  contradiction
              | some zippedTail =>
                  simp only [head_eq, tail_eq, Option.some.injEq] at exact
                  cases exact
                  change AccountedBranches.cons
                      (zippedHead.map Prod.snd)
                      (RootedAccountedUnfolding.mapBranches Prod.snd
                        zippedTail) =
                    AccountedBranches.cons rightHead rightTail
                  rw [zip?_right_projection leftHead rightHead zippedHead
                    head_eq]
                  rw [zipBranches?_right_projection leftTail rightTail
                    zippedTail tail_eq]

end

mutual

theorem zip?_exists_of_shape_eq
    {Left : Type u} {Right : Type v}
    (left : RootedAccountedUnfolding Left)
    (right : RootedAccountedUnfolding Right)
    (shape_eq : left.map (fun _ => ()) = right.map (fun _ => ())) :
    ∃ zipped, zip? left right = some zipped := by
  cases left with
  | occur left leftBranches =>
      cases right with
      | occur right rightBranches =>
          change RootedAccountedUnfolding.occur ()
              (RootedAccountedUnfolding.mapBranches (fun _ => ())
                leftBranches) =
            RootedAccountedUnfolding.occur ()
              (RootedAccountedUnfolding.mapBranches (fun _ => ())
                rightBranches) at shape_eq
          injection shape_eq with _ branches_eq
          obtain ⟨zippedBranches, zipped_eq⟩ :=
            zipBranches?_exists_of_shape_eq leftBranches rightBranches
              branches_eq
          exact ⟨.occur (left, right) zippedBranches, by
            unfold zip?
            rw [zipped_eq]⟩

theorem zipBranches?_exists_of_shape_eq
    {Left : Type u} {Right : Type v}
    (left : AccountedBranches Left) (right : AccountedBranches Right)
    (shape_eq : RootedAccountedUnfolding.mapBranches (fun _ => ()) left =
      RootedAccountedUnfolding.mapBranches (fun _ => ()) right) :
    ∃ zipped, zipBranches? left right = some zipped := by
  cases left with
  | nil =>
      cases right with
      | nil => exact ⟨.nil, rfl⟩
      | cons rightHead rightTail =>
          change AccountedBranches.nil = AccountedBranches.cons
            (rightHead.map (fun _ => ()))
            (RootedAccountedUnfolding.mapBranches (fun _ => ())
              rightTail) at shape_eq
          contradiction
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          change AccountedBranches.cons (leftHead.map (fun _ => ()))
              (RootedAccountedUnfolding.mapBranches (fun _ => ())
                leftTail) = AccountedBranches.nil at shape_eq
          contradiction
      | cons rightHead rightTail =>
          change AccountedBranches.cons (leftHead.map (fun _ => ()))
              (RootedAccountedUnfolding.mapBranches (fun _ => ())
                leftTail) =
            AccountedBranches.cons (rightHead.map (fun _ => ()))
              (RootedAccountedUnfolding.mapBranches (fun _ => ())
                rightTail) at shape_eq
          injection shape_eq with headShape_eq tailShape_eq
          obtain ⟨zippedHead, zippedHead_eq⟩ :=
            zip?_exists_of_shape_eq leftHead rightHead headShape_eq
          obtain ⟨zippedTail, zippedTail_eq⟩ :=
            zipBranches?_exists_of_shape_eq leftTail rightTail tailShape_eq
          exact ⟨.cons zippedHead zippedTail, by
            unfold zipBranches?
            rw [zippedHead_eq, zippedTail_eq]⟩

end

structure GeneratedZipAt {Left : Type u} {Right : Type v}
    (left : RootedAccountedUnfolding Left)
    (right : RootedAccountedUnfolding Right) : Type (max u v) where
  tree : RootedAccountedUnfolding (Left × Right)
  exact : zip? left right = some tree
  left_projection : tree.map Prod.fst = left
  right_projection : tree.map Prod.snd = right

structure ShapeResidualAt {Left : Type u} {Right : Type v}
    (left : RootedAccountedUnfolding Left)
    (right : RootedAccountedUnfolding Right) : Type (max u v) where
  leftShape : RootedAccountedUnfolding Unit
  rightShape : RootedAccountedUnfolding Unit
  leftShape_eq : leftShape = left.map fun _ => ()
  rightShape_eq : rightShape = right.map fun _ => ()
  shape_ne : leftShape ≠ rightShape
  zip_eq_none : zip? left right = none

inductive Disposition {Left : Type u} {Right : Type v}
    (left : RootedAccountedUnfolding Left)
    (right : RootedAccountedUnfolding Right) : Type (max u v)
  | generated (zipped : GeneratedZipAt left right)
  | shapeResidual (residual : ShapeResidualAt left right)

def settle {Left : Type u} {Right : Type v}
    (left : RootedAccountedUnfolding Left)
    (right : RootedAccountedUnfolding Right) : Disposition left right := by
  cases exact : zip? left right with
  | none =>
      exact .shapeResidual
        ⟨left.map (fun _ => ()), right.map (fun _ => ()), rfl, rfl,
          by
            intro shape_eq
            obtain ⟨zipped, zipped_eq⟩ :=
              zip?_exists_of_shape_eq left right shape_eq
            rw [exact] at zipped_eq
            contradiction,
          exact⟩
  | some tree =>
      exact .generated
        ⟨tree, exact, zip?_left_projection left right tree exact,
          zip?_right_projection left right tree exact⟩

end RootedAccountedUnfoldingZip
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
