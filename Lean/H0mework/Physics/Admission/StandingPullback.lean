import H0mework.Physics.Admission.StandingAuditBasis

/-!
# Equal-anchor composition of native standing operations

Independent operation graphs cannot be declared to audit the same object by
placing them in an unconstrained product.  This module requires each graph to
expose a native anchor and prove that every successful operation preserves it.
Two graphs then compose on their typed equal-anchor pullback.

The construction is facet-free and binary, so any number of native axes can be
assembled by iteration.  It does not certify that chosen anchor maps are
physically adequate; constant anchors still collapse to an unrestricted
product and remain a diagnostic anti-pattern.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uLeft uRight uLeftMove uRightMove uAnchor

/-- Native standing operations equipped with an operation-preserved object
anchor. -/
structure AnchoredStandingOperations
    (Presentation : Type uLeft) (Move : Type uLeftMove)
    (Anchor : Type uAnchor)
    extends NativeStandingOperations Presentation Move where
  anchor : Presentation → Anchor
  anchor_preserved :
    ∀ move source result,
      apply move source = some result →
        anchor result = anchor source

theorem AnchoredStandingOperations.anchor_eq_of_generatedStandingEquiv
    {Presentation : Type uLeft} {Move : Type uLeftMove}
    {Anchor : Type uAnchor}
    (operations : AnchoredStandingOperations Presentation Move Anchor)
    {source result : Presentation}
    (hrelated : GeneratedStandingEquiv
      operations.toNativeStandingOperations source result) :
    operations.anchor result = operations.anchor source := by
  induction hrelated with
  | refl _ => rfl
  | step move happlies =>
      exact operations.anchor_preserved move _ _ happlies
  | symm _ ih => exact ih.symm
  | trans _ _ ihleft ihrght => exact ihrght.trans ihleft

/-- Typed equal-anchor carrier for two native presentation graphs. -/
abbrev AnchoredStandingPullback
    {Left : Type uLeft} {Right : Type uRight}
    {LeftMove : Type uLeftMove} {RightMove : Type uRightMove}
    {Anchor : Type uAnchor}
    (left : AnchoredStandingOperations Left LeftMove Anchor)
    (right : AnchoredStandingOperations Right RightMove Anchor) :=
  { pair : Left × Right // left.anchor pair.1 = right.anchor pair.2 }

namespace AnchoredStandingPullback

variable {Left : Type uLeft} {Right : Type uRight}
variable {LeftMove : Type uLeftMove} {RightMove : Type uRightMove}
variable {Anchor : Type uAnchor}

/-- Attach an externally supplied source/object tag to a local presentation
graph.  Local moves may change only the presentation coordinate.  A concrete
producer must still generate a meaningful, nonconstant tag. -/
def taggedOperations
    (operations : NativeStandingOperations Right RightMove) :
    AnchoredStandingOperations (Anchor × Right) RightMove Anchor where
  toNativeStandingOperations := {
    apply := fun move source =>
      match happly : operations.apply move source.2 with
      | none => none
      | some result => some (source.1, result)
  }
  anchor := Prod.fst
  anchor_preserved := by
    intro move source result happlies
    simp only at happlies
    split at happlies
    · simp at happlies
    · simp only [Option.some.injEq] at happlies
      subst result
      rfl

theorem taggedLift_nativeMoveInvariant
    (operations : NativeStandingOperations Right RightMove)
    {target : Right → Prop}
    (hinvariant : NativeMoveInvariant operations target) :
    NativeMoveInvariant
      (taggedOperations (Anchor := Anchor) operations).toNativeStandingOperations
      (fun presentation => target presentation.2) := by
  intro move source result happlies
  simp only [taggedOperations] at happlies
  split at happlies
  · simp at happlies
  · rename_i localResult happly
    simp only [Option.some.injEq] at happlies
    subst result
    exact hinvariant move source.2 localResult happly

theorem taggedLift_standingInvariant
    (operations : NativeStandingOperations Right RightMove)
    {target : Right → Prop}
    (hinvariant : StandingInvariant
      (generatedStandingIdentity operations) target) :
    StandingInvariant
      (generatedStandingIdentity
        (taggedOperations (Anchor := Anchor) operations).toNativeStandingOperations)
      (fun presentation => target presentation.2) := by
  apply
    (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
      (taggedOperations (Anchor := Anchor) operations).toNativeStandingOperations
      _).mpr
  exact taggedLift_nativeMoveInvariant operations
    ((standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
      operations target).mp hinvariant)

/-- Constant `Unit` anchors impose no cross-axis identity constraint: the
pullback is exactly the unrestricted product. -/
def unitAnchorEquiv
    (left : AnchoredStandingOperations Left LeftMove Unit)
    (right : AnchoredStandingOperations Right RightMove Unit) :
    AnchoredStandingPullback left right ≃ Left × Right where
  toFun := fun presentation => presentation.1
  invFun := fun pair => ⟨pair, Subsingleton.elim _ _⟩
  left_inv := by
    intro presentation
    apply Subtype.ext
    rfl
  right_inv := by
    intro pair
    rfl

/-- A left or right native move acts on the corresponding pullback coordinate;
anchor preservation constructs the new typed equality. -/
def operations
    (left : AnchoredStandingOperations Left LeftMove Anchor)
    (right : AnchoredStandingOperations Right RightMove Anchor) :
    NativeStandingOperations
      (AnchoredStandingPullback left right)
      (Sum LeftMove RightMove) where
  apply move source :=
    match move with
    | .inl leftMove =>
        match happly : left.apply leftMove source.1.1 with
        | none => none
        | some result =>
            some
              ⟨(result, source.1.2),
                (left.anchor_preserved leftMove source.1.1 result happly).trans
                  source.2⟩
    | .inr rightMove =>
        match happly : right.apply rightMove source.1.2 with
        | none => none
        | some result =>
            some
              ⟨(source.1.1, result),
                source.2.trans
                  (right.anchor_preserved rightMove source.1.2 result
                    happly).symm⟩

/-- A successful left-axis move remains executable on the equal-anchor
pullback.  The new anchor equality is generated from the operation's
preservation theorem; callers do not have to rewrite dependent subtype proof
terms by hand. -/
theorem exists_apply_inl_of_left_apply
    (left : AnchoredStandingOperations Left LeftMove Anchor)
    (right : AnchoredStandingOperations Right RightMove Anchor)
    {source : AnchoredStandingPullback left right}
    {move : LeftMove} {leftResult : Left}
    (happly : left.apply move source.1.1 = some leftResult) :
    ∃ result : AnchoredStandingPullback left right,
      (operations left right).apply (.inl move) source = some result := by
  let result : AnchoredStandingPullback left right :=
    ⟨(leftResult, source.1.2),
      (left.anchor_preserved move source.1.1 leftResult happly).trans
        source.2⟩
  refine ⟨result, ?_⟩
  simp only [operations]
  split
  · rename_i hnone
    rw [happly] at hnone
    contradiction
  · rename_i actual hactual
    have hactual_eq : actual = leftResult := by
      rw [happly] at hactual
      exact (Option.some.inj hactual).symm
    subst actual
    congr 1

/-- Symmetric executability lemma for the right axis. -/
theorem exists_apply_inr_of_right_apply
    (left : AnchoredStandingOperations Left LeftMove Anchor)
    (right : AnchoredStandingOperations Right RightMove Anchor)
    {source : AnchoredStandingPullback left right}
    {move : RightMove} {rightResult : Right}
    (happly : right.apply move source.1.2 = some rightResult) :
    ∃ result : AnchoredStandingPullback left right,
      (operations left right).apply (.inr move) source = some result := by
  let result : AnchoredStandingPullback left right :=
    ⟨(source.1.1, rightResult),
      source.2.trans
        (right.anchor_preserved move source.1.2 rightResult happly).symm⟩
  refine ⟨result, ?_⟩
  simp only [operations]
  split
  · rename_i hnone
    rw [happly] at hnone
    contradiction
  · rename_i actual hactual
    have hactual_eq : actual = rightResult := by
      rw [happly] at hactual
      exact (Option.some.inj hactual).symm
    subst actual
    congr 1

/-- The pullback operation graph itself preserves the common anchor, so it can
be iterated with further anchored presentation axes. -/
def anchoredOperations
    (left : AnchoredStandingOperations Left LeftMove Anchor)
    (right : AnchoredStandingOperations Right RightMove Anchor) :
    AnchoredStandingOperations
      (AnchoredStandingPullback left right)
      (Sum LeftMove RightMove) Anchor where
  toNativeStandingOperations := operations left right
  anchor := fun presentation => left.anchor presentation.1.1
  anchor_preserved := by
    intro move source result happlies
    cases move with
    | inl leftMove =>
        simp only [operations] at happlies
        split at happlies
        · simp at happlies
        · rename_i leftResult happly
          simp only [Option.some.injEq] at happlies
          subst result
          exact left.anchor_preserved leftMove source.1.1 leftResult happly
    | inr rightMove =>
        simp only [operations] at happlies
        split at happlies
        · simp at happlies
        · simp only [Option.some.injEq] at happlies
          subst result
          rfl

/-- A left standing invariant lifts to the equal-anchor combined carrier. -/
theorem leftLift_nativeMoveInvariant
    (left : AnchoredStandingOperations Left LeftMove Anchor)
    (right : AnchoredStandingOperations Right RightMove Anchor)
    {target : Left → Prop}
    (hinvariant : NativeMoveInvariant
      left.toNativeStandingOperations target) :
    NativeMoveInvariant (operations left right)
      (fun presentation => target presentation.1.1) := by
  intro move source result happlies
  cases move with
  | inl leftMove =>
      simp only [operations] at happlies
      split at happlies
      · simp at happlies
      · rename_i leftResult happly
        simp only [Option.some.injEq] at happlies
        subst result
        exact hinvariant leftMove source.1.1 leftResult happly
  | inr rightMove =>
      simp only [operations] at happlies
      split at happlies
      · simp at happlies
      · simp only [Option.some.injEq] at happlies
        subst result
        rfl

/-- A right standing invariant lifts to the equal-anchor combined carrier. -/
theorem rightLift_nativeMoveInvariant
    (left : AnchoredStandingOperations Left LeftMove Anchor)
    (right : AnchoredStandingOperations Right RightMove Anchor)
    {target : Right → Prop}
    (hinvariant : NativeMoveInvariant
      right.toNativeStandingOperations target) :
    NativeMoveInvariant (operations left right)
      (fun presentation => target presentation.1.2) := by
  intro move source result happlies
  cases move with
  | inl leftMove =>
      simp only [operations] at happlies
      split at happlies
      · simp at happlies
      · simp only [Option.some.injEq] at happlies
        subst result
        rfl
  | inr rightMove =>
      simp only [operations] at happlies
      split at happlies
      · simp at happlies
      · rename_i rightResult happly
        simp only [Option.some.injEq] at happlies
        subst result
        exact hinvariant rightMove source.1.2 rightResult happly

theorem leftLift_standingInvariant
    (left : AnchoredStandingOperations Left LeftMove Anchor)
    (right : AnchoredStandingOperations Right RightMove Anchor)
    {target : Left → Prop}
    (hinvariant : StandingInvariant
      (generatedStandingIdentity left.toNativeStandingOperations) target) :
    StandingInvariant
      (generatedStandingIdentity (operations left right))
      (fun presentation => target presentation.1.1) := by
  apply
    (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
      (operations left right) _).mpr
  exact leftLift_nativeMoveInvariant left right
    ((standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
      left.toNativeStandingOperations target).mp hinvariant)

theorem rightLift_standingInvariant
    (left : AnchoredStandingOperations Left LeftMove Anchor)
    (right : AnchoredStandingOperations Right RightMove Anchor)
    {target : Right → Prop}
    (hinvariant : StandingInvariant
      (generatedStandingIdentity right.toNativeStandingOperations) target) :
    StandingInvariant
      (generatedStandingIdentity (operations left right))
      (fun presentation => target presentation.1.2) := by
  apply
    (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
      (operations left right) _).mpr
  exact rightLift_nativeMoveInvariant left right
    ((standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
      right.toNativeStandingOperations target).mp hinvariant)

end AnchoredStandingPullback
end PhysicsCore
end SaturationMonoid
