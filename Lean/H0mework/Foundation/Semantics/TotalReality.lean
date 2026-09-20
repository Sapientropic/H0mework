import H0mework.Foundation.Responsibility.Lifecycle

/-!
# Total reality and the derived exclusion of unaccounted difference

`NoMagic` is not a field of this kernel.  The derivation starts from weaker
notions which can be realized independently:

* actuality;
* stable reference;
* real difference;
* redundant presentation;
* positive structural identity.

An actual difference is internally determined only when it carries a positive
structural identity.  A purported magic bit is therefore first exposed as an
external-supplement obligation: it claims to be actual and nonredundant while
denying every internal determination.  Total reality is the positive
classification saying that every actual difference is either redundant or
has a structural identity.  The no-external-supplement and no-magic theorems
are consequences, not fields or aliases.

Concrete worlds must still derive `TotalRealityAt` from their source-native
root closure.  A consumer-supplied `TotalRealityAt` is only an abstract theorem
parameter, not living-law world authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace TotalReality

universe u

/-- Weak difference vocabulary before any no-magic claim is available. -/
structure RealityDifferenceSemantics : Type (u + 1) where
  Difference : Type u
  ActualAt : Difference -> Prop
  StableReferenceAt : Difference -> Prop
  RealDifferenceAt : Difference -> Prop
  RedundantAt : Difference -> Prop
  StructuralIdentityAt : Difference -> Prop

/-- A difference which actually occurs, is stably referable, and is real. -/
structure ActualDifferenceAt (R : RealityDifferenceSemantics.{u})
    (difference : R.Difference) : Prop where
  actual : R.ActualAt difference
  stableReference : R.StableReferenceAt difference
  realDifference : R.RealDifferenceAt difference

/-- Positive internal determination.  This is not definitionally `NotMagic`:
it contains the actual difference and its structural identity. -/
structure InternallyDeterminedAt (R : RealityDifferenceSemantics.{u})
    (difference : R.Difference) : Prop where
  actualDifference : ActualDifferenceAt R difference
  structuralIdentity : R.StructuralIdentityAt difference

/-- An actual, nonredundant difference which cannot be located by the internal
structural-identity vocabulary. -/
structure ExternalSupplementAt (R : RealityDifferenceSemantics.{u})
    (difference : R.Difference) : Prop where
  actualDifference : ActualDifferenceAt R difference
  nonredundant : R.RedundantAt difference -> False
  notInternallyDetermined : InternallyDeterminedAt R difference -> False

/-- The alleged magic bit, stated without assuming a no-magic law. -/
structure MagicBitAt (R : RealityDifferenceSemantics.{u})
    (difference : R.Difference) : Prop where
  actualDifference : ActualDifferenceAt R difference
  nonredundant : R.RedundantAt difference -> False
  notInternallyDetermined : InternallyDeterminedAt R difference -> False

/-- A purported magic bit first produces the exact external-supplement
obligation. -/
theorem MagicBitAt.toExternalSupplement
    {R : RealityDifferenceSemantics.{u}} {difference : R.Difference}
    (magic : MagicBitAt R difference) :
    ExternalSupplementAt R difference :=
  ⟨magic.actualDifference, magic.nonredundant,
    magic.notInternallyDetermined⟩

/-- Positive totality.  It classifies actual differences by internal
structure; it contains no no-magic or no-external-supplement field. -/
structure TotalRealityAt (R : RealityDifferenceSemantics.{u}) : Prop where
  locate : (difference : R.Difference) -> ActualDifferenceAt R difference ->
    R.RedundantAt difference ∨ R.StructuralIdentityAt difference

/-- Total reality constructively excludes an external supplement. -/
theorem TotalRealityAt.noExternalSupplement
    {R : RealityDifferenceSemantics.{u}} (total : TotalRealityAt R)
    {difference : R.Difference} :
    ExternalSupplementAt R difference -> False := by
  intro external
  match total.locate difference external.actualDifference with
  | Or.inl redundant => exact external.nonredundant redundant
  | Or.inr identity =>
      exact external.notInternallyDetermined
        ⟨external.actualDifference, identity⟩

/-- Derived no-magic theorem.  `InternallyDeterminedAt` remains a positive
structural witness throughout the proof. -/
theorem TotalRealityAt.noMagicBit
    {R : RealityDifferenceSemantics.{u}} (total : TotalRealityAt R)
    {difference : R.Difference} : MagicBitAt R difference -> False :=
  fun magic => total.noExternalSupplement magic.toExternalSupplement

end TotalReality
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
