import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Projection.Inventory
import Mathlib.Data.Finite.Sum
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

def sourceProjection : Nat → Type
  | 0 => SourceNativeProjectionCoface Public.Source.Projection Abolition.Functions.Revision.Enactment.Projection
  | births + 1 => SourceNativeProjectionCoface Public.Accounting.Born.Source.Projection
      (SourceNativeProjectionCoface (sourceProjection births) Public.Inquiry.Projection)

def completeProjection (births : Nat) := SourceNativeProjectionCoface (sourceProjection births) Public.Inquiry.Projection

theorem source_projection_finite (births : Nat) : Finite (sourceProjection births) := by
  induction births with
  | zero =>
      exact Finite.of_equiv (Public.Source.Projection ⊕ Abolition.Functions.Revision.Enactment.Projection)
        (Macro.Runtime.cofaceEquiv _ _).symm
  | succ births prior =>
      let := prior
      let : Finite (completeProjection births) :=
        Finite.of_equiv (sourceProjection births ⊕ Public.Inquiry.Projection) (Macro.Runtime.cofaceEquiv _ _).symm
      exact Finite.of_equiv (Public.Accounting.Born.Source.Projection ⊕ completeProjection births)
        (Macro.Runtime.cofaceEquiv _ _).symm

theorem source_projection_card (births : Nat) : Nat.card (sourceProjection births) = 12 + 16 * births := by
  induction births with
  | zero =>
      change Nat.card (SourceNativeProjectionCoface Public.Source.Projection Abolition.Functions.Revision.Enactment.Projection) = _
      rw [Nat.card_congr (Macro.Runtime.cofaceEquiv _ _), Nat.card_sum, public_source_projection_card, original_provenance_projection_card]
  | succ births prior =>
      let := source_projection_finite births
      let : Finite (completeProjection births) :=
        Finite.of_equiv (sourceProjection births ⊕ Public.Inquiry.Projection) (Macro.Runtime.cofaceEquiv _ _).symm
      change Nat.card (SourceNativeProjectionCoface Public.Accounting.Born.Source.Projection (completeProjection births)) = _
      rw [Nat.card_congr (Macro.Runtime.cofaceEquiv _ _), Nat.card_sum, born_source_projection_card]
      unfold completeProjection
      rw [Nat.card_congr (Macro.Runtime.cofaceEquiv _ _), Nat.card_sum, prior, public_inquiry_projection_card]
      omega

theorem complete_projection_card (births : Nat) : Nat.card (completeProjection births) = 20 + 16 * births := by
  let := source_projection_finite births
  unfold completeProjection
  rw [Nat.card_congr (Macro.Runtime.cofaceEquiv _ _), Nat.card_sum, source_projection_card, public_inquiry_projection_card]
  omega

structure ProjectionLayout (Projection : Type) where
  births : Nat
  source_eq : Projection = sourceProjection births

namespace ProjectionLayout
variable {P Q : Type} (layout : ProjectionLayout P)

theorem card : Nat.card (SourceNativeProjectionCoface P Public.Inquiry.Projection) = 20 + 16 * layout.births :=
  (congrArg (fun projection => Nat.card (SourceNativeProjectionCoface projection Public.Inquiry.Projection)) layout.source_eq).trans
    (complete_projection_card _)

include layout in
theorem source_eq_of_card (other : ProjectionLayout Q)
    (same : Nat.card (SourceNativeProjectionCoface P Public.Inquiry.Projection) =
      Nat.card (SourceNativeProjectionCoface Q Public.Inquiry.Projection)) : P = Q := by
  have births : layout.births = other.births := by rw [layout.card, other.card] at same; omega
  exact layout.source_eq.trans ((congrArg sourceProjection births).trans other.source_eq.symm)

end ProjectionLayout

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime
