import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Operations

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherLedgerRoot
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeLedgerSource N V}

def Encoding.ofTotal {law : SourceNativeProjectionLaw source} (encode : Total law ↪ B) : Encoding law where
  projection := ⟨fun p => encode (.inl p), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  active := ⟨fun value => encode (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (encode.injective same))⟩
  inactive := ⟨fun value => encode (.inr (.inr (.inl value))), fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (encode.injective same)))⟩
  payload := ⟨fun value => encode (.inr (.inr (.inr value))), fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (encode.injective same)))⟩

theorem projection_formed (parent material : M) (root : RootValue) (formed : formRoot parent = some root)
    (checked : Check (rootCoordinates parent root formed) material) :
    formProjection (MotherHigherLawValue.pack (parent, material)) =
      some ⟨root, projectionLaw (rootCoordinates parent root formed) material checked⟩ := by
  unfold formProjection
  rw [MotherHigherLawValue.split_pack]
  dsimp only
  unfold formProjectionParts
  exact Option.pbind_eq_some_iff.mpr ⟨root, formed, dif_pos checked⟩

theorem every_projection_on_formed_root (parent : M) (root : RootValue) (formed : formRoot parent = some root)
    (old : SourceNativeProjectionLaw root.2.2.source) (encode : Total old ↪ B) :
    ∃ material : M, ∃ generated : SourceNativeProjectionLaw root.2.2.source,
      formProjection material = some ⟨root, generated⟩ ∧ Nonempty (Presentation old generated) := by
  let coordinates := rootCoordinates parent root formed
  let encoding := Encoding.ofTotal encode
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective (Encoding.reader coordinates old encoding)
  let checked := Encoding.checked coordinates old encoding hm
  exact ⟨MotherHigherLawValue.pack (parent, material), projectionLaw coordinates material checked,
    projection_formed parent material root formed checked, ⟨Encoding.presentation coordinates old encoding hm⟩⟩

namespace Presentation
variable {old generated : SourceNativeProjectionLaw source} (p : Presentation old generated)

def outcomeEquiv (projection : old.Projection) (point : Point source.source) :
    SourceNativeProjectionFiberAt old projection point.2 ≃ SourceNativeProjectionFiberAt generated (p.projection projection) point.2 :=
  Equiv.sumCongr (Equiv.sigmaCongr (p.active projection point) (p.payload projection point)) (p.inactive projection point)

theorem outcome_eq (projection : old.Projection) (point : Point source.source) :
    generated.outcomeAt (p.projection projection) point.2 = outcomeEquiv p projection point (old.outcomeAt projection point.2) := by
  unfold SourceNativeProjectionLaw.outcomeAt
  rw [p.classify]
  cases selected : old.classify projection point.2 with
  | inl active =>
      exact congrArg Sum.inl (congrArg
        (fun value => (⟨p.active projection point active, value⟩ : Sigma (generated.PayloadAt (p.projection projection) point.2)))
        (p.project projection point active))
  | inr inactive => rfl
end Presentation

/-- The full original outcome, including the chosen Type-valued active
member and its dependent payload or complete inactive receipt, is consumed. -/
theorem formed_projection_consumes_original_outcome (parent : M) (root : RootValue) (formed : formRoot parent = some root)
    (old : SourceNativeProjectionLaw root.2.2.source) (encode : Total old ↪ B) :
    ∃ material : M, ∃ generated : SourceNativeProjectionLaw root.2.2.source, ∃ p : Presentation old generated,
      formProjection material = some ⟨root, generated⟩ ∧
      ∀ projection point, generated.outcomeAt (p.projection projection) point.2 =
        p.outcomeEquiv projection point (old.outcomeAt projection point.2) := by
  obtain ⟨material, generated, produced, ⟨p⟩⟩ := every_projection_on_formed_root parent root formed old encode
  exact ⟨material, generated, p, produced, p.outcome_eq⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
