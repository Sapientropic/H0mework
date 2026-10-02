import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaProjection.Operations
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Formation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherLedgerRoot
open MotherPatchInventory
open MotherProjectionOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeLedgerSource N V}

def Encoding.ofTotal {law : SourceNativeProjectionLaw source} (encode : Total law ↪ B) : Encoding (rank := rank) law where
  projection := ⟨fun p => encode (.inl p), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  active := ⟨fun value => encode (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (encode.injective same))⟩
  inactive := ⟨fun value => encode (.inr (.inr (.inl value))), fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (encode.injective same)))⟩
  payload := ⟨fun value => encode (.inr (.inr (.inr value))), fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (encode.injective same)))⟩

theorem projection_formed (parent material : M) (root : RootValue) (formed : MotherArenaRoot.formRoot parent = some root)
    (checked : Check (rootCoordinates parent root formed) material) :
    formProjection ((MotherArenaHigher.pack rank) (parent, material)) =
      some ⟨root, projectionLaw (rootCoordinates parent root formed) material checked⟩ := by
  unfold formProjection
  rw [MotherArenaHigher.split_pack]
  dsimp only
  unfold formProjectionParts
  exact Option.pbind_eq_some_iff.mpr ⟨root, formed, dif_pos checked⟩

theorem every_projection_on_formed_root (parent : M) (root : RootValue) (formed : MotherArenaRoot.formRoot parent = some root)
    (old : SourceNativeProjectionLaw root.2.2.source) (encode : Total old ↪ B) :
    ∃ material : M, ∃ generated : SourceNativeProjectionLaw root.2.2.source,
      formProjection material = some ⟨root, generated⟩ ∧ Nonempty (Presentation old generated) := by
  let coordinates := rootCoordinates parent root formed
  let encoding := Encoding.ofTotal encode
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank) (Encoding.reader coordinates old encoding)
  let checked := Encoding.checked coordinates old encoding hm
  exact ⟨(MotherArenaHigher.pack rank) (parent, material), projectionLaw coordinates material checked,
    projection_formed parent material root formed checked, ⟨Encoding.presentation coordinates old encoding hm⟩⟩

/-- The full original outcome, including the chosen Type-valued active
member and its dependent payload or complete inactive receipt, is consumed. -/
theorem formed_projection_consumes_original_outcome (parent : M) (root : RootValue) (formed : MotherArenaRoot.formRoot parent = some root)
    (old : SourceNativeProjectionLaw root.2.2.source) (encode : Total old ↪ B) :
    ∃ material : M, ∃ generated : SourceNativeProjectionLaw root.2.2.source, ∃ p : Presentation old generated,
      formProjection material = some ⟨root, generated⟩ ∧
      ∀ projection point, generated.outcomeAt (p.projection projection) point.2 =
        p.outcomeEquiv projection point (old.outcomeAt projection point.2) := by
  obtain ⟨material, generated, produced, ⟨p⟩⟩ := every_projection_on_formed_root parent root formed old encode
  exact ⟨material, generated, p, produced, p.outcome_eq⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
