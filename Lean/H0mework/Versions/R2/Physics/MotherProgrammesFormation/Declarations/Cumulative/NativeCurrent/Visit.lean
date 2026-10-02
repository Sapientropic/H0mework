import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeVisit.Material

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}

/-- A complete formed living-root header supplies the lawful visit generator.
The material selects its chronological origin and depth. -/
def formCurrent (header : Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, SourceNativeLivingRootClosure N vocabulary)
    (material : MotherArenaHigher.Material rank) : Option (SourceNativeLivingRootCurrentAt N) :=
  (MotherNativeVisit.formVisit header.2 material).map (fun visit => ⟨header.1, header.2, visit⟩)

theorem current_on_header (old : SourceNativeLivingRootCurrentAt N)
    (header : Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, SourceNativeLivingRootClosure N vocabulary)
    (same : header = ⟨old.V, old.root⟩) :
    ∃ material : MotherArenaHigher.Material rank, formCurrent header material = some old := by
  obtain ⟨material, formed⟩ := MotherNativeVisit.every_visit_material old.root old.visit
  refine ⟨material, ?_⟩
  rw [same, formCurrent, formed]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
