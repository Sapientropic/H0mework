import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldPresentation.Current

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace CPS1ReactiveField.FinitePresentation
noncomputable section
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
variable (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
  (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
  (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
  (oldActions : List CPS1AtomicDynamics.Source.RawAction)
  (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
  (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
  (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
  (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
  (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
  (deformationActions : List CPS1Deformation.Source.RawAction) (deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind)
  (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
  (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) (raw : List CPS1AddressedReactiveJoint.Rows.RawAction)

theorem from_source_old :
    (fromSourceWhole edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
      electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
      molecularFeed deformationActions deformationFeed actions feed raw).map
      (fun generated => ⟨generated.1,generated.2.current.old⟩) =
    CPS1Deformation.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
      electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
      molecularFeed deformationActions deformationFeed := by
  unfold fromSourceWhole Carried.fromSource CPS1ReactiveField.fromSource
  cases CPS1Deformation.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
    electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
    molecularFeed deformationActions deformationFeed <;> rfl

theorem source_complete_stages :
    ∀ generated ∈ (fromSourceWhole edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
      electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
      molecularFeed deformationActions deformationFeed actions feed raw).toList,
      ∀ entry ∈ generated.2.stages, entry.NativeValid := by
  unfold fromSourceWhole Carried.fromSource
  cases original : CPS1ReactiveField.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
    electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
    molecularFeed deformationActions deformationFeed actions feed raw with
  | none => simp only [Option.map_none,Option.toList_none,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | some source =>
    intro generated member entry held
    have same : generated = ⟨source.1,cursor (Carried.startCursor source.2)⟩ := by simpa only [Option.map_some,Option.toList_some,List.mem_singleton] using member
    subst generated
    rcases List.mem_map.mp held with ⟨native,member,rfl⟩
    exact ⟨native,rfl,initial_stages_valid source.2 native member⟩

theorem advance_complete_stages (inputs : List Carried.Input) :
    ∀ generated ∈ (advanceFromSourceWhole edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
      electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
      molecularFeed deformationActions deformationFeed actions feed raw inputs).toList,
      ∀ entry ∈ generated.2.stages, entry.NativeValid := by
  unfold advanceFromSourceWhole Carried.fromSource
  cases original : CPS1ReactiveField.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
    electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
    molecularFeed deformationActions deformationFeed actions feed raw with
  | none => simp only [Option.map_none,Option.toList_none,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | some source =>
    intro generated member
    have same : generated = ⟨source.1,cursor (Carried.advanceAll (Carried.startCursor source.2) inputs)⟩ := by
      simpa only [Option.map_some,Option.toList_some,List.mem_singleton] using member
    subst generated
    exact complete_generated_stages source.2 inputs

end
end CPS1ReactiveField.FinitePresentation
