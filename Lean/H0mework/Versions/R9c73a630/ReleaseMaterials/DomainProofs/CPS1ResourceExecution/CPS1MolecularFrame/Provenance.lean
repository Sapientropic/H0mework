import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Provenance

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

theorem actual_execution_source
    (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm
      (CPS1Reinitiation.Handover.rawFuel CPS1ResourceExecution.Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) (generated : 0 < CPS1EditingChemicalJoin.EditingStock.paid edits water additional)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction)
    (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    ∃ (frame : CPS1Recycling.Frame) (previous : CPS1Following.Source.Occurrence frame)
      (current : Source.Occurrence frame),
      CPS1Following.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
        oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
        followingActions followingFeed = some ⟨frame,previous⟩ ∧
      Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
        oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
        followingActions followingFeed actions feed = some ⟨frame,current⟩ ∧
      current.previous = previous ∧
      current.current = Source.advance frame (Source.fromActual frame previous).current actions feed := by
  rcases CPS1Following.actual_execution_source edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth generated
    oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed with
    ⟨frame,_,previous,_,followingSource,_,_⟩
  let current : Source.Occurrence frame :=
    {Source.fromActual frame previous with current := Source.advance frame (Source.fromActual frame previous).current actions feed}
  refine ⟨frame,previous,current,followingSource,?_,rfl,rfl⟩
  simp only [Source.execution,followingSource]
  rfl

end
end CPS1MolecularFrame
