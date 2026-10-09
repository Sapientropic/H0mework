import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Birth

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath.Actual
noncomputable section
open CPS1ResourceExecution
open CPS1AtomicDynamics

/-- The saved source body is read from the actual live inventory, not reconstructed
from an old peptide or supplied in the public source entry. -/
theorem body_member (frame : CPS1Recycling.Frame) (stock : CPS1AtomicDynamics.Stock frame)
    (body : Body.State frame) (held : CPS1AtomicDynamics.Source.heldBody frame stock = some body) :
    CPS1AtomicDynamics.Species.body body ∈ stock := by
  induction stock with
  | nil => cases held
  | cons species rest ih =>
    cases species <;> first
    | exact List.mem_cons_of_mem _ (ih held)
    | simp only [CPS1AtomicDynamics.Source.heldBody,Option.some.injEq] at held
      cases held
      exact List.mem_cons_self

theorem capture_live_body (frame : CPS1Recycling.Frame)
    (previous : CPS1AtomicDynamics.Source.Occurrence frame) (body : Body.State frame)
    (held : CPS1AtomicDynamics.Source.heldBody frame previous.current.stock = some body) :
    (CPS1EnzymeBath.Source.start frame previous).stock.Perm
      (.joint (Joint.fromBody frame body) ::
        (previous.current.stock.erase (.body body)).map (CPS1EnzymeBath.Source.liftMaterial frame)) ∧
    (CPS1EnzymeBath.Source.start frame previous).captureRemaining = [] ∧
    (CPS1EnzymeBath.Source.start frame previous).cut = none ∧
    (CPS1EnzymeBath.Source.start frame previous).pending =
      previous.current.pending.map CPS1EnzymeBath.Source.liftBodyAction := by
  have present := body_member frame previous.current.stock body held
  have inventory := (List.perm_cons_erase present).map (CPS1EnzymeBath.Source.liftMaterial frame)
  have mapped : (previous.current.stock.map (CPS1EnzymeBath.Source.liftMaterial frame)).Perm
      (Species.retained (.body body) ::
        (previous.current.stock.erase (.body body)).map (CPS1EnzymeBath.Source.liftMaterial frame)) := inventory
  have paid := capture_actual frame body _ _ mapped
  simp only [CPS1EnzymeBath.Source.start,held]
  exact ⟨paid.2.2.2,paid.2.1,paid.2.2.1,True.intro⟩

theorem initial_pending_material (frame : CPS1Recycling.Frame)
    (previous : CPS1AtomicDynamics.Source.Occurrence frame) :
    (CPS1EnzymeBath.Source.start frame previous).pending =
      previous.current.pending.map CPS1EnzymeBath.Source.liftBodyAction := rfl

theorem actual_live_capture
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm (CPS1Reinitiation.Handover.rawFuel
      CPS1ResourceExecution.Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) (generated : 0 < CPS1EditingChemicalJoin.EditingStock.paid edits water additional)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (actions : List CPS1EnzymeBath.Source.RawAction) (feed : List Primary.TemplateKind) :
    ∃ (frame : CPS1Recycling.Frame) (current : CPS1EnzymeBath.Source.Occurrence frame) (body : Body.State frame),
      CPS1EnzymeBath.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth oldActions actions feed =
        some ⟨frame,current⟩ ∧
      CPS1AtomicDynamics.Source.heldBody frame current.previous.current.stock = some body ∧
      current.current = CPS1EnzymeBath.Source.advance frame (CPS1EnzymeBath.Source.start frame current.previous) actions feed ∧
      (CPS1EnzymeBath.Source.start frame current.previous).stock.Perm
        (.joint (Joint.fromBody frame body) ::
          (current.previous.current.stock.erase (.body body)).map (CPS1EnzymeBath.Source.liftMaterial frame)) ∧
      (CPS1EnzymeBath.Source.start frame current.previous).captureRemaining = [] ∧
      (CPS1EnzymeBath.Source.start frame current.previous).pending =
        current.previous.current.pending.map CPS1EnzymeBath.Source.liftBodyAction := by
  rcases Birth.actual_live_body edits water additional path recycleFeed recycleExtra recyclingRaw
    scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth generated oldActions with
    ⟨frame,previous,body,actual,held,unique,count⟩
  have captured := capture_live_body frame previous body held
  refine ⟨frame,⟨previous,CPS1EnzymeBath.Source.advance frame (CPS1EnzymeBath.Source.start frame previous) actions feed⟩,
    body,?_,held,rfl,captured.1,captured.2.1,captured.2.2.2⟩
  simp only [CPS1EnzymeBath.Source.execution,actual]
  rfl

end
end CPS1EnzymeBath.Actual
