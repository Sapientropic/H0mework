import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Source

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource.Actual
noncomputable section
open CPS1ResourceExecution
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
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    ∃ (frame : CPS1Recycling.Frame) (previous : CPS1EnzymeBath.Source.Occurrence frame)
      (current : Source.Occurrence frame),
      CPS1EnzymeBath.Source.generatedExecution edits water additional path recycleFeed scanFeed bodyFeed depth
        oldActions bathActions bathFeed = some ⟨frame,previous⟩ ∧
      Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
        oldActions bathActions bathFeed actions feed = some ⟨frame,current⟩ ∧
      current.previous = previous ∧
      current.current = Source.advance frame (Source.start frame previous) actions feed := by
  rcases CPS1EnzymeBath.Partner.actual_generated_partner edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw
    depth generated oldActions bathActions bathFeed with
    ⟨frame,previous,body,surplus,actual,remaining⟩
  let current : Source.Occurrence frame :=
    ⟨previous,Source.advance frame (Source.start frame previous) actions feed⟩
  refine ⟨frame,previous,current,actual,?_,rfl,rfl⟩
  simp only [Source.execution,actual]
  rfl

def carrierSpecies (frame : CPS1Recycling.Frame) : Carrier frame → Species frame
  | .joint joint => .retained (.joint joint)
  | .quantum state => .quantum state

theorem carrier_member (frame : CPS1Recycling.Frame) (stock : Stock frame) (carrier : Carrier frame)
    (held : Source.heldCarrier frame stock = some carrier) :
    carrierSpecies frame carrier ∈ stock := by
  induction stock with
  | nil => cases held
  | cons species rest ih =>
    cases species with
    | retained old =>
      cases old with
      | joint joint =>
        simp only [Source.heldCarrier,Option.some.injEq] at held
        cases held
        exact List.mem_cons_self
      | _ => exact List.mem_cons_of_mem _ (ih held)
    | quantum state =>
      simp only [Source.heldCarrier,Option.some.injEq] at held
      cases held
      exact List.mem_cons_self
    | _ => exact List.mem_cons_of_mem _ (ih held)

theorem prepare_actual (frame : CPS1Recycling.Frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (state : State frame) (stock : Stock frame)
    (held : Source.heldCarrier frame stock = some (.joint joint))
    (prepared : State.fromJoint? frame joint = .ok state) :
    execute frame [.prepare joint] stock =
      ⟨[.prepare joint],[],.quantum state :: stock.erase (.retained (.joint joint)),none⟩ := by
  have present := carrier_member frame stock (.joint joint) held
  change Species.retained (.joint joint) ∈ stock at present
  have fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) (.prepare joint) stock =
      .ok (.quantum state :: stock.erase (.retained (.joint joint))) := by
    simp [Inventory.fire,Reaction.reactants,guards,prepared,Inventory.consume,present,Reaction.products]
  rw [execute,Inventory.execute_cons,fired]

theorem program_length (frame : CPS1Recycling.Frame) (actions : List Source.RawAction)
    (carrier : Option (Carrier frame)) : (Source.program frame carrier actions).length = actions.length := by
  induction actions generalizing carrier with
  | nil => rfl
  | cons action rest ih =>
    change (Source.program frame (action.next frame carrier) rest).length + 1 = rest.length+1
    rw [ih]

theorem raw_cut_suffix (frame : CPS1Recycling.Frame) (cursor : Source.Cursor frame)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    let available := cursor.stock ++
      feed.map (fun kind => Species.retained (CPS1EnzymeBath.componentSpecies frame kind)) ++
      actions.flatMap (Source.RawAction.material frame)
    let requested := actions ++ cursor.pending
    let result := execute frame (Source.program frame (Source.heldCarrier frame available) requested) available
    (Source.advance frame cursor actions feed).pending = requested.drop result.fired.length ∧
      (Source.advance frame cursor actions feed).pending.length = result.remaining.length := by
  dsimp only
  refine ⟨rfl,?_⟩
  have decomposition := Inventory.execution_decomposes (Reaction.reactants frame) (Reaction.products frame)
    (Source.program frame (Source.heldCarrier frame
      (cursor.stock ++ feed.map (fun kind => Species.retained (CPS1EnzymeBath.componentSpecies frame kind)) ++
        actions.flatMap (Source.RawAction.material frame))) (actions ++ cursor.pending))
    (cursor.stock ++ feed.map (fun kind => Species.retained (CPS1EnzymeBath.componentSpecies frame kind)) ++
      actions.flatMap (Source.RawAction.material frame))
  have lengths := congrArg List.length decomposition
  rw [List.length_append,program_length] at lengths
  simp only [Source.advance,List.length_drop]
  dsimp only [execute] at lengths ⊢
  omega

end
end CPS1ElectronicSource.Actual
