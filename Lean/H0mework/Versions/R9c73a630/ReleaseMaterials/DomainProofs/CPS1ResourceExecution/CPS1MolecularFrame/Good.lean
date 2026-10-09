import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Payment
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Good

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ResourceExecution
variable {frame : CPS1Recycling.Frame}

def selectRetained : Species frame → Option (CPS1Following.Species frame)
  | .retained species => some species
  | _ => none

def retainedStock (stock : Stock frame) : CPS1Following.Stock frame := stock.filterMap selectRetained

def GoodStock (stock : Stock frame) : Prop :=
  CPS1Following.GoodStock (retainedStock stock) ∧
    ∀ state, Species.molecular state ∈ stock → Good state

def NoGuardStock (stock : Stock frame) : Prop :=
  (∀ failure, Species.guard failure ∉ stock) ∧ Species.missingCarrier ∉ stock ∧
    CPS1Following.NoGuardStock (retainedStock stock)

theorem retained_mem (stock : Stock frame) (species : CPS1Following.Species frame) :
    species ∈ retainedStock stock ↔ Species.retained species ∈ stock := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with ⟨old,present,same⟩
    cases old with
    | retained prior =>
      have identified := Option.some.inj same
      cases identified
      exact present
    | molecular state => cases same
    | spentAdopt reference => cases same
    | spentPulse before time => cases same
    | guard failure => cases same
    | missingCarrier => cases same
  · intro member
    exact List.mem_filterMap.mpr ⟨.retained species,member,rfl⟩

theorem retained_map (stock : CPS1Following.Stock frame) : retainedStock (stock.map Species.retained) = stock := by
  have identity : selectRetained ∘ (Species.retained : CPS1Following.Species frame → Species frame) = some := rfl
  simp only [retainedStock,List.filterMap_map,identity,List.filterMap_some]

theorem old_stock_good (stock : CPS1Following.Stock frame) (good : CPS1Following.GoodStock stock) :
    GoodStock (stock.map Species.retained) := by
  refine ⟨?_,?_⟩
  · rw [retained_map]
    exact good
  · intro state member
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same

theorem old_stock_noGuard (stock : CPS1Following.Stock frame) (safe : CPS1Following.NoGuardStock stock) :
    NoGuardStock (stock.map Species.retained) := by
  refine ⟨?_,?_,?_⟩
  · intro failure member
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same
  · intro member
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same
  · rw [retained_map]
    exact safe

theorem reaction_good (reaction : Reaction frame) (good : GoodStock (reaction.reactants frame)) :
    GoodStock (reaction.products frame) := by
  cases reaction with
  | retained old =>
    have prior : CPS1Following.GoodStock (old.reactants frame) := by
      simpa only [Reaction.reactants,retained_map] using good.1
    exact old_stock_good _ (CPS1Following.reaction_good old prior)
  | adopt reference =>
    cases updated : adopt? reference with
    | error failure => simp [Reaction.products,updated,GoodStock,retainedStock,CPS1Following.GoodStock]
    | ok next =>
      simpa [Reaction.products,updated,GoodStock,retainedStock,selectRetained,CPS1Following.GoodStock]
        using adopt_good reference next updated
  | pulse before time =>
    have prior := good.2 before (by simp [Reaction.reactants])
    cases updated : before.pulse? time with
    | error failure => simp [Reaction.products,updated,GoodStock,retainedStock,CPS1Following.GoodStock]
    | ok next =>
      simpa [Reaction.products,updated,GoodStock,retainedStock,selectRetained,CPS1Following.GoodStock]
        using pulse_good before next time updated prior
  | deposit before amount =>
    have prior := good.2 before (by simp [Reaction.reactants])
    cases updated : before.deposit? amount with
    | error failure => simp [Reaction.products,updated,GoodStock,retainedStock,CPS1Following.GoodStock]
    | ok next =>
      simpa [Reaction.products,updated,GoodStock,retainedStock,selectRetained,CPS1Following.GoodStock]
        using deposit_good before next amount updated prior
  | keepMolecular before =>
    have prior := good.2 before (by simp [Reaction.reactants])
    simpa [Reaction.products,GoodStock,retainedStock,selectRetained,CPS1Following.GoodStock] using prior
  | requireCarrier => simp [Reaction.products,GoodStock,retainedStock,CPS1Following.GoodStock]

theorem good_of_subset {left right : Stock frame} (subset : ∀ species ∈ right, species ∈ left)
    (good : GoodStock left) : GoodStock right := by
  refine ⟨CPS1Following.good_of_subset ?_ good.1,fun state member => good.2 state (subset _ member)⟩
  intro species member
  exact (retained_mem left species).mpr (subset _ ((retained_mem right species).mp member))

theorem good_append {left right : Stock frame} (first : GoodStock left) (second : GoodStock right) :
    GoodStock (left++right) := by
  refine ⟨?_,?_⟩
  · simpa only [retainedStock,List.filterMap_append] using CPS1Following.good_append first.1 second.1
  · intro state member
    rcases List.mem_append.mp member with l | r
    · exact first.2 state l
    · exact second.2 state r

theorem fire_good (reaction : Reaction frame) (stock next : Stock frame) (good : GoodStock stock)
    (actual : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock = .ok next) :
    GoodStock next := by
  unfold Inventory.fire at actual
  cases consumed : Inventory.consume (reaction.reactants frame) stock with
  | error missing => simp [consumed] at actual
  | ok remainder =>
    simp only [consumed,Except.ok.injEq] at actual
    subst next
    have decomposition := Inventory.consume_perm _ _ _ consumed
    have input := good_of_subset
      (fun species member => decomposition.mem_iff.mpr (List.mem_append_left _ member)) good
    have rest := good_of_subset
      (fun species member => decomposition.mem_iff.mpr (List.mem_append_right _ member)) good
    exact good_append (reaction_good reaction input) rest

theorem products_noGuard (reaction : Reaction frame) : NoGuardStock (reaction.products frame) := by
  cases reaction with
  | retained old => exact old_stock_noGuard _ (CPS1Following.products_noGuard old)
  | adopt reference => cases updated : adopt? reference <;>
      simp [Reaction.products,updated,NoGuardStock,retainedStock,selectRetained,CPS1Following.NoGuardStock]
  | pulse state time => cases updated : state.pulse? time <;>
      simp [Reaction.products,updated,NoGuardStock,retainedStock,selectRetained,CPS1Following.NoGuardStock]
  | deposit state amount => cases updated : state.deposit? amount <;>
      simp [Reaction.products,updated,NoGuardStock,retainedStock,selectRetained,CPS1Following.NoGuardStock]
  | keepMolecular state =>
      simp [Reaction.products,NoGuardStock,retainedStock,selectRetained,CPS1Following.NoGuardStock]
  | requireCarrier => simp [Reaction.products,NoGuardStock,retainedStock,CPS1Following.NoGuardStock]

theorem noGuard_of_subset {left right : Stock frame} (subset : ∀ species ∈ right, species ∈ left)
    (safe : NoGuardStock left) : NoGuardStock right := by
  refine ⟨fun failure member => safe.1 failure (subset _ member),
    fun member => safe.2.1 (subset _ member),CPS1Following.noGuard_of_subset ?_ safe.2.2⟩
  intro species member
  exact (retained_mem left species).mpr (subset _ ((retained_mem right species).mp member))

theorem noGuard_append {left right : Stock frame} (first : NoGuardStock left) (second : NoGuardStock right) :
    NoGuardStock (left++right) := by
  refine ⟨?_,?_,?_⟩
  · intro failure member
    rcases List.mem_append.mp member with l | r
    · exact first.1 failure l
    · exact second.1 failure r
  · intro member
    rcases List.mem_append.mp member with l | r
    · exact first.2.1 l
    · exact second.2.1 r
  · simpa only [retainedStock,List.filterMap_append] using CPS1Following.noGuard_append first.2.2 second.2.2

theorem fire_noGuard (reaction : Reaction frame) (stock next : Stock frame) (safe : NoGuardStock stock)
    (actual : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock = .ok next) :
    NoGuardStock next := by
  unfold Inventory.fire at actual
  cases consumed : Inventory.consume (reaction.reactants frame) stock with
  | error missing => simp [consumed] at actual
  | ok remainder =>
    simp only [consumed,Except.ok.injEq] at actual
    subst next
    have decomposition := Inventory.consume_perm _ _ _ consumed
    have rest := noGuard_of_subset
      (fun species member => decomposition.mem_iff.mpr (List.mem_append_right _ member)) safe
    exact noGuard_append (products_noGuard reaction) rest

theorem execute_good (program : List (Reaction frame)) (stock : Stock frame) (good : GoodStock stock) :
    GoodStock (execute frame program stock).stock := by
  induction program generalizing stock with
  | nil => exact good
  | cons action rest ih =>
    change GoodStock (Inventory.execute (Reaction.reactants frame) (Reaction.products frame) (action :: rest) stock).stock
    cases fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) action stock with
    | error missing => rw [Inventory.execute_cons,fired]; exact good
    | ok next => rw [Inventory.execute_cons,fired]; exact ih next (fire_good action stock next good fired)

theorem execute_noGuard (program : List (Reaction frame)) (stock : Stock frame) (safe : NoGuardStock stock) :
    NoGuardStock (execute frame program stock).stock := by
  induction program generalizing stock with
  | nil => exact safe
  | cons action rest ih =>
    change NoGuardStock (Inventory.execute (Reaction.reactants frame) (Reaction.products frame) (action :: rest) stock).stock
    cases fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) action stock with
    | error missing => rw [Inventory.execute_cons,fired]; exact safe
    | ok next => rw [Inventory.execute_cons,fired]; exact ih next (fire_noGuard action stock next safe fired)

theorem raw_good (action : Source.RawAction) : GoodStock (action.material frame) := by
  cases action with
  | old action => exact old_stock_good _ (CPS1Following.raw_good action)
  | adopt => simp [GoodStock,Source.RawAction.material,retainedStock,CPS1Following.GoodStock]
  | pulse time => simp [GoodStock,Source.RawAction.material,retainedStock,selectRetained,CPS1Following.GoodStock]
  | deposit amount => simp [GoodStock,Source.RawAction.material,retainedStock,selectRetained,CPS1Following.GoodStock]

theorem raw_noGuard (action : Source.RawAction) : NoGuardStock (action.material frame) := by
  cases action with
  | old action => exact old_stock_noGuard _ (CPS1Following.raw_noGuard action)
  | adopt => simp [NoGuardStock,Source.RawAction.material,retainedStock,CPS1Following.NoGuardStock]
  | pulse time => simp [NoGuardStock,Source.RawAction.material,retainedStock,selectRetained,CPS1Following.NoGuardStock]
  | deposit amount => simp [NoGuardStock,Source.RawAction.material,retainedStock,selectRetained,CPS1Following.NoGuardStock]

theorem actions_good (actions : List Source.RawAction) : GoodStock (actions.flatMap (Source.RawAction.material frame)) := by
  induction actions with
  | nil => simp [GoodStock,retainedStock,CPS1Following.GoodStock]
  | cons action rest ih => exact good_append (raw_good action) ih

theorem actions_noGuard (actions : List Source.RawAction) : NoGuardStock (actions.flatMap (Source.RawAction.material frame)) := by
  induction actions with
  | nil => simp [NoGuardStock,retainedStock,CPS1Following.NoGuardStock]
  | cons action rest ih => exact noGuard_append (raw_noGuard action) ih

theorem feed_good (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    GoodStock (feed.map (fun kind => Species.retained (.retained (.retained (.retained
      (CPS1EnzymeBath.componentSpecies frame kind)))))) := by
  have same : (feed.map (fun kind => Species.retained (.retained (.retained (.retained
      (CPS1EnzymeBath.componentSpecies frame kind)))))) =
      (feed.map (fun kind => CPS1Following.Species.retained (.retained (.retained
        (CPS1EnzymeBath.componentSpecies frame kind))))).map Species.retained := by
    rw [List.map_map]
    rfl
  rw [same]
  exact old_stock_good _ (CPS1Following.feed_good feed)

theorem feed_noGuard (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    NoGuardStock (feed.map (fun kind => Species.retained (.retained (.retained (.retained
      (CPS1EnzymeBath.componentSpecies frame kind)))))) := by
  have same : (feed.map (fun kind => Species.retained (.retained (.retained (.retained
      (CPS1EnzymeBath.componentSpecies frame kind)))))) =
      (feed.map (fun kind => CPS1Following.Species.retained (.retained (.retained
        (CPS1EnzymeBath.componentSpecies frame kind))))).map Species.retained := by
    rw [List.map_map]
    rfl
  rw [same]
  exact old_stock_noGuard _ (CPS1Following.feed_noGuard feed)

theorem advance_good (cursor : Source.Cursor frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (good : GoodStock cursor.stock) :
    GoodStock (Source.advance frame cursor actions feed).stock :=
  execute_good _ _ (good_append (good_append good (feed_good feed)) (actions_good actions))

theorem advance_noGuard (cursor : Source.Cursor frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (safe : NoGuardStock cursor.stock) :
    NoGuardStock (Source.advance frame cursor actions feed).stock :=
  execute_noGuard _ _ (noGuard_append (noGuard_append safe (feed_noGuard feed)) (actions_noGuard actions))

theorem resume_good (current : Source.Occurrence frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (good : GoodStock current.current.stock) :
    GoodStock (Source.resume frame current actions feed).current.stock := advance_good _ actions feed good

theorem resume_noGuard (current : Source.Occurrence frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (safe : NoGuardStock current.current.stock) :
    NoGuardStock (Source.resume frame current actions feed).current.stock := advance_noGuard _ actions feed safe

theorem source_stock
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind)
    (current : Σ frame : CPS1Recycling.Frame, Source.Occurrence frame)
    (actual : Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed actions feed = some current) :
    GoodStock current.2.current.stock ∧ NoGuardStock current.2.current.stock := by
  unfold Source.execution at actual
  cases prior : CPS1Following.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed with
  | none => simp [prior] at actual
  | some previous =>
    simp only [prior] at actual
    have same := Option.some.inj actual
    cases same
    have paid := CPS1Following.source_stock edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed previous prior
    exact ⟨advance_good _ actions feed (old_stock_good _ paid.1),
      advance_noGuard _ actions feed (old_stock_noGuard _ paid.2)⟩

end
end CPS1MolecularFrame
