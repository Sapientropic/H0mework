import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Payment

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open CPS1ResourceExecution
variable {frame : CPS1Recycling.Frame}

def GoodStock (stock : Stock frame) : Prop :=
  (∀ state, Species.retained (.retained (.quantum state)) ∈ stock → CPS1ElectronicEvolution.Consumer.Good state) ∧
    (∀ state, Species.following state ∈ stock → CPS1ElectronicEvolution.Consumer.Good state)

def NoGuardStock (stock : Stock frame) : Prop :=
  (∀ failure, Species.guard failure ∉ stock) ∧
    (∀ failure, Species.retained (.guard failure) ∉ stock) ∧
    (∀ failure, Species.retained (.retained (.guard failure)) ∉ stock) ∧
      Species.retained (.retained .missingCarrier) ∉ stock

theorem reaction_good (reaction : Reaction frame) (good : GoodStock (reaction.reactants frame)) :
    GoodStock (reaction.products frame) := by
  cases reaction with
  | retained old =>
    have prior : CPS1QuantumNuclear.GoodStock (old.reactants frame) := by
      intro state member
      exact good.1 state (List.mem_map.mpr ⟨_,member,rfl⟩)
    constructor
    · intro state member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact CPS1QuantumNuclear.reaction_good old prior state present
    · intro state member
      rcases List.mem_map.mp member with ⟨species,_,same⟩
      cases same
  | relocate before =>
    have prior := good.1 before (by simp [Reaction.reactants])
    cases updated : relocate? before with
    | error failure => simp [Reaction.products,updated,GoodStock]
    | ok next =>
      refine ⟨?_,?_⟩
      · intro state member
        simp [Reaction.products,updated] at member
      · intro state member
        simp [Reaction.products,updated] at member
        subst state
        exact relocate_good before next updated prior
  | pulse before time =>
    have prior := good.2 before (by simp [Reaction.reactants])
    cases updated : pulse? before time with
    | error failure => simp [Reaction.products,updated,GoodStock]
    | ok next =>
      refine ⟨?_,?_⟩
      · intro state member
        simp [Reaction.products,updated] at member
      · intro state member
        simp [Reaction.products,updated] at member
        subst state
        exact pulse_good before time next updated prior
  | deposit before amount =>
    have prior := good.2 before (by simp [Reaction.reactants])
    cases updated : deposit? before amount with
    | error failure => simp [Reaction.products,updated,GoodStock]
    | ok next =>
      refine ⟨?_,?_⟩
      · intro state member
        simp [Reaction.products,updated] at member
      · intro state member
        simp [Reaction.products,updated] at member
        subst state
        exact deposit_good before amount next updated prior
  | keepFollowing before =>
    refine ⟨?_,?_⟩
    · intro state member
      simp [Reaction.products] at member
    · intro state member
      simp [Reaction.products] at member
      subst state
      exact good.2 before (by simp [Reaction.reactants])

theorem good_of_subset {left right : Stock frame} (subset : ∀ species ∈ right, species ∈ left)
    (good : GoodStock left) : GoodStock right :=
  ⟨fun state member => good.1 state (subset _ member),fun state member => good.2 state (subset _ member)⟩

theorem good_append {left right : Stock frame} (first : GoodStock left) (second : GoodStock right) :
    GoodStock (left++right) := by
  constructor
  · intro state member
    rcases List.mem_append.mp member with l | r
    · exact first.1 state l
    · exact second.1 state r
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
  | retained old =>
    have safe := CPS1QuantumNuclear.products_noGuard old
    refine ⟨?_,?_,?_,?_⟩
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,_,same⟩
      cases same
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact safe.1 failure present
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact safe.2.1 failure present
    · intro member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact safe.2.2 present
  | relocate state => cases updated : relocate? state <;> simp [Reaction.products,updated,NoGuardStock]
  | pulse state time => cases updated : pulse? state time <;> simp [Reaction.products,updated,NoGuardStock]
  | deposit state amount => cases updated : deposit? state amount <;> simp [Reaction.products,updated,NoGuardStock]
  | keepFollowing state => simp [Reaction.products,NoGuardStock]

theorem noGuard_of_subset {left right : Stock frame} (subset : ∀ species ∈ right, species ∈ left)
    (safe : NoGuardStock left) : NoGuardStock right :=
  ⟨fun failure member => safe.1 failure (subset _ member),
    fun failure member => safe.2.1 failure (subset _ member),
    fun failure member => safe.2.2.1 failure (subset _ member),
    fun member => safe.2.2.2 (subset _ member)⟩

theorem noGuard_append {left right : Stock frame} (first : NoGuardStock left) (second : NoGuardStock right) :
    NoGuardStock (left++right) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro failure member
    rcases List.mem_append.mp member with l | r
    · exact first.1 failure l
    · exact second.1 failure r
  · intro failure member
    rcases List.mem_append.mp member with l | r
    · exact first.2.1 failure l
    · exact second.2.1 failure r
  · intro failure member
    rcases List.mem_append.mp member with l | r
    · exact first.2.2.1 failure l
    · exact second.2.2.1 failure r
  · intro member
    rcases List.mem_append.mp member with l | r
    · exact first.2.2.2 l
    · exact second.2.2.2 r

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
    | error missing =>
      rw [Inventory.execute_cons,fired]
      exact good
    | ok next =>
      rw [Inventory.execute_cons,fired]
      exact ih next (fire_good action stock next good fired)

theorem execute_noGuard (program : List (Reaction frame)) (stock : Stock frame) (safe : NoGuardStock stock) :
    NoGuardStock (execute frame program stock).stock := by
  induction program generalizing stock with
  | nil => exact safe
  | cons action rest ih =>
    change NoGuardStock (Inventory.execute (Reaction.reactants frame) (Reaction.products frame) (action :: rest) stock).stock
    cases fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) action stock with
    | error missing =>
      rw [Inventory.execute_cons,fired]
      exact safe
    | ok next =>
      rw [Inventory.execute_cons,fired]
      exact ih next (fire_noGuard action stock next safe fired)

theorem raw_good (action : Source.RawAction) : GoodStock (action.material frame) := by
  cases action with
  | old action =>
    have prior := CPS1QuantumNuclear.raw_good (frame := frame) action
    constructor
    · intro state member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact prior state present
    · intro state member
      rcases List.mem_map.mp member with ⟨species,_,same⟩
      cases same
  | relocate => simp [GoodStock,Source.RawAction.material]
  | pulse time => simp [GoodStock,Source.RawAction.material]
  | deposit amount => simp [GoodStock,Source.RawAction.material]

theorem raw_noGuard (action : Source.RawAction) : NoGuardStock (action.material frame) := by
  cases action with
  | old action =>
    have prior := CPS1QuantumNuclear.raw_noGuard (frame := frame) action
    refine ⟨?_,?_,?_,?_⟩
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,_,same⟩
      cases same
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact prior.1 failure present
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact prior.2.1 failure present
    · intro member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact prior.2.2 present
  | relocate => simp [NoGuardStock,Source.RawAction.material]
  | pulse time => simp [NoGuardStock,Source.RawAction.material]
  | deposit amount => simp [NoGuardStock,Source.RawAction.material]

theorem old_stock_good (stock : CPS1QuantumNuclear.Stock frame) (good : CPS1QuantumNuclear.GoodStock stock) :
    GoodStock (stock.map Species.retained) := by
  constructor
  · intro state member
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    exact good state present
  · intro state member
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same

theorem old_stock_noGuard (stock : CPS1QuantumNuclear.Stock frame) (safe : CPS1QuantumNuclear.NoGuardStock stock) :
    NoGuardStock (stock.map Species.retained) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro failure member
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same
  · intro failure member
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    exact safe.1 failure present
  · intro failure member
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    exact safe.2.1 failure present
  · intro member
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    exact safe.2.2 present


theorem actions_good (actions : List Source.RawAction) :
    GoodStock (actions.flatMap (Source.RawAction.material frame)) := by
  induction actions with
  | nil => simp [GoodStock]
  | cons action rest ih => exact good_append (raw_good action) ih

theorem actions_noGuard (actions : List Source.RawAction) :
    NoGuardStock (actions.flatMap (Source.RawAction.material frame)) := by
  induction actions with
  | nil => simp [NoGuardStock]
  | cons action rest ih => exact noGuard_append (raw_noGuard action) ih

theorem feed_good (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    GoodStock (feed.map (fun kind => Species.retained (.retained (.retained
      (CPS1EnzymeBath.componentSpecies frame kind))))) := by
  have same : (feed.map (fun kind => Species.retained (.retained (.retained
      (CPS1EnzymeBath.componentSpecies frame kind))))) =
      (feed.map (fun kind => CPS1QuantumNuclear.Species.retained (.retained
        (CPS1EnzymeBath.componentSpecies frame kind)))).map Species.retained := by
    rw [List.map_map]
    rfl
  rw [same]
  exact old_stock_good _ (CPS1QuantumNuclear.feed_good feed)

theorem feed_noGuard (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    NoGuardStock (feed.map (fun kind => Species.retained (.retained (.retained
      (CPS1EnzymeBath.componentSpecies frame kind))))) := by
  have same : (feed.map (fun kind => Species.retained (.retained (.retained
      (CPS1EnzymeBath.componentSpecies frame kind))))) =
      (feed.map (fun kind => CPS1QuantumNuclear.Species.retained (.retained
        (CPS1EnzymeBath.componentSpecies frame kind)))).map Species.retained := by
    rw [List.map_map]
    rfl
  rw [same]
  exact old_stock_noGuard _ (CPS1QuantumNuclear.feed_noGuard feed)

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
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind)
    (current : Σ frame : CPS1Recycling.Frame, Source.Occurrence frame)
    (actual : Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed actions feed = some current) :
    GoodStock current.2.current.stock ∧ NoGuardStock current.2.current.stock := by
  unfold Source.execution at actual
  cases prior : CPS1QuantumNuclear.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed with
  | none => simp [prior] at actual
  | some previous =>
    simp only [prior] at actual
    have same := Option.some.inj actual
    cases same
    have paid := CPS1QuantumNuclear.source_stock edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed previous prior
    exact ⟨advance_good _ actions feed (old_stock_good _ paid.1),
      advance_noGuard _ actions feed (old_stock_noGuard _ paid.2)⟩

end
end CPS1Following
