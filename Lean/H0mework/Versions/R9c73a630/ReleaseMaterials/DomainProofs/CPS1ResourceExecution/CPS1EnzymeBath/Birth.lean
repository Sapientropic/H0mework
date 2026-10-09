import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Contract

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1EnzymeBath.Birth
noncomputable section
open CPS1AtomicDynamics

def selectBody (frame : CPS1Recycling.Frame) : Species frame → Option (Body.State frame)
  | .body state => some state
  | _ => none

def bodies (frame : CPS1Recycling.Frame) (stock : Stock frame) : List (Body.State frame) :=
  stock.filterMap (selectBody frame)

theorem held_body_readout (frame : CPS1Recycling.Frame) (stock : Stock frame) :
    Source.heldBody frame stock = (bodies frame stock).head? := by
  induction stock with
  | nil => rfl
  | cons species rest ih => cases species <;> first | exact ih | rfl

def markBody (frame : CPS1Recycling.Frame) : Species frame → Nat
  | .body _ => 1
  | _ => 0

def bodyCount (frame : CPS1Recycling.Frame) (stock : Stock frame) : Nat :=
  (stock.map (markBody frame)).sum

theorem body_count_readout (frame : CPS1Recycling.Frame) (stock : Stock frame) :
    bodyCount frame stock = (bodies frame stock).length := by
  induction stock with
  | nil => rfl
  | cons species rest ih =>
    cases species <;> simp only [bodyCount,bodies,List.map_cons,List.sum_cons,List.filterMap_cons,
      selectBody,markBody,List.length_cons,zero_add]
    all_goals first
    | exact ih
    | simpa only [bodyCount,bodies,Nat.add_comm] using congrArg (fun count : Nat => count+1) ih

theorem guard_blocks_fire (frame : CPS1Recycling.Frame) (reaction : Reaction frame)
    (failure : Body.Failure) (required : 0 < (reaction.reactants frame).count (.guard failure))
    (stock next : Stock frame) (empty : stock.count (.guard failure) = 0)
    (paid : CPS1ResourceExecution.Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock = .ok next) : False := by
  have balance := CPS1ResourceExecution.Inventory.fire_balance (Reaction.reactants frame) (Reaction.products frame) reaction stock next paid
    (.guard failure)
  rw [empty,Source.product_no_guard] at balance
  omega

theorem action_fire_body_count (frame : CPS1Recycling.Frame) (state : Body.State frame)
    (action : Source.RawAction) (stock next : Stock frame)
    (noGuard : ∀ failure, stock.count (.guard failure) = 0)
    (paid : CPS1ResourceExecution.Inventory.fire (Reaction.reactants frame) (Reaction.products frame)
      (action.reaction frame state) stock = .ok next) : bodyCount frame stock = bodyCount frame next := by
  cases action with
  | report address row =>
    cases computed : Body.report? frame state address row with
    | error failure =>
      apply False.elim
      apply guard_blocks_fire frame (.report state address row) failure _ stock next (noGuard failure) paid
      simp [Reaction.reactants,computed,guards]
    | ok current =>
      apply CPS1ResourceExecution.Inventory.fire_measure_preserved _ _ _ _ _ paid (markBody frame)
      simp [Source.RawAction.reaction,Reaction.reactants,Reaction.products,computed,guards,markBody]
  | deposit amount =>
    cases computed : Body.deposit? frame state amount with
    | error failure =>
      apply False.elim
      apply guard_blocks_fire frame (.deposit state amount) failure _ stock next (noGuard failure) paid
      simp [Reaction.reactants,computed,guards]
    | ok current =>
      apply CPS1ResourceExecution.Inventory.fire_measure_preserved _ _ _ _ _ paid (markBody frame)
      simp [Source.RawAction.reaction,Reaction.reactants,Reaction.products,computed,guards,markBody]
  | pulse dt =>
    cases computed : Body.pulse? frame state dt with
    | error failure =>
      apply False.elim
      apply guard_blocks_fire frame (.pulse state dt) failure _ stock next (noGuard failure) paid
      simp [Reaction.reactants,computed,guards]
    | ok current =>
      apply CPS1ResourceExecution.Inventory.fire_measure_preserved _ _ _ _ _ paid (markBody frame)
      simp [Source.RawAction.reaction,Reaction.reactants,Reaction.products,computed,guards,markBody]

theorem program_body_count (frame : CPS1Recycling.Frame) (actions : List Source.RawAction)
    (state : Body.State frame) (stock : Stock frame)
    (noGuard : ∀ failure, stock.count (.guard failure) = 0) :
    bodyCount frame (execute frame (Source.program frame state actions) stock).stock = bodyCount frame stock := by
  induction actions generalizing state stock with
  | nil => rfl
  | cons action rest ih =>
    change bodyCount frame (execute frame (action.reaction frame state ::
      Source.program frame (action.next frame state) rest) stock).stock = _
    rw [execute,CPS1ResourceExecution.Inventory.execute_cons]
    cases paid : CPS1ResourceExecution.Inventory.fire (Reaction.reactants frame) (Reaction.products frame)
        (action.reaction frame state) stock with
    | error missing => rfl
    | ok next =>
      have preserved := action_fire_body_count frame state action stock next noGuard paid
      have following : ∀ failure, next.count (.guard failure) = 0 := by
        intro failure
        have free := Source.execute_no_guard frame [action.reaction frame state] stock failure (noGuard failure)
        simpa only [execute,CPS1ResourceExecution.Inventory.execute,paid] using free
      exact (ih (action.next frame state) next following).trans preserved.symm

theorem raw_body_count (frame : CPS1Recycling.Frame) (actions : List Source.RawAction) :
    bodyCount frame (actions.flatMap (Source.RawAction.material frame)) = 0 := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
    cases action <;> simpa only [bodyCount,Source.RawAction.material,List.flatMap_cons,List.map_append,
      List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,markBody,zero_add] using ih

theorem advance_body_count (frame : CPS1Recycling.Frame) (cursor : Source.Cursor frame)
    (actions : List Source.RawAction) (captured : cursor.captureRemaining = [])
    (noGuard : ∀ failure, cursor.stock.count (.guard failure) = 0) :
    bodyCount frame (Source.advance frame cursor actions).stock = bodyCount frame cursor.stock := by
  let available := cursor.stock ++ actions.flatMap (Source.RawAction.material frame)
  have free : ∀ failure, available.count (.guard failure) = 0 := by
    intro failure
    simp only [available,List.count_append,noGuard failure,Source.raw_no_guard,zero_add]
  have total : bodyCount frame available = bodyCount frame cursor.stock := by
    simp only [available,bodyCount,List.map_append,List.sum_append]
    change bodyCount frame cursor.stock + bodyCount frame (actions.flatMap (Source.RawAction.material frame)) = _
    rw [raw_body_count,Nat.add_zero]
    rfl
  simp only [Source.advance,captured,List.nil_append]
  change bodyCount frame (execute frame
    (match Source.heldBody frame available with
    | some state => Source.program frame state (actions ++ cursor.pending) | none => []) available).stock = _
  cases held : Source.heldBody frame available with
  | none => exact total
  | some state => exact (program_body_count frame (actions ++ cursor.pending) state available free).trans total

theorem retained_body_count (frame : CPS1Recycling.Frame) (stock : CPS1AtomicSource.Current.Stock frame) :
    bodyCount frame (stock.map Species.retained) = 0 := by
  induction stock with
  | nil => rfl
  | cons species rest ih =>
    simpa only [bodyCount,List.map_cons,List.sum_cons,markBody,zero_add] using ih

theorem unique_body_held (frame : CPS1Recycling.Frame) (stock : Stock frame)
    (once : bodyCount frame stock = 1) :
    ∃ body, Source.heldBody frame stock = some body ∧ bodies frame stock = [body] := by
  have length := (body_count_readout frame stock).symm.trans once
  cases found : bodies frame stock with
  | nil =>
    rw [found] at length
    cases length
  | cons body rest =>
    have empty : rest = [] := by
      apply List.length_eq_zero_iff.mp
      rw [found,List.length_cons] at length
      omega
    subst rest
    refine ⟨body,?_,rfl⟩
    rw [held_body_readout,found]
    rfl

theorem actual_live_body
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm
      (CPS1Reinitiation.Handover.rawFuel
        CPS1ResourceExecution.Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) (generated : 0 < CPS1EditingChemicalJoin.EditingStock.paid edits water additional)
    (actions : List Source.RawAction) :
    ∃ (frame : CPS1Recycling.Frame) (current : Source.Occurrence frame) (body : Body.State frame),
      Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth actions = some ⟨frame,current⟩ ∧
      Source.heldBody frame current.current.stock = some body ∧
      bodies frame current.current.stock = [body] ∧ bodyCount frame current.current.stock = 1 := by
  rcases Actual.actual_start edits water additional path recycleFeed recycleExtra recyclingRaw
    scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth generated actions with
    ⟨frame,current,actual,advanced,inventory,captured,missing,valid,charge⟩
  have once : bodyCount frame (Source.start frame current.previous).stock = 1 := by
    have counted := (inventory.map (markBody frame)).sum_eq
    change bodyCount frame (Source.start frame current.previous).stock =
      1 + bodyCount frame ((current.previous.current.stock.erase
        (.atomic (CPS1LocalChemicalExecution.Chain.initial frame))).map Species.retained) at counted
    rw [retained_body_count,Nat.add_zero] at counted
    exact counted
  have updated : bodyCount frame current.current.stock = 1 := by
    rw [advanced]
    exact (advance_body_count frame (Source.start frame current.previous) actions captured
      (Source.start_no_guard frame current.previous)).trans once
  rcases unique_body_held frame current.current.stock updated with ⟨body,held,unique⟩
  exact ⟨frame,current,body,actual,held,unique,updated⟩

end
end CPS1EnzymeBath.Birth
