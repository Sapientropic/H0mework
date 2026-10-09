import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Birth

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1EnzymeBath.BathAccounting
noncomputable section

def sourceCp (frame : CPS1Recycling.Frame) : CPS1LocalChemicalExecution.Species frame :=
  CPS1LocalChemicalExecution.molecule frame .carbamoylPhosphate

def atomicCp (frame : CPS1Recycling.Frame) : CPS1AtomicSource.Current.Species frame :=
  .retained (sourceCp frame)

def currentCp (frame : CPS1Recycling.Frame) : CPS1AtomicDynamics.Species frame :=
  .retained (atomicCp frame)

theorem trace_count_zero {S R : Type} [DecidableEq S] (material : R → List S) (species : S)
    (empty : ∀ reaction, (material reaction).count species = 0) (trace : List R) :
    (trace.flatMap material).count species = 0 := by
  induction trace with
  | nil => rfl
  | cons reaction rest ih => simp only [List.flatMap_cons,List.count_append,empty,ih,zero_add]

theorem execute_count_preserved {S R : Type} [DecidableEq S]
    (reactants products : R → List S) (species : S)
    (inputs : ∀ reaction, (reactants reaction).count species = 0)
    (outputs : ∀ reaction, (products reaction).count species = 0) (program : List R) (stock : List S) :
    (CPS1ResourceExecution.Inventory.execute reactants products program stock).stock.count species = stock.count species := by
  have balanced := CPS1ResourceExecution.Inventory.execution_balance reactants products program stock species
  rw [trace_count_zero products species outputs,trace_count_zero reactants species inputs,Nat.add_zero,Nat.add_zero] at balanced
  exact balanced.symm

theorem atomic_reactants_no_cp (frame : CPS1Recycling.Frame) (reaction : CPS1AtomicSource.Current.Reaction frame) :
    (reaction.reactants frame).count (atomicCp frame) = 0 := by
  cases reaction <;> simp [CPS1AtomicSource.Current.Reaction.reactants,atomicCp,sourceCp,
    CPS1AtomicSource.Current.proton,CPS1LocalChemicalExecution.molecule,List.count_replicate]

theorem atomic_products_no_cp (frame : CPS1Recycling.Frame) (reaction : CPS1AtomicSource.Current.Reaction frame) :
    (reaction.products frame).count (atomicCp frame) = 0 := by
  cases reaction <;> simp [CPS1AtomicSource.Current.Reaction.products,atomicCp]

theorem atomic_cp_count (frame : CPS1Recycling.Frame)
    (previous : CPS1EditingChemicalJoin.Source.Occurrence frame) :
    (CPS1AtomicSource.Current.fromActual frame previous).current.stock.count (atomicCp frame) =
      previous.current.stock.count (sourceCp frame) := by
  have preserved := execute_count_preserved
    (CPS1AtomicSource.Current.Reaction.reactants frame) (CPS1AtomicSource.Current.Reaction.products frame)
    (atomicCp frame) (atomic_reactants_no_cp frame) (atomic_products_no_cp frame)
    (match CPS1LocalChemicalExecution.Source.heldChain frame previous.current.stock with
      | none => [.requireChain] | some chain => [.atomize chain])
    (previous.current.stock.map CPS1AtomicSource.Current.Species.retained)
  change (CPS1AtomicSource.Current.fromActual frame previous).current.stock.count (atomicCp frame) = _ at preserved
  rw [preserved]
  exact List.count_map_of_injective previous.current.stock (CPS1AtomicSource.Current.Species.retained (frame := frame))
    (fun _ _ same => CPS1AtomicSource.Current.Species.retained.inj same) (sourceCp frame)

theorem retained_reactants_zero (frame : CPS1Recycling.Frame) (old : CPS1AtomicSource.Current.Species frame)
    (notAtomic : ∀ chain, old ≠ .atomic chain) (reaction : CPS1AtomicDynamics.Reaction frame) :
    (reaction.reactants frame).count (.retained old) = 0 := by
  cases reaction with
  | capture chain => simp [CPS1AtomicDynamics.Reaction.reactants,(notAtomic chain).symm]
  | requireAtomic => rfl
  | report state address row =>
    cases computed : CPS1AtomicDynamics.Body.report? frame state address row <;>
      simp [CPS1AtomicDynamics.Reaction.reactants,computed,CPS1AtomicDynamics.guards]
  | deposit state amount =>
    cases computed : CPS1AtomicDynamics.Body.deposit? frame state amount <;>
      simp [CPS1AtomicDynamics.Reaction.reactants,computed,CPS1AtomicDynamics.guards]
  | pulse state dt =>
    cases computed : CPS1AtomicDynamics.Body.pulse? frame state dt <;>
      simp [CPS1AtomicDynamics.Reaction.reactants,computed,CPS1AtomicDynamics.guards]

theorem retained_products_zero (frame : CPS1Recycling.Frame) (old : CPS1AtomicSource.Current.Species frame)
    (reaction : CPS1AtomicDynamics.Reaction frame) :
    (reaction.products frame).count (.retained old) = 0 := by
  cases reaction with
  | capture chain => rfl
  | requireAtomic => rfl
  | report state address row =>
    cases computed : CPS1AtomicDynamics.Body.report? frame state address row <;>
      simp [CPS1AtomicDynamics.Reaction.products,computed]
  | deposit state amount =>
    cases computed : CPS1AtomicDynamics.Body.deposit? frame state amount <;>
      simp [CPS1AtomicDynamics.Reaction.products,computed]
  | pulse state dt =>
    cases computed : CPS1AtomicDynamics.Body.pulse? frame state dt <;>
      simp [CPS1AtomicDynamics.Reaction.products,computed]

theorem execute_retained_count (frame : CPS1Recycling.Frame) (old : CPS1AtomicSource.Current.Species frame)
    (notAtomic : ∀ chain, old ≠ .atomic chain) (program : List (CPS1AtomicDynamics.Reaction frame))
    (stock : CPS1AtomicDynamics.Stock frame) :
    (CPS1AtomicDynamics.execute frame program stock).stock.count (.retained old) = stock.count (.retained old) :=
  execute_count_preserved (CPS1AtomicDynamics.Reaction.reactants frame) (CPS1AtomicDynamics.Reaction.products frame)
    (.retained old) (retained_reactants_zero frame old notAtomic) (retained_products_zero frame old) program stock

theorem start_cp_count (frame : CPS1Recycling.Frame) (previous : CPS1AtomicSource.Current.Occurrence frame) :
    (CPS1AtomicDynamics.Source.start frame previous).stock.count (currentCp frame) =
      previous.current.stock.count (atomicCp frame) := by
  have preserved := execute_retained_count frame (atomicCp frame) (fun _ same => by cases same)
    (match CPS1AtomicDynamics.Source.heldAtomic frame previous.current.stock with
      | some chain => [.capture chain] | none => [.requireAtomic])
    (previous.current.stock.map CPS1AtomicDynamics.Species.retained)
  change (CPS1AtomicDynamics.Source.start frame previous).stock.count (currentCp frame) = _ at preserved
  rw [preserved]
  exact List.count_map_of_injective previous.current.stock (CPS1AtomicDynamics.Species.retained (frame := frame))
    (fun _ _ same => CPS1AtomicDynamics.Species.retained.inj same) (atomicCp frame)

theorem raw_no_cp (frame : CPS1Recycling.Frame) (actions : List CPS1AtomicDynamics.Source.RawAction) :
    (actions.flatMap (CPS1AtomicDynamics.Source.RawAction.material frame)).count (currentCp frame) = 0 := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
    cases action <;> simpa [CPS1AtomicDynamics.Source.RawAction.material,currentCp] using ih

theorem advance_cp_count (frame : CPS1Recycling.Frame) (cursor : CPS1AtomicDynamics.Source.Cursor frame)
    (actions : List CPS1AtomicDynamics.Source.RawAction) :
    (CPS1AtomicDynamics.Source.advance frame cursor actions).stock.count (currentCp frame) =
      cursor.stock.count (currentCp frame) := by
  let available := cursor.stock ++ actions.flatMap (CPS1AtomicDynamics.Source.RawAction.material frame)
  let localProgram := match CPS1AtomicDynamics.Source.heldBody frame available with
    | some state => CPS1AtomicDynamics.Source.program frame state (actions ++ cursor.pending) | none => []
  have preserved := execute_retained_count frame (atomicCp frame) (fun _ same => by cases same)
    (cursor.captureRemaining ++ localProgram) available
  change (CPS1AtomicDynamics.Source.advance frame cursor actions).stock.count (currentCp frame) = _ at preserved
  change (CPS1AtomicDynamics.Source.advance frame cursor actions).stock.count (currentCp frame) =
    available.count (currentCp frame) at preserved
  rw [preserved,List.count_append,raw_no_cp,Nat.add_zero]

theorem actual_current_CP_present
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm
      (CPS1Reinitiation.Handover.rawFuel CPS1ResourceExecution.Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) (generated : 0 < CPS1EditingChemicalJoin.EditingStock.paid edits water additional)
    (actions : List CPS1AtomicDynamics.Source.RawAction) :
    ∃ (frame : CPS1Recycling.Frame) (current : CPS1AtomicDynamics.Source.Occurrence frame),
      CPS1AtomicDynamics.Source.execution edits water additional path
        recycleFeed scanFeed bodyFeed depth actions = some ⟨frame,current⟩ ∧
      currentCp frame ∈ current.current.stock ∧
      0 < current.current.stock.count (currentCp frame) ∧
      current.current.stock.count (currentCp frame) =
        current.previous.previous.current.stock.count (sourceCp frame) := by
  rcases CPS1EditingChemicalJoin.Source.actual_chemical_complete edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw
    bodyFeed bodyExtra bodyRaw depth generated with
    ⟨frame,chemical,chemicalActual,inventory,_⟩
  have productCount : (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count (sourceCp frame) = 1 := rfl
  have positive : 0 < chemical.current.stock.count (sourceCp frame) := by
    have counted := inventory.count_eq (sourceCp frame)
    rw [List.count_append,productCount] at counted
    omega
  let atomic := CPS1AtomicSource.Current.fromActual frame chemical
  have atomicActual : CPS1AtomicSource.Current.execution edits water additional path
      recycleFeed scanFeed bodyFeed depth = some ⟨frame,atomic⟩ := by
    simp only [CPS1AtomicSource.Current.execution,CPS1AtomicSource.Current.sourceExecution,chemicalActual]
    rfl
  let current : CPS1AtomicDynamics.Source.Occurrence frame :=
    ⟨atomic,CPS1AtomicDynamics.Source.advance frame (CPS1AtomicDynamics.Source.start frame atomic) actions⟩
  have actual : CPS1AtomicDynamics.Source.execution edits water additional path
      recycleFeed scanFeed bodyFeed depth actions = some ⟨frame,current⟩ := by
    simp only [CPS1AtomicDynamics.Source.execution,atomicActual]
    rfl
  have kept : current.current.stock.count (currentCp frame) = chemical.current.stock.count (sourceCp frame) :=
    (advance_cp_count frame (CPS1AtomicDynamics.Source.start frame atomic) actions).trans
      ((start_cp_count frame atomic).trans (atomic_cp_count frame chemical))
  have surviving : 0 < current.current.stock.count (currentCp frame) := by
    rw [kept]
    exact positive
  exact ⟨frame,current,actual,List.count_pos_iff.mp surviving,surviving,kept⟩

end
end CPS1EnzymeBath.BathAccounting
