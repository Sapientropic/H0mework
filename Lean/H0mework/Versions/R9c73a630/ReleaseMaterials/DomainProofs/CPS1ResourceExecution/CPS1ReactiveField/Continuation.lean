import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Renewal

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveField.Carried
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators
variable {frame : CPS1Recycling.Frame} {current : Occurrence frame}

structure Active (frame : CPS1Recycling.Frame) where
  source : Occurrence frame
  fields : Snapshot
  good : fields.Good
  body : CPS1AddressedReactiveJoint.Body frame
  actual : CPS1AddressedReactiveJoint.admission source.ingress = .ok body
  paidRawReserve : ℝ

inductive Failure (frame : CPS1Recycling.Frame)
  | inlet (failure : InletFailure)
  | differentSource
  | lostOrigins (before after : List CPS1AddressedHydrolysis.Origin)
  | incompatibleElectronInertia
  | collision
  | negativeReserve
  | energyShortage

def activate (current : Occurrence frame) : Except (Failure frame) (Active frame) := by
  classical
  exact match inlet current with
    | .error failure => .error (.inlet failure)
    | .ok source =>
      if ¬ (∀ node ∈ waterNodes source, isElectron node = true →
          node.row.inertia = source.old.reference.geometry.electronInertia) then .error .incompatibleElectronInertia
      else if ¬ CPS1AtomicDynamics.Body.ready (commonNuclei source) then .error .collision
      else if incomingReserve source < 0 then .error .negativeReserve
      else if incomingReserve source < price source then .error .energyShortage
      else
        let material : Material current := ⟨source,incomingReserve source-price source⟩
        .ok ⟨current,initial material,initial_good material,source.body,source.actual,current.ingress.measurements.reserve⟩

theorem activate_generated (current : Occurrence frame) (next : Active frame)
    (actual : activate current = .ok next) :
    ∃ source : Inlet current, inlet current = .ok source ∧ next.source = current ∧
      next.fields = initial (⟨source,incomingReserve source-price source⟩ : Material current) ∧
      next.fields.reserve ≥ 0 ∧ next.fields.account = incomingEnergy source+incomingReserve source := by
  unfold activate at actual
  cases selected : inlet current with
  | error => simp only [selected] at actual; cases actual
  | ok source =>
    simp only [selected] at actual
    split at actual
    · cases actual
    · split at actual
      · cases actual
      · split at actual
        · cases actual
        · split at actual
          · cases actual
          · rename_i paid
            cases Except.ok.inj actual
            refine ⟨source,rfl,rfl,rfl,sub_nonneg.mpr (le_of_not_gt paid),?_⟩
            rw [Snapshot.account,initial_energy]
            change energy source+(incomingReserve source-price source) = _
            unfold price
            ring

def retainedOrigins (old : Active frame) (source : Inlet current) : Prop :=
  ∀ origin ∈ old.body.atoms.map CPS1AddressedHydrolysis.Atom.origin,
    origin ∈ source.body.atoms.map CPS1AddressedHydrolysis.Atom.origin

def deltaReserve (old : Active frame) (current : Occurrence frame) : ℝ :=
  current.ingress.measurements.reserve-old.paidRawReserve

def renewalPrice (old : Active frame) (source : Inlet current) : ℝ :=
  (renewed old.fields old.good source).energy-old.fields.energy-
    CPS1AtomicDynamics.Body.energy (freshNodes old.fields source)

def advance (old : Active frame) (current : Occurrence frame) : Except (Failure frame) (Active frame) := by
  classical
  exact match inlet current with
    | .error failure => .error (.inlet failure)
    | .ok source =>
      if current.old ≠ old.source.old ∨
          current.ingress.atomic.source.prior ≠ old.source.ingress.atomic.source.prior then .error .differentSource
      else if ¬ retainedOrigins old source then .error (.lostOrigins
        (old.body.atoms.map CPS1AddressedHydrolysis.Atom.origin)
        (source.body.atoms.map CPS1AddressedHydrolysis.Atom.origin))
      else if ¬ (∀ node ∈ freshNodes old.fields source, isElectron node = true →
          node.row.inertia = old.fields.electronInertia) then .error .incompatibleElectronInertia
      else if ¬ CPS1AtomicDynamics.Body.ready (renewed old.fields old.good source).nuclei then .error .collision
      else if old.fields.reserve+deltaReserve old current < 0 then .error .negativeReserve
      else if old.fields.reserve+deltaReserve old current < renewalPrice old source then .error .energyShortage
      else
        let generated := (renewed old.fields old.good source).reprice
          (old.fields.reserve+deltaReserve old current-renewalPrice old source)
        .ok ⟨current,generated,renewed_good old.fields old.good source,source.body,source.actual,
          current.ingress.measurements.reserve⟩

theorem advance_generated (old : Active frame) (current : Occurrence frame) (next : Active frame)
    (actual : advance old current = .ok next) :
    ∃ source : Inlet current, inlet current = .ok source ∧ next.source = current ∧
      next.fields = (renewed old.fields old.good source).reprice
        (old.fields.reserve+deltaReserve old current-renewalPrice old source) ∧
      next.fields.reserve ≥ 0 ∧
      next.fields.account = old.fields.account+deltaReserve old current+
        CPS1AtomicDynamics.Body.energy (freshNodes old.fields source) ∧ retainedOrigins old source ∧
      current.old = old.source.old ∧ current.ingress.atomic.source.prior = old.source.ingress.atomic.source.prior := by
  unfold advance at actual
  cases selected : inlet current with
  | error => simp only [selected] at actual; cases actual
  | ok source =>
    simp only [selected] at actual
    split at actual
    · cases actual
    · rename_i sameSource
      split at actual
      · cases actual
      · rename_i retained
        split at actual
        · cases actual
        · split at actual
          · cases actual
          · split at actual
            · cases actual
            · split at actual
              · cases actual
              · rename_i paid
                cases Except.ok.inj actual
                have same := not_or.mp sameSource
                refine ⟨source,rfl,rfl,rfl,sub_nonneg.mpr (le_of_not_gt paid),?_,not_not.mp retained,
                  not_not.mp same.1,not_not.mp same.2⟩
                change ((renewed old.fields old.good source).reprice
                  (old.fields.reserve+deltaReserve old current-renewalPrice old source)).account = _
                rw [Snapshot.account,reprice_energy]
                change (renewed old.fields old.good source).energy+
                  (old.fields.reserve+deltaReserve old current-renewalPrice old source) = _
                unfold Snapshot.account renewalPrice
                ring

structure Stage (frame : CPS1Recycling.Frame) where
  source : Occurrence frame
  before : Option (Active frame)
  result : Except (Failure frame) (Active frame)

def Stage.Valid (stage : Stage frame) : Prop :=
  stage.result = match stage.before with
    | none => activate stage.source
    | some old => advance old stage.source

structure Cursor (frame : CPS1Recycling.Frame) where
  current : Occurrence frame
  active : Option (Active frame)
  stages : List (Stage frame)

def startCursor (current : Occurrence frame) : Cursor frame :=
  let result := activate current
  ⟨current,result.toOption,[⟨current,none,result⟩]⟩

def nextCursor (current : Cursor frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) : Cursor frame :=
  let source := CPS1ReactiveField.next current.current actions feed raw
  let result := match current.active with
    | none => activate source
    | some old => advance old source
  ⟨source,result.toOption.or current.active,current.stages ++ [⟨source,current.active,result⟩]⟩

abbrev Input := CPS1AddressedChemicalReaction.Source.Input × List CPS1AddressedReactiveJoint.Rows.RawAction
def advanceAll (current : Cursor frame) (inputs : List Input) : Cursor frame :=
  List.rec (motive := fun _ => Cursor frame → Cursor frame) (fun current => current)
    (fun input _ recur current => recur (nextCursor current input.1.1 input.1.2 input.2)) inputs current

theorem advance_all_cons (current : Cursor frame) (input : Input) (rest : List Input) :
    advanceAll current (input :: rest) = advanceAll (nextCursor current input.1.1 input.1.2 input.2) rest := rfl

theorem next_cursor_source (current : Cursor frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    (nextCursor current actions feed raw).current = CPS1ReactiveField.next current.current actions feed raw ∧
    type_of% (source_whole current.current actions feed raw) ∧
    current.stages.Sublist (nextCursor current actions feed raw).stages :=
  ⟨rfl,source_whole current.current actions feed raw,List.sublist_append_left _ _⟩

theorem advance_all_source (current : Cursor frame) (inputs : List Input) :
    (advanceAll current inputs).current.ingress.atomic = CPS1AddressedHydrolysis.Atomic.advanceAll
      current.current.ingress.atomic (inputs.map Prod.fst) := by
  induction inputs generalizing current with
  | nil => rfl
  | cons input rest ih =>
    simpa only [advance_all_cons,List.map_cons,CPS1AddressedHydrolysis.Atomic.advance_all_cons,
      nextCursor,CPS1ReactiveField.next,CPS1AddressedReactiveJoint.next] using
      ih (nextCursor current input.1.1 input.1.2 input.2)

theorem advance_all_generated_stages (current : Cursor frame) (inputs : List Input) :
    ∃ generated : List (Stage frame), (advanceAll current inputs).stages = current.stages ++ generated ∧
      ∀ stage ∈ generated, stage.Valid := by
  induction inputs generalizing current with
  | nil => exact ⟨[],by simp only [show advanceAll current [] = current from rfl,List.append_nil],by simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]⟩
  | cons input rest ih =>
    obtain ⟨generated,whole,valid⟩ := ih (nextCursor current input.1.1 input.1.2 input.2)
    let source := CPS1ReactiveField.next current.current input.1.1 input.1.2 input.2
    let stage : Stage frame := ⟨source,current.active,match current.active with
      | none => activate source | some old => advance old source⟩
    refine ⟨stage :: generated,?_,?_⟩
    · rw [advance_all_cons,whole]
      simp only [nextCursor,List.append_assoc,List.singleton_append]
      rfl
    · intro entry member
      rcases List.mem_cons.mp member with first | later
      · subst entry
        rfl
      · exact valid entry later

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def fromSource (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
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
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    Option (Σ frame : CPS1Recycling.Frame, Cursor frame) :=
  match CPS1ReactiveField.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed actions feed raw with
  | none => none
  | some source => some ⟨source.1,startCursor source.2⟩

inductive PhysicalLive (frame : CPS1Recycling.Frame)
  | residual (species : CPS1Deformation.Species frame)
  | common (state : Active frame)

def physicalStock (state : Active frame) : List (PhysicalLive frame) :=
  match heldDeformed state.source.old.current.stock with
  | none => .common state :: state.source.old.current.stock.map PhysicalLive.residual
  | some old => .common state :: (state.source.old.current.stock.erase (.deformed old)).map PhysicalLive.residual

theorem active_whole (state : Active frame) :
    state.fields.Good ∧
    state.body.atomic = state.source.ingress.atomic ∧
    state.body.missing = CPS1AddressedReactiveJoint.residuals state.source.ingress.atomic.history
      state.source.ingress.atomic.source.stock ∧
    (CPS1AddressedReactiveJoint.blocks state.source.ingress.atomic.history state.source.ingress.atomic.source.stock).map
      CPS1AddressedReactiveJoint.Block.material = state.source.ingress.atomic.source.stock := by
  have paid := CPS1AddressedReactiveJoint.admitted_body state.source.ingress.atomic state.source.ingress.measurements
    state.body state.actual
  exact ⟨state.good,paid.1,paid.2.2.2.2.2.1,CPS1AddressedReactiveJoint.blocks_whole _ _⟩

theorem physical_live_once (state : Active frame) (old : CPS1Deformation.Material frame)
    (selected : heldDeformed state.source.old.current.stock = some old) :
    state.source.old.current.stock.Perm (.deformed old :: state.source.old.current.stock.erase (.deformed old)) ∧
    physicalStock state = .common state :: (state.source.old.current.stock.erase (.deformed old)).map PhysicalLive.residual ∧
    old.currentJoint.components = old.reference.geometry.originJoint.components ∧
    old.currentJoint.originBody = old.reference.geometry.originJoint.originBody := by
  exact ⟨List.perm_cons_erase (held_deformed_member _ _ selected),by simp only [physicalStock,selected],rfl,rfl⟩

end
end CPS1ReactiveField.Carried
