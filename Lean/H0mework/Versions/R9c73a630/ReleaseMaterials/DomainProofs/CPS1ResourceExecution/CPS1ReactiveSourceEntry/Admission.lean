import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Entry

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

namespace CPS1ReactiveSourceEntry
noncomputable section
open CPS1ElectronicSource CPS1ReactiveNuclear CPS1ReactiveJointNuclear
open CPS1ReactiveField CPS1ReactiveField.Carried
variable {frame : CPS1Recycling.Frame}

private def initialActive {current : Occurrence frame} (material : Material current) : Active frame :=
  ⟨current,initial material,initial_good material,material.source.body,material.source.actual,
    current.ingress.measurements.reserve⟩

private def initialCursor {current : Occurrence frame} (material : Material current)
    (germ : Germ current.old (initial material)) : SourceCursor frame :=
  ⟨⟨current,some (initialActive material),[⟨current,none,activate current⟩]⟩,.ok germ⟩

private theorem inlet_selected {current : Occurrence frame} (source : Inlet current)
    (actual : inlet current = .ok source) :
    heldDeformed current.old.current.stock = some source.old := by
  unfold inlet at actual
  split at actual
  · cases actual
  · rename_i old selected
    split at actual
    · split at actual
      · cases actual
      · rename_i body admitted
        cases Except.ok.inj actual
        exact selected
    · cases actual

private theorem activate_from_inlet {current : Occurrence frame} (source : Inlet current)
    (selected : inlet current = .ok source) (active : Active frame)
    (actual : activate current = .ok active) :
    active = initialActive (⟨source,incomingReserve source-price source⟩ : Material current) := by
  unfold activate at actual
  cases inletResult : inlet current with
  | error failure => simp only [inletResult] at actual; cases actual
  | ok found =>
    have same : found = source := Except.ok.inj (inletResult.symm.trans selected)
    subst found
    simp only [inletResult] at actual
    split at actual
    · cases actual
    · split at actual
      · cases actual
      · split at actual
        · cases actual
        · split at actual
          · cases actual
          · exact (Except.ok.inj actual).symm

private theorem initial_cursor_native {current : Occurrence frame} (source : Inlet current)
    (selected : inlet current = .ok source) (active : Active frame)
    (actual : activate current = .ok active)
    (germ : Germ current.old (initial (⟨source,incomingReserve source-price source⟩ : Material current))) :
    (initialCursor (⟨source,incomingReserve source-price source⟩ : Material current) germ).native = startCursor current := by
  rw [initialCursor,startCursor,actual,Except.toOption,activate_from_inlet source selected active actual]

structure Entered (frame : CPS1Recycling.Frame) where
  cursor : SourceCursor frame
  active : Active frame
  held : cursor.native.active = some active
  current : active.source = cursor.native.current
  germ : Germ active.source.old active.fields
  binding : boundGerm cursor active held = .ok germ
  budget : 0 < active.fields.reserve
  rows : BirthRows germ active.body.sourceRows
  aligned : OriginAligned active germ

theorem Entered.ready (entry : Entered frame) : Ready entry.cursor :=
  ⟨entry.active,entry.held,entry.current,entry.budget,entry.germ,entry.binding,entry.aligned⟩

inductive EntryFailure (frame : CPS1Recycling.Frame)
  | native (failure : CPS1ReactiveField.Carried.Failure frame)
  | germ (failure : GermFailure)
  | originalRows
  | exhaustedReserve

inductive Entry (frame : CPS1Recycling.Frame)
  | admitted (entry : Entered frame)
  | residual (cursor : SourceCursor frame) (failure : EntryFailure frame)

/-- Source admission generates its full germ and row law before requesting the first physical write. -/
def enterFromOld (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) : Entry frame := by
  classical
  let current := CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw
  let retained := SourceCursor.start current
  exact match selected : inlet current with
  | .error _ => match actual : activate current with
    | .error failure => .residual retained (.native failure)
    | .ok _ => .residual retained .originalRows
  | .ok source => match actual : activate current with
    | .error failure => .residual retained (.native failure)
    | .ok _ =>
      let material : Material current := ⟨source,incomingReserve source-price source⟩
      match born : initialGerm material with
      | .error failure => .residual retained (.germ failure)
      | .ok germ =>
        if original : OriginalRows material then
          if budget : 0 < material.reserve then
            let cursor := initialCursor material germ
            let aligned := initial_source_origin_aligned old actions feed raw material
              (inlet_selected source selected) germ born original
            let rows := initial_birth_rows old actions feed raw material
              (inlet_selected source selected) germ born original
            .admitted ⟨cursor,initialActive material,rfl,rfl,germ,rfl,budget,rows,aligned⟩
          else .residual retained .exhaustedReserve
        else .residual retained .originalRows

structure InitialRun (frame : CPS1Recycling.Frame) where
  admission : Entry frame
  requestedDepth : Nat
  physical : Option (CPS1ReactiveJointNuclear.Run frame)

def fromOld (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (depth : Nat) : InitialRun frame :=
  let admission := enterFromOld old actions feed raw
  ⟨admission,depth,match admission with
    | .admitted entry => some (CPS1ReactiveJointNuclear.renew entry.cursor depth)
    | .residual _ _ => none⟩

private theorem admitted_actual_step (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (entry : Entered frame)
    (_actual : enterFromOld old actions feed raw = .admitted entry) :
    ∃ next pulse, CPS1ReactiveJointNuclear.step entry.cursor = .ok (next,pulse) ∧
      pulse.Valid ∧ Ready next := step_ready entry.cursor entry.ready

private theorem admitted_actual_finite (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (entry : Entered frame) (depth : Nat)
    (actual : enterFromOld old actions feed raw = .admitted entry) :
    (fromOld old actions feed raw depth).physical = some (CPS1ReactiveJointNuclear.renew entry.cursor depth) ∧
    (CPS1ReactiveJointNuclear.renew entry.cursor depth).remaining = 0 ∧
    (CPS1ReactiveJointNuclear.renew entry.cursor depth).failure = none ∧
    (CPS1ReactiveJointNuclear.renew entry.cursor depth).pulses.length = depth ∧
    Ready (CPS1ReactiveJointNuclear.renew entry.cursor depth).cursor := by
  have generated := renew_ready entry.cursor depth entry.ready
  exact ⟨by simp only [fromOld,actual],generated⟩

/-- The public consumer reads only the disposition generated from this source and raw input. -/
theorem source_initial_actual_step (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    match enterFromOld old actions feed raw with
    | .residual _ _ => True
    | .admitted entry => ∃ next pulse, CPS1ReactiveJointNuclear.step entry.cursor = .ok (next,pulse) ∧
        pulse.Valid ∧ Ready next := by
  cases actual : enterFromOld old actions feed raw with
  | residual cursor failure => exact True.intro
  | admitted entry => exact admitted_actual_step old actions feed raw entry actual

theorem source_initial_actual_finite (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (depth : Nat) :
    match (fromOld old actions feed raw depth).admission with
    | .residual _ _ => (fromOld old actions feed raw depth).physical = none
    | .admitted entry =>
      (fromOld old actions feed raw depth).physical = some (CPS1ReactiveJointNuclear.renew entry.cursor depth) ∧
      (CPS1ReactiveJointNuclear.renew entry.cursor depth).remaining = 0 ∧
      (CPS1ReactiveJointNuclear.renew entry.cursor depth).failure = none ∧
      (CPS1ReactiveJointNuclear.renew entry.cursor depth).pulses.length = depth ∧
      Ready (CPS1ReactiveJointNuclear.renew entry.cursor depth).cursor := by
  change match enterFromOld old actions feed raw with
    | .residual _ _ => _
    | .admitted _ => _
  cases actual : enterFromOld old actions feed raw with
  | residual cursor failure => simp only [fromOld,actual]
  | admitted entry => exact admitted_actual_finite old actions feed raw entry depth actual

end
end CPS1ReactiveSourceEntry
