import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Admission
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Renewal

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

namespace CPS1ReactiveSourceEntry
noncomputable section
open CPS1ElectronicSource CPS1ReactiveNuclear CPS1ReactiveJointNuclear
open CPS1ReactiveField CPS1ReactiveField.Carried
variable {frame : CPS1Recycling.Frame}

private theorem rows_transport {root root' : CPS1Deformation.Source.Occurrence frame}
    {state state' : Snapshot} (rootSame : root = root') (stateSame : state = state')
    (germ : Germ root state) (rows : CPS1AddressedReactiveJoint.Rows.Stock)
    (generated : BirthRows germ rows) : BirthRows (germ.transport rootSame stateSame) rows := by
  cases rootSame
  cases stateSame
  exact generated

private theorem aligned_transport {root root' : CPS1Deformation.Source.Occurrence frame}
    {state state' : Snapshot} (rootSame : root = root') (stateSame : state = state')
    (germ : Germ root state) (body : CPS1AddressedReactiveJoint.Body frame)
    (generated : BodyOriginAligned body germ) :
    BodyOriginAligned body (germ.transport rootSame stateSame) := by
  cases rootSame
  cases stateSame
  exact generated

private theorem aligned_reprice {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (germ : Germ root state) (body : CPS1AddressedReactiveJoint.Body frame) (reserve : ℝ)
    (generated : BodyOriginAligned body germ) : BodyOriginAligned body (germ.reprice reserve) := generated

@[reducible] def chemicalCurrent (before : Entered frame) (input : Input) : Occurrence frame :=
  CPS1ReactiveField.next before.active.source input.1.1 input.1.2 input.2

private def chemicalNative (before : Entered frame) (input : Input) : Cursor frame :=
  nextCursor before.cursor.native input.1.1 input.1.2 input.2

private theorem chemical_current (before : Entered frame) (input : Input) :
    (chemicalNative before input).current = chemicalCurrent before input := by
  simp only [chemicalNative,nextCursor,chemicalCurrent,← before.current]

private theorem chemical_active (before : Entered frame) (input : Input) (after : Active frame)
    (actual : advance before.active (chemicalCurrent before input) = .ok after) :
    (chemicalNative before input).active = some after := by
  unfold chemicalCurrent at actual
  simp only [chemicalNative,nextCursor,before.held,← before.current,actual,Except.toOption,Option.or]

private def chemicalCursor (before : Entered frame) (input : Input) (after : Active frame)
    (held : (chemicalNative before input).active = some after)
    (germ : Germ after.source.old after.fields) : SourceCursor frame :=
  ⟨chemicalNative before input,by
    simpa only [GermAt,held] using (.ok germ : Except GermFailure (Germ after.source.old after.fields))⟩

private theorem chemical_binding (before : Entered frame) (input : Input) (after : Active frame)
    (held : (chemicalNative before input).active = some after)
    (germ : Germ after.source.old after.fields) :
    boundGerm (chemicalCursor before input after held germ) after held = .ok germ := by
  simp [boundGerm,chemicalCursor,GermAt]

private theorem advance_body {current : Occurrence frame} (before after : Active frame)
    (source : Inlet current) (selected : inlet current = .ok source)
    (actual : advance before current = .ok after) : after.body = source.body := by
  unfold advance at actual
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
          · split at actual
            · cases actual
            · split at actual
              · cases actual
              · cases Except.ok.inj actual
                rfl

/-- The exact chemical next generates the retained/fresh germ and pays a fresh physical entrance. -/
def reenter (before : Entered frame) (input : Input) : Entry frame := by
  classical
  let current := chemicalCurrent before input
  let retained := SourceCursor.next before.cursor input.1.1 input.1.2 input.2
  exact match actual : advance before.active current with
  | .error failure => .residual retained (.native failure)
  | .ok after =>
    let generated := advance_generated before.active current after actual
    let source := generated.choose
    let law := generated.choose_spec
    match born : renewedGerm (current := current) before.germ before.active.good source with
    | .error failure => .residual retained (.germ failure)
    | .ok germ =>
      if budget : 0 < after.fields.reserve then
        let reserve := before.active.fields.reserve+deltaReserve before.active current-renewalPrice before.active source
        let priced := germ.reprice reserve
        let live := priced.transport (congrArg Occurrence.old law.2.1.symm) law.2.2.1.symm
        let held := chemical_active before input after actual
        let cursor := chemicalCursor before input after held live
        have beforeRows : BirthRows before.germ before.active.source.ingress.measurements.rows := by
          have rows := (CPS1AddressedReactiveJoint.admitted_body _ _ _ before.active.actual).2.2.1
          rw [← rows]
          exact before.rows
        have rawRows := renewed_birth_rows before.active.source before.germ before.active.good
          input.1.1 input.1.2 input.2 source germ born beforeRows
        have rawAligned := renewed_body_origin_aligned (current := current) before.germ before.active.good source germ born rawRows
        have liveRows := rows_transport (congrArg Occurrence.old law.2.1.symm) law.2.2.1.symm priced source.body.sourceRows
          (birth_rows_reprice germ _ reserve rawRows)
        have liveAligned := aligned_transport (congrArg Occurrence.old law.2.1.symm) law.2.2.1.symm priced source.body
          (aligned_reprice germ _ reserve rawAligned)
        have bodySame := advance_body before.active after source law.1 actual
        .admitted ⟨cursor,after,held,law.2.1.trans (chemical_current before input).symm,
          live,chemical_binding before input after held live,budget,
          by rw [bodySame]; exact liveRows,by rw [OriginAligned,bodySame]; exact liveAligned⟩
      else .residual retained .exhaustedReserve

theorem reentry_actual_step (before : Entered frame) (input : Input) :
    match reenter before input with
    | .residual _ _ => True
    | .admitted after => ∃ next pulse, CPS1ReactiveJointNuclear.step after.cursor = .ok (next,pulse) ∧
        pulse.Valid ∧ Ready next := by
  cases reenter before input with
  | residual cursor failure => exact True.intro
  | admitted after => exact step_ready after.cursor after.ready

private theorem entered_cursor_normal_form (before : Entered frame) :
    before.cursor =
      (⟨⟨before.active.source, some before.active, before.cursor.native.stages⟩,
        .ok before.germ⟩ : SourceCursor frame) := by
  rcases before with
    ⟨⟨⟨nativeSource,nativeActive,stages⟩,stored⟩,
      active,held,current,germ,binding,budget,rows,aligned⟩
  cases nativeActive with
  | none => cases held
  | some selected =>
    cases Option.some.inj held
    cases current
    change stored = .ok germ at binding
    cases binding
    rfl

private def entryCursor : Entry frame → SourceCursor frame
  | .residual current _ => current
  | .admitted after => after.cursor

private theorem except_rec_ok {errorType valueType resultType : Type*}
    (result : Except errorType valueType) (value : valueType) (actual : result = .ok value)
    (onError : ∀ failure, result = .error failure → resultType)
    (onOk : ∀ value, result = .ok value → resultType) :
    (Except.rec (motive := fun selected => result = selected → resultType)
      onError onOk result rfl) = onOk value actual := by
  cases actual
  rfl

private theorem eq_rec_arrow {valueType resultType : Type*} {left right : valueType}
    (same : left = right) (value : right = left → resultType) :
    (Eq.rec (motive := fun selected _ => right = selected → resultType) value same) rfl =
      value same.symm := by
  cases same
  rfl

private theorem reentry_cursor_value (before : Entered frame) (input : Input) :
    entryCursor (reenter before input) = SourceCursor.next before.cursor input.1.1 input.1.2 input.2 := by
  classical
  rcases before with
    ⟨⟨⟨nativeSource,nativeActive,stages⟩,stored⟩,
      active,held,current,oldGerm,binding,budget,rows,aligned⟩
  cases nativeActive with
  | none => cases held
  | some selected =>
    cases Option.some.inj held
    cases current
    change stored = .ok oldGerm at binding
    cases binding
    unfold reenter
    dsimp only
    split
    · rfl
    · rename_i after actual
      dsimp only [chemicalCurrent,CPS1ReactiveField.next]
      split
      · rfl
      · rename_i germ born
        split
        · dsimp only [entryCursor]
          change advance active
            (CPS1ReactiveField.next active.source input.1.1 input.1.2 input.2) = .ok after at actual
          simp [SourceCursor.next,chemicalCursor,chemicalNative,nextCursor,actual]
          rw [except_rec_ok _ _ actual]
          rw [eq_rec_arrow]
          dsimp only [Except.bind]
          congr 1
          let current := CPS1ReactiveField.next active.source input.1.1 input.1.2 input.2
          let generated := advance_generated active current after actual
          let source := generated.choose
          let law := generated.choose_spec
          let reserve := active.fields.reserve+deltaReserve active current-renewalPrice active source
          have readback := congrArg
            (fun output : Except GermFailure (Germ current.old (renewed active.fields active.good source)) =>
              output.bind (fun newGerm => .ok ((newGerm.reprice reserve).transport
                (congrArg Occurrence.old law.2.1.symm) law.2.2.1.symm))) born
          exact readback.symm
        · rfl

theorem reentry_same_value (before : Entered frame) (input : Input) :
    match reenter before input with
    | .residual current _ => current = SourceCursor.next before.cursor input.1.1 input.1.2 input.2
    | .admitted after => after.cursor = SourceCursor.next before.cursor input.1.1 input.1.2 input.2 := by
  have generated := reentry_cursor_value before input
  cases selected : reenter before input <;> simpa only [selected,entryCursor] using generated

end
end CPS1ReactiveSourceEntry
