import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Admission
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Renewal
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Source

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

namespace CPS1ReactiveSourceEntry
noncomputable section
open CPS1ElectronicSource CPS1ReactiveNuclear CPS1ReactiveJointNuclear
open CPS1ReactiveField CPS1ReactiveField.Carried
variable {frame : CPS1Recycling.Frame}

def RowsAt (current : SourceCursor frame) : Prop :=
  ∀ active : Active frame, ∀ held : current.native.active = some active,
    ∀ germ : Germ active.source.old active.fields,
      boundGerm current active held = .ok germ →
        BirthRows germ current.native.current.ingress.measurements.rows

theorem entered_rows_at (entry : Entered frame) : RowsAt entry.cursor := by
  intro active held germ binding
  have same : active = entry.active := Option.some.inj (held.symm.trans entry.held)
  subst active
  have germSame : germ = entry.germ := Except.ok.inj (binding.symm.trans entry.binding)
  subst germ
  have bodyRows := (CPS1AddressedReactiveJoint.admitted_body _ _ _ entry.active.actual).2.2.1
  rw [← entry.current,← bodyRows]
  exact entry.rows

theorem step_rows_at (current next : SourceCursor frame) (pulse : Pulse frame)
    (actual : CPS1ReactiveJointNuclear.step current = .ok (next,pulse))
    (sourceRows : RowsAt current) : RowsAt next := by
  classical
  unfold CPS1ReactiveJointNuclear.step at actual
  split at actual
  · cases actual
  · rename_i active held
    split at actual
    · cases actual
    · rename_i sourceTag
      split at actual
      · cases actual
      · split at actual
        · cases actual
        · rename_i germ binding
          split at actual
          · cases actual
          · split at actual
            · cases actual
            · rename_i index selected
              dsimp only at actual
              split at actual
              · cases actual
              · rename_i body bodyActual
                split at actual
                · cases actual
                · rename_i afterGerm germActual
                  cases Except.ok.inj actual
                  intro afterActive afterHeld readGerm readBinding
                  have activeSame := Option.some.inj afterHeld
                  subst afterActive
                  have germSame := Except.ok.inj readBinding
                  subst readGerm
                  change BirthRows afterGerm
                    (originRows germ (CPS1ReactiveFieldDynamics.dyadicTime index)
                      active.source.ingress.measurements.rows)
                  apply motion_birth_rows germ _ _ _ afterGerm germActual
                  have same : active.source = current.native.current := not_ne_iff.mp sourceTag
                  have sameRows := congrArg (fun source : Occurrence frame => source.ingress.measurements.rows) same
                  exact sameRows.symm ▸ sourceRows active held germ binding

private structure LiveFields (current : SourceCursor frame) where
  active : Active frame
  held : current.native.active = some active
  source : active.source = current.native.current
  germ : Germ active.source.old active.fields
  binding : boundGerm current active held = .ok germ
  budget : 0 < active.fields.reserve
  aligned : OriginAligned active germ

private def readLiveFields (current : SourceCursor frame) (ready : Ready current) : LiveFields current := by
  classical
  cases held : current.native.active with
  | none =>
    exact False.elim (by
      rcases ready with ⟨active,present,_⟩
      rw [held] at present
      cases present)
  | some active =>
    cases actual : boundGerm current active held with
    | error failure =>
      exact False.elim (by
        rcases ready with ⟨selected,present,_,_,germ,binding,_⟩
        have same : selected = active := Option.some.inj (present.symm.trans held)
        subst selected
        have impossible := actual.symm.trans binding
        cases impossible)
    | ok germ =>
      have laws : active.source = current.native.current ∧ 0 < active.fields.reserve ∧ OriginAligned active germ := by
        rcases ready with ⟨selected,present,source,budget,generated,binding,aligned⟩
        have same : selected = active := Option.some.inj (present.symm.trans held)
        subst selected
        have germSame : generated = germ := Except.ok.inj (binding.symm.trans actual)
        subst generated
        exact ⟨source,budget,aligned⟩
      exact ⟨active,held,laws.1,germ,actual,laws.2.1,laws.2.2⟩

private def packEntered (current : SourceCursor frame) (ready : Ready current)
    (sourceRows : RowsAt current) : Entered frame :=
  let data := readLiveFields current ready
  ⟨current,data.active,data.held,data.source,data.germ,data.binding,data.budget,by
    have bodyRows := (CPS1AddressedReactiveJoint.admitted_body _ _ _ data.active.actual).2.2.1
    have sameRows := congrArg (fun source : Occurrence frame => source.ingress.measurements.rows) data.source
    rw [bodyRows,sameRows]
    exact sourceRows data.active data.held data.germ data.binding,data.aligned⟩

structure EnteredPulse (entry : Entered frame) where
  after : Entered frame
  pulse : Pulse frame
  actual : CPS1ReactiveJointNuclear.step entry.cursor = .ok (after.cursor,pulse)

/-- Reads the actual successful joint write; its full source rows are regenerated by that write. -/
def nextEntered (entry : Entered frame) : EnteredPulse entry := by
  classical
  cases actual : CPS1ReactiveJointNuclear.step entry.cursor with
  | error failure =>
    exact False.elim (by
      obtain ⟨next,pulse,generated,_⟩ := step_ready entry.cursor entry.ready
      have impossible := actual.symm.trans generated
      cases impossible)
  | ok generated =>
    let after := packEntered generated.1 (step_generated _ _ _ actual).2.1
      (step_rows_at _ _ _ actual (entered_rows_at entry))
    exact ⟨after,generated.2,actual⟩

structure EnteredRun (entry : Entered frame) (depth : Nat) where
  after : Entered frame
  pulses : List (Pulse frame)
  actual : CPS1ReactiveJointNuclear.renew entry.cursor depth = ⟨after.cursor,pulses,0,none⟩

def renewEntered (entry : Entered frame) (depth : Nat) : EnteredRun entry depth :=
  Nat.rec (motive := fun depth => ∀ entry : Entered frame, EnteredRun entry depth)
    (fun entry => ⟨entry,[],rfl⟩)
    (fun depth recur entry =>
      let first := nextEntered entry
      let tail := recur first.after
      ⟨tail.after,first.pulse :: tail.pulses,by
        rw [renew_succ,first.actual]
        dsimp only
        rw [tail.actual]
        ⟩) depth entry

end
end CPS1ReactiveSourceEntry
