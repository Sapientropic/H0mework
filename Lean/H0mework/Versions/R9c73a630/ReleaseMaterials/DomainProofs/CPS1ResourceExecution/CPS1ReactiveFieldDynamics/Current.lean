import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Budget

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveFieldDynamics
noncomputable section
variable {frame : CPS1Recycling.Frame}
abbrev NativeCursor := CPS1ReactiveField.Carried.Cursor
abbrev NativeActive := CPS1ReactiveField.Carried.Active

inductive Failure
  | missingActive
  | staleActive
  | exhausted (reserve : ℝ)

structure Pulse (frame : CPS1Recycling.Frame) where
  before : NativeActive frame
  index : Nat
  after : NativeActive frame

def Pulse.time (pulse : Pulse frame) : ℝ := dyadicTime pulse.index
def Pulse.Valid (pulse : Pulse frame) : Prop :=
  AffordableDyadic pulse.before.fields pulse.index ∧
  pulse.after.fields = paidResponse pulse.before.fields pulse.time ∧
  pulse.after.source = pulse.before.source ∧ pulse.after.body = pulse.before.body ∧
  pulse.after.paidRawReserve = pulse.before.paidRawReserve

def nativePulse (old : NativeActive frame) (margin : 0 < old.fields.reserve) : Pulse frame :=
  ⟨old,affordableIndex old.fields margin,
    ⟨old.source,generatedResponse old.fields margin,
      (generated_response_paid old.fields old.good margin).2.1,old.body,old.actual,old.paidRawReserve⟩⟩

theorem native_pulse_valid (old : NativeActive frame) (margin : 0 < old.fields.reserve) :
    (nativePulse old margin).Valid :=
  ⟨affordable_index_spec old.fields margin,rfl,rfl,rfl,rfl⟩

theorem pulse_paid (pulse : Pulse frame) (valid : pulse.Valid) :
    0 < pulse.time ∧ 0 < pulse.after.fields.reserve ∧
    pulse.after.fields.account = pulse.before.fields.account ∧
    pulse.after.fields.Ne = pulse.before.fields.Ne ∧
    pulse.after.fields.nuclei = pulse.before.fields.nuclei ∧
    pulse.after.fields.waterOrigins = pulse.before.fields.waterOrigins := by
  rw [valid.2.1]
  exact ⟨dyadic_time_positive _,sub_pos.mpr valid.1,(paid_response_account _ _).2.2,rfl,rfl,rfl⟩

/-- A failed chemical stage can retain an older active field. Its source equality
is tested before a new physical pulse is generated. -/
def step (current : NativeCursor frame) : Except Failure (NativeCursor frame × Pulse frame) := by
  classical
  exact match current.active with
    | none => .error .missingActive
    | some old =>
      if same : old.source = current.current then
        if margin : 0 < old.fields.reserve then
          let pulse := nativePulse old margin
          .ok ({current with active := some pulse.after},pulse)
        else .error (.exhausted old.fields.reserve)
      else .error .staleActive

def Ready (current : NativeCursor frame) : Prop :=
  ∃ old, current.active = some old ∧ old.source = current.current ∧ 0 < old.fields.reserve

theorem step_generated (current next : NativeCursor frame) (pulse : Pulse frame)
    (actual : step current = .ok (next,pulse)) :
    current.active = some pulse.before ∧ pulse.before.source = current.current ∧
    next.active = some pulse.after ∧ next.current = current.current ∧ next.stages = current.stages ∧
    pulse.Valid ∧ Ready next := by
  unfold step at actual
  cases selected : current.active with
  | none => simp only [selected] at actual; cases actual
  | some old =>
    simp only [selected] at actual
    split at actual
    · rename_i same
      split at actual
      · rename_i margin
        cases Except.ok.inj actual
        exact ⟨rfl,same,rfl,rfl,rfl,native_pulse_valid old margin,
          ⟨(nativePulse old margin).after,rfl,same,
            (generated_response_paid old.fields old.good margin).2.2.1⟩⟩
      · cases actual
    · cases actual

theorem step_ready (current : NativeCursor frame) (ready : Ready current) :
    ∃ next pulse, step current = .ok (next,pulse) := by
  classical
  obtain ⟨old,held,same,margin⟩ := ready
  refine ⟨{current with active := some (nativePulse old margin).after},nativePulse old margin,?_⟩
  simp only [step,held,dif_pos same,dif_pos margin]

structure Run (frame : CPS1Recycling.Frame) where
  cursor : NativeCursor frame
  pulses : List (Pulse frame)
  remaining : Nat
  failure : Option Failure

/-- Every pulse recomputes Fock and the nonlinear price from its actual previous
occupied field; no initial-field reset is performed. -/
def renew (current : NativeCursor frame) (depth : Nat) : Run frame :=
  Nat.rec (motive := fun _ => NativeCursor frame → Run frame)
    (fun current => ⟨current,[],0,none⟩)
    (fun depth recur current => match step current with
      | .error failure => ⟨current,[],depth+1,some failure⟩
      | .ok (next,pulse) =>
        let rest := recur next
        {rest with pulses := pulse :: rest.pulses}) depth current

theorem renew_zero (current : NativeCursor frame) : renew current 0 = ⟨current,[],0,none⟩ := rfl
theorem renew_succ (current : NativeCursor frame) (depth : Nat) :
    renew current (depth+1) = match step current with
      | .error failure => ⟨current,[],depth+1,some failure⟩
      | .ok (next,pulse) => let rest := renew next depth; {rest with pulses := pulse :: rest.pulses} := rfl

inductive Trace : NativeCursor frame → List (Pulse frame) → NativeCursor frame → Prop
  | nil (current) : Trace current [] current
  | cons (current next final : NativeCursor frame) (pulse : Pulse frame) (rest : List (Pulse frame))
      (actual : step current = .ok (next,pulse)) (tail : Trace next rest final) :
      Trace current (pulse :: rest) final

theorem renew_trace (current : NativeCursor frame) (depth : Nat) :
    Trace current (renew current depth).pulses (renew current depth).cursor := by
  induction depth generalizing current with
  | zero => exact .nil current
  | succ depth ih =>
    rw [renew_succ]
    cases actual : step current with
    | error failure => exact .nil current
    | ok output => exact .cons current output.1 _ output.2 _ actual (ih output.1)

theorem trace_whole (current final : NativeCursor frame) (pulses : List (Pulse frame))
    (trace : Trace current pulses final) :
    final.current = current.current ∧ final.stages = current.stages ∧
    ∀ pulse ∈ pulses, pulse.Valid := by
  induction trace with
  | nil current => exact ⟨rfl,rfl,by intro pulse held; cases held⟩
  | cons current next final pulse rest actual _ ih =>
    have generated := step_generated current next pulse actual
    refine ⟨ih.1.trans generated.2.2.2.1,ih.2.1.trans generated.2.2.2.2.1,?_⟩
    intro entry held
    rcases List.mem_cons.mp held with same | later
    · exact same ▸ generated.2.2.2.2.2.1
    · exact ih.2.2 entry later

theorem renew_whole (current : NativeCursor frame) (depth : Nat) :
    (renew current depth).cursor.current = current.current ∧
    (renew current depth).cursor.stages = current.stages ∧
    ∀ pulse ∈ (renew current depth).pulses, pulse.Valid :=
  trace_whole _ _ _ (renew_trace current depth)

theorem renew_ready (current : NativeCursor frame) (depth : Nat) (ready : Ready current) :
    (renew current depth).remaining = 0 ∧ (renew current depth).failure = none ∧
    (renew current depth).pulses.length = depth ∧ Ready (renew current depth).cursor := by
  induction depth generalizing current with
  | zero => exact ⟨rfl,rfl,rfl,ready⟩
  | succ depth ih =>
    obtain ⟨next,pulse,actual⟩ := step_ready current ready
    have generated := step_generated current next pulse actual
    have tail := ih next generated.2.2.2.2.2.2
    rw [renew_succ,actual]
    exact ⟨tail.1,tail.2.1,by simp only [List.length_cons,tail.2.2.1],tail.2.2.2⟩

def continueChemical (current : NativeCursor frame) (depth : Nat)
    (inputs : List CPS1ReactiveField.Carried.Input) : Run frame :=
  let physical := renew current depth
  {physical with cursor := CPS1ReactiveField.Carried.advanceAll physical.cursor inputs}

theorem continue_chemical_actual (current : NativeCursor frame) (depth : Nat)
    (inputs : List CPS1ReactiveField.Carried.Input) :
    (continueChemical current depth inputs).cursor =
      CPS1ReactiveField.Carried.advanceAll (renew current depth).cursor inputs ∧
    (continueChemical current depth inputs).cursor.current.ingress.atomic =
      CPS1AddressedHydrolysis.Atomic.advanceAll current.current.ingress.atomic (inputs.map Prod.fst) := by
  refine ⟨rfl,?_⟩
  change (CPS1ReactiveField.Carried.advanceAll (renew current depth).cursor inputs).current.ingress.atomic = _
  rw [CPS1ReactiveField.Carried.advance_all_source,(renew_whole current depth).1]

end
end CPS1ReactiveFieldDynamics
