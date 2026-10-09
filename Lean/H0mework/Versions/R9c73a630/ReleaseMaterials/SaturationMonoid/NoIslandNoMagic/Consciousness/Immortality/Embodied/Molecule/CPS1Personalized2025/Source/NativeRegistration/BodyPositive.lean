import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Positive
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeRootNextLaw
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root.NativeCurrent

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate CPS1LiveEditing
open CPS1MaterialIncidence.NativeRootDataProbe CPS1MaterialIncidence.NativePrepareNextProbe
open CPS1MaterialIncidence.NativePrepareBinding CPS1MaterialIncidence.NativeAdoptionProbe
open CPS1MaterialIncidence.NativeBodyProbe CPS1MaterialIncidence.NativeBodyGenomeProbe
attribute [local irreducible] generated_input source_programme InputBodyAt DispositionBodyAt
attribute [local irreducible] source_input_body input_body_next disposition_body_next
attribute [local irreducible] source_paid_data source_continuation_data source_prepared_data
attribute [local irreducible] native_origin_germ source_adopted_data body_next
attribute [local implicit_reducible] ProgrammeAt ClassicalRepairResponse GeneratedBodyAt

universe u v
private theorem option_case_some {α : Type u} {β : Sort v} {source : Option α} {value : α}
    (atNone : source = none → β) (atSome : (value : α) → source = some value → β)
    (actual : source = some value) :
    Option.casesOn (motive := fun value => source = value → β) source atNone atSome rfl = atSome value actual := by
  cases actual
  rfl

private theorem selected_source_body (input : RegisteredNativeInput) (occurrence : InputOccurrence input)
    (actual : generated_input input = some occurrence) :
    HEq (source_input_body input)
      (source_disposition_body occurrence.whole input.supply occurrence.repair occurrence.response
        occurrence.outcome occurrence.repairActual) := by
  unfold source_input_body
  rw [option_case_some _ _ actual]
  unfold Eq.ndrec
  rw [apply_eqRec (fun x _ => generated_input input = x)]
  simp only [eq_mpr_eq_cast]
  apply HEq.trans (cast_heq _ _)
  exact HEq.rfl

private theorem selected_next (input : RegisteredNativeInput) (occurrence : InputOccurrence input)
    (actual : generated_input input = some occurrence) (body : InputBodyAt input)
    (native : DispositionBodyAt occurrence.whole input.supply occurrence.repair occurrence.response
      occurrence.outcome occurrence.repairActual) (same : HEq body native) :
    HEq (input_body_next input body)
      (disposition_body_next occurrence.whole input.supply occurrence.repair occurrence.response
        occurrence.outcome occurrence.repairActual native) := by
  have law := input_write_law input body
  unfold InputWriteLaw at law
  rw [actual] at law
  obtain ⟨represented,representedActual,nextActual,_⟩ := law
  have equal : represented = native := eq_of_heq (representedActual.symm.trans same)
  subst represented
  exact nextActual

section Run
variable {frame : CPS1Recycling.Frame} {origin : CPS1ReactiveNuclear.SourceCursor frame}
  {water : Nat} {material : List RawSupply} {path : CPS1Recycling.SplitSite}
  {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
  {physical : PhysicalRaw} {depth : Nat}
  (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
  {responseRaw : WholeRaw} {exchange : CPS1PhosphorylExchange.Raw}
  (repair : LocalRepairDisposition (initialBody ⟨frame,origin⟩))
  (response : WholeResponse repair responseRaw)
  (outcome : CPS1PhosphorylExchange.Disposition responseRaw exchange repair response)
  (repairActual : repair = repairWhole whole supply)

def NativeBodyRun {α : Type} (initial first second : α) : Prop := by
  classical
  cases outcome with
  | retained response failure => exact False
  | @responded receipt response before step selected source current =>
    exact if profile : NativeProfile supply then
      let paid := source_paid_data whole supply profile receipt repairActual.symm source current
      let continuation := source_continuation_data paid
      let returned := source_prepared_data whole supply profile receipt repairActual.symm source paid continuation
      let germ := native_origin_germ returned.occurrence
      let adopted := source_adopted_data returned germ
      let body := source_generated_body_at whole supply profile receipt repairActual.symm source paid continuation
      let middle := body_next receipt body
      let next := body_next receipt middle
      HEq initial body ∧ HEq first middle ∧ HEq second next ∧
        middle.current.state ≠ body.current.state ∧ next.current.state ≠ middle.current.state ∧
        body.current = adopted.next ∧
        (type_of% returned.execution_exact) ∧ (type_of% returned.next_exact) ∧
        (type_of% adopted.adoption_paid) ∧ (type_of% adopted.actual_execution) ∧
        (type_of% (body_event_actual receipt body)) ∧ (type_of% (body_event_actual receipt middle)) ∧
        middle.current = advanceSource body.current ∧ next.current = advanceSource middle.current ∧
        middle.current.state = (CPS1MaterialIncidence.NativeResumableProbe.advanceNative body.current.state).next ∧
        next.current.state = (CPS1MaterialIncidence.NativeResumableProbe.advanceNative middle.current.state).next ∧
        middle.current.stock = (runPulse body.current).stock ∧ next.current.stock = (runPulse middle.current).stock ∧
        middle.history = body.history ++ [.written body.current (body_event_at receipt body)] ∧
        next.history = middle.history ++ [.written middle.current (body_event_at receipt middle)] ∧
        (type_of% (body_next_law receipt body)) ∧ (type_of% (body_next_law receipt middle)) ∧
        (type_of% (body_next_invariant receipt body)) ∧ (type_of% (body_next_invariant receipt middle)) ∧
        (type_of% (body_next_genome receipt body)) ∧ (type_of% (body_next_genome receipt middle)) ∧
        native_damage middle.current = .fullLength ∧ native_damage next.current = .fullLength ∧
        (type_of% next.whole) ∧ (type_of% next.fields) ∧ (type_of% next.electrons) ∧ (type_of% next.full_account) ∧
        next.legacyRestriction = receipt.nextBody ∧
        middle.pending = independentDuties ∧ next.pending = independentDuties
    else False

attribute [local irreducible] NativeBodyRun

private theorem disposition_body_run (native : IsNativeOutcome outcome) (profile : NativeProfile supply) :
    let initial := source_disposition_body whole supply repair response outcome repairActual
    let first := disposition_body_next whole supply repair response outcome repairActual initial
    let second := disposition_body_next whole supply repair response outcome repairActual first
    NativeBodyRun whole supply repair response outcome repairActual initial first second := by
  classical
  cases outcome with
  | retained response failure => exact False.elim native
  | @responded receipt response before step selected source current =>
    let paid := source_paid_data whole supply profile receipt repairActual.symm source current
    let continuation := source_continuation_data paid
    let returned := source_prepared_data whole supply profile receipt repairActual.symm source paid continuation
    let germ := native_origin_germ returned.occurrence
    let adopted := source_adopted_data returned germ
    let body := source_generated_body_at whole supply profile receipt repairActual.symm source paid continuation
    let initial := source_disposition_body whole supply (.repaired receipt) response
      (.responded response before step selected source current) repairActual
    let first := disposition_body_next whole supply (.repaired receipt) response
      (.responded response before step selected source current) repairActual initial
    let second := disposition_body_next whole supply (.repaired receipt) response
      (.responded response before step selected source current) repairActual first
    have initialActual : HEq initial body := by
      dsimp only [initial,body,paid,continuation]
      have decision : Classical.propDecidable (NativeProfile supply) = .isTrue profile := Subsingleton.elim _ _
      simp only [source_disposition_body,decision,eq_mpr_eq_cast]
      with_unfolding_all exact (cast_heq _ _).trans HEq.rfl
    have firstLaw := disposition_write_law whole supply (.repaired receipt) response
      (.responded response before step selected source current) repairActual initial
    simp only [DispositionWriteLaw,dif_pos profile] at firstLaw
    obtain ⟨initialNative,initialNativeActual,firstActual,_⟩ := firstLaw
    have initialEqual : initialNative = body := eq_of_heq (initialNativeActual.symm.trans initialActual)
    subst initialNative
    have secondLaw := disposition_write_law whole supply (.repaired receipt) response
      (.responded response before step selected source current) repairActual first
    simp only [DispositionWriteLaw,dif_pos profile] at secondLaw
    obtain ⟨firstNative,firstNativeActual,secondActual,_⟩ := secondLaw
    have firstEqual : firstNative = body_next receipt body := eq_of_heq (firstNativeActual.symm.trans firstActual)
    subst firstNative
    simp only [NativeBodyRun,dif_pos profile]
    exact ⟨initialActual,firstActual,secondActual,body_next_strict receipt body,
      body_next_strict receipt (body_next receipt body),rfl,returned.execution_exact,returned.next_exact,
      adopted.adoption_paid,adopted.actual_execution,body_event_actual receipt body,
      body_event_actual receipt (body_next receipt body),body_next_kernel receipt body,
      body_next_kernel receipt (body_next receipt body),body_next_state receipt body,
      body_next_state receipt (body_next receipt body),body_next_stock receipt body,
      body_next_stock receipt (body_next receipt body),body_next_history receipt body,
      body_next_history receipt (body_next receipt body),body_next_law receipt body,
      body_next_law receipt (body_next receipt body),body_next_invariant receipt body,
      body_next_invariant receipt (body_next receipt body),body_next_genome receipt body,
      body_next_genome receipt (body_next receipt body),(body_next_invariant receipt body).fullLength,
      (body_next_invariant receipt (body_next receipt body)).fullLength,
      (body_next receipt (body_next receipt body)).whole,(body_next receipt (body_next receipt body)).fields,
      (body_next receipt (body_next receipt body)).electrons,(body_next receipt (body_next receipt body)).full_account,
      (body_next receipt (body_next receipt body)).legacy_actual,
      (body_next_invariant receipt body).pending,(body_next_invariant receipt (body_next receipt body)).pending⟩

private theorem body_run_transport {α β : Type} (initial first second : α) (native middle next : β)
    (initialActual : HEq initial native) (firstActual : HEq first middle) (secondActual : HEq second next)
    (law : NativeBodyRun whole supply repair response outcome repairActual native middle next) :
    NativeBodyRun whole supply repair response outcome repairActual initial first second := by
  cases initialActual
  have firstEqual : first = middle := eq_of_heq firstActual
  have secondEqual : second = next := eq_of_heq secondActual
  subst first
  subst second
  exact law

private theorem body_run_not_reset {α : Type} (initial first second : α)
    (law : NativeBodyRun whole supply repair response outcome repairActual initial first second) :
    first ≠ initial ∧ second ≠ first := by
  classical
  cases outcome with
  | retained response failure =>
    unfold NativeBodyRun at law
    exact False.elim law
  | @responded receipt response before step selected source current =>
    by_cases profile : NativeProfile supply
    · simp only [NativeBodyRun,dif_pos profile] at law
      obtain ⟨initialActual,firstActual,secondActual,firstStrict,secondStrict,_⟩ := law
      constructor
      · intro equal
        have nativeEqual := eq_of_heq (firstActual.symm.trans ((heq_of_eq equal).trans initialActual))
        exact firstStrict (congrArg (fun body => body.current.state) nativeEqual)
      · intro equal
        have nativeEqual := eq_of_heq (secondActual.symm.trans ((heq_of_eq equal).trans firstActual))
        exact secondStrict (congrArg (fun body => body.current.state) nativeEqual)
    · simp only [NativeBodyRun,dif_neg profile] at law

end Run

def NativeBodyRunAt (input : RegisteredNativeInput) (occurrence : InputOccurrence input) : Prop :=
  NativeBodyRun occurrence.whole input.supply occurrence.repair occurrence.response occurrence.outcome
    occurrence.repairActual (Root.Native.initial input).body
    (Root.Native.next (Root.Native.initial input)).body
    (Root.Native.next (Root.Native.next (Root.Native.initial input))).body

private theorem input_body_run (input : RegisteredNativeInput) (occurrence : InputOccurrence input)
    (actual : generated_input input = some occurrence) (native : IsNativeOutcome occurrence.outcome)
    (profile : NativeProfile input.supply) : NativeBodyRunAt input occurrence := by
  let initial := source_disposition_body occurrence.whole input.supply occurrence.repair occurrence.response
    occurrence.outcome occurrence.repairActual
  let first := disposition_body_next occurrence.whole input.supply occurrence.repair occurrence.response
    occurrence.outcome occurrence.repairActual initial
  let second := disposition_body_next occurrence.whole input.supply occurrence.repair occurrence.response
    occurrence.outcome occurrence.repairActual first
  have initialActual : HEq (source_input_body input) initial := selected_source_body input occurrence actual
  have firstActual := selected_next input occurrence actual (source_input_body input) initial initialActual
  have secondActual := selected_next input occurrence actual (input_body_next input (source_input_body input)) first firstActual
  exact body_run_transport occurrence.whole input.supply occurrence.repair occurrence.response occurrence.outcome
    occurrence.repairActual (source_input_body input) (input_body_next input (source_input_body input))
    (input_body_next input (input_body_next input (source_input_body input))) initial first second
    initialActual firstActual secondActual
    (disposition_body_run occurrence.whole input.supply occurrence.repair occurrence.response occurrence.outcome
      occurrence.repairActual native profile)

theorem registered_native_body_run :
    ∃ occurrence : InputOccurrence registeredNativeInput,
      generated_input registeredNativeInput = some occurrence ∧ NativeBodyRunAt registeredNativeInput occurrence := by
  obtain ⟨occurrence,actual,native,profile⟩ := registered_generated_input_native
  exact ⟨occurrence,actual,input_body_run registeredNativeInput occurrence actual native profile⟩

theorem registered_native_body_not_reset :
    (Root.Native.next (Root.Native.initial registeredNativeInput)).body ≠
      (Root.Native.initial registeredNativeInput).body ∧
    (Root.Native.next (Root.Native.next (Root.Native.initial registeredNativeInput))).body ≠
      (Root.Native.next (Root.Native.initial registeredNativeInput)).body := by
  obtain ⟨occurrence,_actual,law⟩ := registered_native_body_run
  exact body_run_not_reset occurrence.whole registeredNativeInput.supply occurrence.repair occurrence.response
    occurrence.outcome occurrence.repairActual _ _ _ law

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
