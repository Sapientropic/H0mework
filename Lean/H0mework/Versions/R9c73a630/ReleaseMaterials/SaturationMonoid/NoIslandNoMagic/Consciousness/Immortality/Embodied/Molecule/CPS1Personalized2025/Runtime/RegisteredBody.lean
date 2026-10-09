import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Positive
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.Runtime


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
noncomputable section
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open CPS1ResourceExecution CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate CPS1LiveEditing
open CPS1MaterialIncidence.NativeRootDataProbe CPS1MaterialIncidence.NativeAdoptionProbe
open CPS1MaterialIncidence.NativeBodyProbe CPS1MaterialIncidence.NativeBodyGenomeProbe
open Source.NativeRegistration
attribute [local irreducible] generated_input source_programme InputBodyAt DispositionBodyAt
attribute [local irreducible] input_body_next disposition_body_next DispositionWriteLaw InputWriteLaw
attribute [local irreducible] registeredNativeInput Delivery.afterParent Delivery.atParent Delivery.seed
attribute [local implicit_reducible] ProgrammeAt ClassicalRepairResponse GeneratedBodyAt


noncomputable def NativeBodyRootTransitionAt (current : Root.Native.Current) (write : Root.Native.Write current) : Prop :=
  current.input = registeredNativeInput ∧
  ∃ occurrence : InputOccurrence current.input,
    generated_input current.input = some occurrence ∧ IsNativeOutcome occurrence.outcome ∧
    NativeProfile current.input.supply ∧
    ∃ native : DispositionBodyAt occurrence.whole current.input.supply occurrence.repair occurrence.response
        occurrence.outcome occurrence.repairActual,
      HEq current.body native ∧ HEq write.body
        (disposition_body_next occurrence.whole current.input.supply occurrence.repair occurrence.response
          occurrence.outcome occurrence.repairActual native) ∧
      DispositionWriteLaw occurrence.whole current.input.supply occurrence.repair occurrence.response
        occurrence.outcome occurrence.repairActual native ∧ write.body ≠ current.body


section Strict
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

private theorem disposition_write_strict (body : DispositionBodyAt whole supply repair response outcome repairActual)
    (native : IsNativeOutcome outcome) (profile : NativeProfile supply)
    (law : DispositionWriteLaw whole supply repair response outcome repairActual body) :
    disposition_body_next whole supply repair response outcome repairActual body ≠ body := by
  classical
  cases outcome with
  | retained response failure => exact False.elim native
  | @responded receipt response before step selected source current =>
    simp only [DispositionWriteLaw,dif_pos profile] at law
    obtain ⟨represented,bodyActual,nextActual,_kernel,_stock,_history,_update,_invariant,_genome,
      _fullLength,_whole,_fields,_electrons,_account,_legacy,_duties,strict⟩ := law
    intro equal
    have nativeEqual := eq_of_heq (nextActual.symm.trans ((heq_of_eq equal).trans bodyActual))
    exact strict (congrArg (fun body => body.current.state) nativeEqual)

end Strict


private theorem registered_current_transition (current : Root.Native.Current)
    (registered : current.input = registeredNativeInput) (write : Root.Native.Write current) :
    NativeBodyRootTransitionAt current write := by
  cases current with
  | mk phase input body =>
    dsimp only [Root.Native.Current.input] at registered
    subst input
    obtain ⟨occurrence,actual,native,profile⟩ := registered_generated_input_native
    have law := input_write_law registeredNativeInput body
    unfold InputWriteLaw at law
    rw [actual] at law
    obtain ⟨represented,bodyActual,nextActual,writeLaw⟩ := law
    have strict := disposition_write_strict occurrence.whole registeredNativeInput.supply occurrence.repair
      occurrence.response occurrence.outcome occurrence.repairActual represented native profile writeLaw
    refine ⟨rfl,occurrence,actual,native,profile,represented,bodyActual,?_,writeLaw,?_⟩
    · exact (heq_of_eq write.actual).trans nextActual
    · intro equal
      have nativeEqual := eq_of_heq (nextActual.symm.trans
        ((heq_of_eq (write.actual.symm.trans equal)).trans bodyActual))
      exact strict nativeEqual


noncomputable def registered_body_runtime : Nat → LivingRuntimeState Delivery.process
  | 0 => Delivery.seed
  | n+1 => (registered_body_runtime n).tick.next

private theorem registered_body_zero : registered_body_runtime 0 = Delivery.seed := rfl

private theorem registered_body_succ (n : Nat) :
    registered_body_runtime (n+1) = (registered_body_runtime n).tick.next := rfl

attribute [local irreducible] registered_body_runtime


theorem registered_body_seed_current :
    (registered_body_runtime 0).current.visit.current = Root.Native.initial registeredNativeInput := by
  rw [registered_body_zero]
  unfold Delivery.seed
  rfl

private theorem registered_body_input (n : Nat) :
    (registered_body_runtime n).current.visit.current.input = registeredNativeInput := by
  induction n with
  | zero =>
    exact (congrArg Root.Native.Current.input registered_body_seed_current).trans
      (Root.Native.initial_input registeredNativeInput)
  | succ n previous =>
    rw [registered_body_succ]
    exact (congrArg Root.Native.Current.input (Delivery.full_native_current_next (registered_body_runtime n))).trans
      ((Root.Native.next_input (registered_body_runtime n).current.visit.current).trans previous)

private theorem registered_runtime_transition (runtime : LivingRuntimeState Delivery.process)
    (registered : runtime.current.visit.current.input = registeredNativeInput) :
    NativeBodyRootTransitionAt runtime.current.visit.current (Delivery.readNativeWrite runtime) ∧
      (type_of% (Delivery.native_material_factorizes runtime)) ∧
      Delivery.readNativeBody runtime = runtime.current.visit.current.body ∧
      Delivery.readNativeWrite runtime = runtime.emittedOccurrence.2 ∧
      Delivery.readWrittenNativeBody runtime =
        input_body_next runtime.current.visit.current.input (Delivery.readNativeBody runtime) ∧
      Delivery.readNativeBody runtime.tick.next = Delivery.readWrittenNativeBody runtime ∧
      Delivery.readNativeBody runtime.tick.next =
        input_body_next runtime.current.visit.current.input (Delivery.readNativeBody runtime) ∧
      Delivery.readWrittenNativeBody runtime ≠ Delivery.readNativeBody runtime := by
  have transition := registered_current_transition runtime.current.visit.current registered
    (Delivery.readNativeWrite runtime)
  refine ⟨transition,Delivery.native_material_factorizes runtime,Delivery.native_material_source_actual runtime,
    Delivery.native_material_write_actual runtime,Delivery.native_written_body_actual runtime,?_,
    Delivery.literal_native_body_next runtime,?_⟩
  · exact (Delivery.literal_native_body_next runtime).trans (Delivery.native_written_body_actual runtime).symm
  · intro equal
    obtain ⟨_registered,occurrence,_actual,_native,_profile,represented,_old,_new,_law,strict⟩ := transition
    exact strict (equal.trans (Delivery.native_material_source_actual runtime))

theorem source_generated_native_body_root_next (n : Nat) :
    type_of% (registered_runtime_transition (registered_body_runtime n) (registered_body_input n)) :=
  registered_runtime_transition (registered_body_runtime n) (registered_body_input n)

private theorem runtime_input_next (runtime : LivingRuntimeState Delivery.process) :
    runtime.tick.next.current.visit.current.input = runtime.current.visit.current.input :=
  (congrArg Root.Native.Current.input (Delivery.full_native_current_next runtime)).trans
    (Root.Native.next_input runtime.current.visit.current)

private theorem after_parent_registered :
    Delivery.afterParent.current.visit.current.input = registeredNativeInput := by
  with_unfolding_all rfl


theorem source_generated_native_body_after_parent :
    NativeBodyRootTransitionAt Delivery.afterParent.current.visit.current
      (Delivery.readNativeWrite Delivery.afterParent) ∧
    (type_of% (Delivery.native_material_factorizes Delivery.afterParent)) :=
  ⟨registered_current_transition Delivery.afterParent.current.visit.current after_parent_registered
    (Delivery.readNativeWrite Delivery.afterParent),
    Delivery.native_material_factorizes Delivery.afterParent⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
