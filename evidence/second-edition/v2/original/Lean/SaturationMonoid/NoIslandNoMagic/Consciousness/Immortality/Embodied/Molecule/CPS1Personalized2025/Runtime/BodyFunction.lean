import CPS1MaterialIncidence.NativeBodyFunction
import SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime.RegisteredBody

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
open CPS1MaterialIncidence.NativeBodyFunctionProbe
open Source.NativeRegistration
attribute [local irreducible] generated_input source_programme InputBodyAt DispositionBodyAt
attribute [local irreducible] input_body_next disposition_body_next DispositionWriteLaw InputWriteLaw
attribute [local irreducible] registeredNativeInput Delivery.afterParent Delivery.atParent Delivery.seed registered_body_runtime
attribute [local implicit_reducible] ProgrammeAt ClassicalRepairResponse GeneratedBodyAt

section Disposition
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

/-- The existential is consumed in Prop. It identifies the stored body and
actual writer; the function factory receives that same typed native body. -/
def FunctionAtDisposition {α : Type} (beforeBody afterBody : α) : Prop := by
  classical
  cases outcome with
  | retained response failure => exact False
  | @responded receipt response before step selected source current =>
      exact if profile : NativeProfile supply then
        let paid := source_paid_data whole supply profile receipt repairActual.symm source current
        let continuation := source_continuation_data paid
        ∃ body : GeneratedBodyAt whole supply profile receipt repairActual.symm source paid continuation,
          ∃ function : NativeBodyFunction body,
            function = source_generated_native_body_function body ∧
            HEq beforeBody body ∧ HEq afterBody function.next ∧
            BodyUpdate receipt _ _ body function.event function.next ∧
            BodyInvariant receipt _ _ function.next ∧
            DispositionLaw continuation.focus function.disposition
      else False

attribute [local irreducible] FunctionAtDisposition

private theorem function_at_actual_write {α : Type} (beforeBody afterBody : α)
    (body : DispositionBodyAt whole supply repair response outcome repairActual)
    (beforeActual : HEq beforeBody body)
    (afterActual : HEq afterBody (disposition_body_next whole supply repair response outcome repairActual body))
    (native : IsNativeOutcome outcome) (profile : NativeProfile supply)
    (law : DispositionWriteLaw whole supply repair response outcome repairActual body) :
    FunctionAtDisposition whole supply repair response outcome repairActual beforeBody afterBody := by
  classical
  cases outcome with
  | retained response failure => exact False.elim native
  | @responded receipt response before step selected source current =>
      simp only [FunctionAtDisposition,dif_pos profile]
      simp only [DispositionWriteLaw,dif_pos profile] at law
      obtain ⟨represented,bodyActual,nextActual,_kernel,_stock,_history,_update,_invariant,_genome,
        _fullLength,_whole,_fields,_electrons,_account,_legacy,_duties,_strict⟩ := law
      let function := source_generated_native_body_function represented
      have actualNext : function.next = body_next receipt represented := by
        simpa only [body_next,body_write_at,body_event_at] using function.actual_next
      refine ⟨represented,function,rfl,beforeActual.trans bodyActual,
        (afterActual.trans nextActual).trans (heq_of_eq actualNext.symm),?_,function.invariant,
        function.actual_disposition⟩
      rw [function.writeActual]
      exact body_write_law receipt _ _ represented function.event

end Disposition

/-- The same installed occurrence carries its typed function and literal
successor. The native body is recovered in Prop, never selected as a new seed. -/
def NativeBodyFunctionRootAt (runtime : LivingRuntimeState Delivery.process) : Prop :=
  NativeBodyRootTransitionAt runtime.current.visit.current (Delivery.readNativeWrite runtime) ∧
  (∃ occurrence : InputOccurrence runtime.current.visit.current.input,
    generated_input runtime.current.visit.current.input = some occurrence ∧
    FunctionAtDisposition occurrence.whole runtime.current.visit.current.input.supply occurrence.repair
      occurrence.response occurrence.outcome occurrence.repairActual runtime.current.visit.current.body
      (Delivery.readNativeWrite runtime).body) ∧
  (type_of% (Delivery.native_material_factorizes runtime)) ∧
  Delivery.readNativeBody runtime = runtime.current.visit.current.body ∧
  Delivery.readNativeWrite runtime = runtime.emittedOccurrence.2 ∧
  Delivery.readNativeBody runtime.tick.next = Delivery.readWrittenNativeBody runtime

private theorem native_function_root_actual (current : Root.Native.Current) (write : Root.Native.Write current)
    (transition : NativeBodyRootTransitionAt current write) :
    ∃ occurrence : InputOccurrence current.input,
      generated_input current.input = some occurrence ∧
      FunctionAtDisposition occurrence.whole current.input.supply occurrence.repair occurrence.response
        occurrence.outcome occurrence.repairActual current.body write.body := by
  obtain ⟨_registered,occurrence,actual,native,profile,represented,beforeActual,afterActual,law,_strict⟩ := transition
  exact ⟨occurrence,actual,function_at_actual_write occurrence.whole current.input.supply occurrence.repair
    occurrence.response occurrence.outcome occurrence.repairActual current.body write.body represented
    beforeActual afterActual native profile law⟩

private theorem native_function_installed_next (runtime : LivingRuntimeState Delivery.process)
    (transition : NativeBodyRootTransitionAt runtime.current.visit.current (Delivery.readNativeWrite runtime)) :
    NativeBodyFunctionRootAt runtime :=
  ⟨transition,native_function_root_actual _ _ transition,Delivery.native_material_factorizes runtime,
    Delivery.native_material_source_actual runtime,Delivery.native_material_write_actual runtime,
    (Delivery.literal_native_body_next runtime).trans (Delivery.native_written_body_actual runtime).symm⟩

theorem source_generated_native_body_root_function (n : Nat) :
    NativeBodyFunctionRootAt (registered_body_runtime n) :=
  native_function_installed_next (registered_body_runtime n) (source_generated_native_body_root_next n).1

theorem source_generated_native_body_after_parent_function : NativeBodyFunctionRootAt Delivery.afterParent :=
  native_function_installed_next Delivery.afterParent source_generated_native_body_after_parent.1

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
