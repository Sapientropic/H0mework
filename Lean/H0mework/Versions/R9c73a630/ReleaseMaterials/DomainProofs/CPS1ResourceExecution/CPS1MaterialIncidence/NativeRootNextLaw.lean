import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeRootFromInput

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeRootDataProbe
noncomputable section
open CPS1ResourceExecution CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate CPS1LiveEditing
open NativePaidEvent NativeCPContinuationProbe NativePrepareNextProbe NativePrepareBinding
open NativeAmmoniaDynamics NativeAdoptionProbe NativeBodyProbe NativeBodyGenomeProbe
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
attribute [local irreducible] generated_input source_programme DispositionBodyAt input_body_next disposition_body_next
attribute [local irreducible] source_paid_data source_continuation_data source_prepared_data native_origin_germ source_adopted_data body_next
attribute [local implicit_reducible] ProgrammeAt ClassicalRepairResponse GeneratedBodyAt InputBodyAt

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

def DispositionWriteLaw (body : DispositionBodyAt whole supply repair response outcome repairActual) : Prop := by
  classical
  cases outcome with
  | retained response failure =>
      exact disposition_body_next whole supply _ response (.retained response failure) repairActual body = body
  | @responded receipt response before step selected source current =>
      let continued := disposition_body_next whole supply (.repaired receipt) response
        (.responded response before step selected source current) repairActual body
      exact if profile : NativeProfile supply then
        let paid := source_paid_data whole supply profile receipt repairActual.symm source current
        let continuation := source_continuation_data paid
        ∃ native : GeneratedBodyAt whole supply profile receipt repairActual.symm source paid continuation,
          HEq body native ∧ HEq continued (body_next receipt native) ∧
          (body_next receipt native).current = advanceSource native.current ∧
          (body_next receipt native).current.stock = (runPulse native.current).stock ∧
          (body_next receipt native).history = native.history ++ [.written native.current (body_event_at receipt native)] ∧
          (type_of% (body_next_law receipt native)) ∧ (type_of% (body_next_invariant receipt native)) ∧
          (type_of% (body_next_genome receipt native)) ∧
          native_damage (body_next receipt native).current = .fullLength ∧
          (type_of% (body_next receipt native).whole) ∧ (type_of% (body_next receipt native).fields) ∧
          (type_of% (body_next receipt native).electrons) ∧ (type_of% (body_next receipt native).full_account) ∧
          (body_next receipt native).legacyRestriction = receipt.nextBody ∧
          (body_next receipt native).pending = independentDuties ∧
          (body_next receipt native).current.state ≠ native.current.state
      else continued = body

attribute [local irreducible] DispositionWriteLaw

theorem disposition_write_law (body : DispositionBodyAt whole supply repair response outcome repairActual) :
    DispositionWriteLaw whole supply repair response outcome repairActual body := by
  classical
  cases outcome with
  | retained response failure =>
      unfold DispositionWriteLaw
      simp only [disposition_body_next]
  | @responded receipt response before step selected source current =>
      by_cases profile : NativeProfile supply
      · simp only [DispositionWriteLaw,dif_pos profile]
        let paid := source_paid_data whole supply profile receipt repairActual.symm source current
        let continuation := source_continuation_data paid
        have sameType : DispositionBodyAt whole supply (.repaired receipt) response
            (.responded response before step selected source current) repairActual =
            GeneratedBodyAt whole supply profile receipt repairActual.symm source paid continuation := by
          simp only [DispositionBodyAt,dif_pos profile]
          rfl
        let native := cast sameType body
        refine ⟨native,(cast_heq sameType body).symm,?_,body_next_kernel receipt native,body_next_stock receipt native,
          body_next_history receipt native,body_next_law receipt native,body_next_invariant receipt native,
          body_next_genome receipt native,(body_next_invariant receipt native).fullLength,
          (body_next receipt native).whole,(body_next receipt native).fields,(body_next receipt native).electrons,
          (body_next receipt native).full_account,(body_next receipt native).legacy_actual,
          (body_next_invariant receipt native).pending,body_next_strict receipt native⟩
        simp only [disposition_body_next,dif_pos profile,eq_mpr_eq_cast]
        apply HEq.trans (cast_heq _ _)
        exact HEq.rfl
      · simp only [DispositionWriteLaw,disposition_body_next,dif_neg profile]

end Disposition

universe u v

private theorem option_case_none {α : Type u} {β : Sort v} {source : Option α}
    (atNone : source = none → β) (atSome : (value : α) → source = some value → β)
    (actual : source = none) :
    Option.casesOn (motive := fun value => source = value → β) source atNone atSome rfl = atNone actual := by
  cases actual
  rfl

private theorem option_case_some {α : Type u} {β : Sort v} {source : Option α} {value : α}
    (atNone : source = none → β) (atSome : (value : α) → source = some value → β)
    (actual : source = some value) :
    Option.casesOn (motive := fun value => source = value → β) source atNone atSome rfl = atSome value actual := by
  cases actual
  rfl

def InputWriteLaw (input : RegisteredNativeInput) (body : InputBodyAt input) : Prop :=
  match generated_input input with
  | none => input_body_next input body = body
  | some occurrence =>
      ∃ native : DispositionBodyAt occurrence.whole input.supply occurrence.repair occurrence.response
          occurrence.outcome occurrence.repairActual,
        HEq body native ∧ HEq (input_body_next input body)
          (disposition_body_next occurrence.whole input.supply occurrence.repair occurrence.response
            occurrence.outcome occurrence.repairActual native) ∧
        DispositionWriteLaw occurrence.whole input.supply occurrence.repair occurrence.response
          occurrence.outcome occurrence.repairActual native

attribute [local irreducible] InputWriteLaw

theorem input_write_law (input : RegisteredNativeInput) (body : InputBodyAt input) : InputWriteLaw input body := by
  cases actual : generated_input input with
  | none =>
      unfold InputWriteLaw
      rw [actual]
      dsimp only
      unfold input_body_next
      rw [option_case_none _ _ actual]
      unfold Eq.ndrec
      rw [apply_eqRec (fun x _ => generated_input input = x)]
  | some occurrence =>
      unfold InputWriteLaw
      rw [actual]
      dsimp only
      have sameType : InputBodyAt input = DispositionBodyAt occurrence.whole input.supply occurrence.repair
          occurrence.response occurrence.outcome occurrence.repairActual := by
        simp only [InputBodyAt,actual]
      let native := cast sameType body
      refine ⟨native,(cast_heq sameType body).symm,?_,disposition_write_law occurrence.whole input.supply occurrence.repair
        occurrence.response occurrence.outcome occurrence.repairActual native⟩
      unfold input_body_next
      rw [option_case_some _ _ actual]
      unfold Eq.ndrec
      rw [apply_eqRec (fun x _ => generated_input input = x)]
      simp only [eq_mpr_eq_cast]
      apply HEq.trans (cast_heq _ _)
      exact HEq.rfl

theorem input_two_writes_law (input : RegisteredNativeInput) (body : InputBodyAt input) :
    InputWriteLaw input body ∧ InputWriteLaw input (input_body_next input body) :=
  ⟨input_write_law input body,input_write_law input (input_body_next input body)⟩

theorem source_input_two_writes (input : RegisteredNativeInput) :
    InputWriteLaw input (source_input_body input) ∧
      InputWriteLaw input (input_body_next input (source_input_body input)) :=
  input_two_writes_law input (source_input_body input)

end
end CPS1MaterialIncidence.NativeRootDataProbe
