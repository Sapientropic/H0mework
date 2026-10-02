import H0mework.Versions.R2.Foundation.Cofinal.TemporalAnswer

/-! The original chronological constructors need only the ledger root.
The source-owned cofinal event and its entire productive path are retained;
no living terminal-handoff law is needed to generate an admitted visit. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmittedWorld
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
universe u
variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}

def formCofinal (root : SourceNativeLedgerRootClosure N V) : Option (SourceNativeCofinalVisitAt root) := by
  classical
  exact match emitted : V.cofinal.emit? with
  | none => none
  | some event =>
      if compatible :
          V.cofinal.pathAt event 0 = root.toRoot.source.initial ∧
          ∀ index, (root.toRoot.evolutionAt (V.cofinal.pathAt event index)).nextCurrent? =
            some (V.cofinal.pathAt event (index + 1)) then
        let history : ProductiveFiniteRootHistoryAt root :=
          ⟨V.cofinal.pathAt event, compatible.1, compatible.2⟩
        history.generatedCofinalVisit? (fun {other} otherEmitted _ => by
          have same : other = event := Option.some.inj (otherEmitted.symm.trans emitted)
          cases same
          rfl)
      else none

theorem formCofinal_recovers (root : SourceNativeLedgerRootClosure N V) (visit : SourceNativeCofinalVisitAt root) :
    formCofinal root = some visit := by
  have compatible :
      V.cofinal.pathAt visit.event 0 = root.toRoot.source.initial ∧
      ∀ index, (root.toRoot.evolutionAt (V.cofinal.pathAt visit.event index)).nextCurrent? =
        some (V.cofinal.pathAt visit.event (index + 1)) :=
    ⟨visit.history.initial_eq, visit.history.next_eq⟩
  unfold formCofinal
  split
  · rename_i absent
    cases visit.emitted_eq_event.symm.trans absent
  · rename_i event emitted
    have same : event = visit.event := Option.some.inj (emitted.symm.trans visit.emitted_eq_event)
    subst event
    split
    · unfold ProductiveFiniteRootHistoryAt.generatedCofinalVisit?
      split
      · rename_i absent
        cases visit.emitted_eq_event.symm.trans absent
      · apply congrArg some
        exact SourceNativeCofinalVisitAt.eq _ visit
    · rename_i incompatible
      exact False.elim (incompatible compatible)

def start (root : SourceNativeLedgerRootClosure N V) : Bool → Option (SourceNativeTemporalVisitAt root)
  | false => some (.finite root.toRoot.initialVisit)
  | true => (formCofinal root).map SourceNativeTemporalVisitAt.cofinal

def advance (root : SourceNativeLedgerRootClosure N V) (visit : SourceNativeTemporalVisitAt root) :
    Option (SourceNativeTemporalVisitAt root) :=
  match next_eq : (root.toRoot.evolutionAt visit.current).nextCurrent? with
  | none => none
  | some _ => some (visit.next next_eq)

theorem advance_recovers (root : SourceNativeLedgerRootClosure N V) (visit : SourceNativeTemporalVisitAt root)
    {next : V.Current} (next_eq : (root.toRoot.evolutionAt visit.current).nextCurrent? = some next) :
    advance root visit = some (visit.next next_eq) := by
  unfold advance
  split
  · rename_i absent
    cases next_eq.symm.trans absent
  · rename_i other produced
    have same := Option.some.inj (produced.symm.trans next_eq)
    cases same
    rfl

def generate (root : SourceNativeLedgerRootClosure N V) (cofinal : Bool) : Nat → Option (SourceNativeTemporalVisitAt root)
  | 0 => start root cofinal
  | steps + 1 => (generate root cofinal steps).bind (advance root)

theorem every_finite (root : SourceNativeLedgerRootClosure N V) {current : V.Current}
    (history : root.toRoot.ReachableAt current) :
    ∃ steps, generate root false steps = some ⟨current, .finite history⟩ := by
  induction history with
  | initial => exact ⟨0, rfl⟩
  | @step current next prior next_eq ih =>
    obtain ⟨steps, formed⟩ := ih
    refine ⟨steps + 1, ?_⟩
    rw [generate, formed, Option.bind_some]
    exact advance_recovers root ⟨current, .finite prior⟩ next_eq

theorem every_postCofinal (root : SourceNativeLedgerRootClosure N V) {current : V.Current}
    (history : SourceNativePostCofinalReachableAt root current) :
    ∃ steps, generate root true steps = some ⟨current, .postCofinal history⟩ := by
  induction history with
  | cofinal visit =>
    refine ⟨0, ?_⟩
    rw [generate, start, formCofinal_recovers root visit]
    rfl
  | @step current next prior next_eq ih =>
    obtain ⟨steps, formed⟩ := ih
    refine ⟨steps + 1, ?_⟩
    rw [generate, formed, Option.bind_some]
    exact advance_recovers root ⟨current, .postCofinal prior⟩ next_eq

theorem every_visit (root : SourceNativeLedgerRootClosure N V) (visit : SourceNativeTemporalVisitAt root) :
    ∃ cofinal steps, generate root cofinal steps = some visit := by
  rcases visit with ⟨current, history⟩
  cases history with
  | finite history =>
    obtain ⟨steps, formed⟩ := every_finite root history
    exact ⟨false, steps, formed⟩
  | postCofinal history =>
    obtain ⟨steps, formed⟩ := every_postCofinal root history
    exact ⟨true, steps, formed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmittedWorld
