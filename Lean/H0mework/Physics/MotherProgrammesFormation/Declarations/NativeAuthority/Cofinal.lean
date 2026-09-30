import H0mework.Foundation.Authority.CausalEntry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace MotherNativeAuthority

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}

/-- The fixed root supplies the event and path. Productivity is tested internally. -/
noncomputable def formCofinal (root : SourceNativeLivingRootClosure N V) :
    Option (SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot) := by
  classical
  exact match emitted : V.cofinal.emit? with
  | none => none
  | some event =>
      if compatible :
          V.cofinal.pathAt event 0 = root.toAuthoritativeRoot.toRoot.source.initial ∧
          ∀ index, (root.toAuthoritativeRoot.toRoot.evolutionAt
            (V.cofinal.pathAt event index)).nextCurrent? =
              some (V.cofinal.pathAt event (index + 1)) then
        let history : ProductiveFiniteRootHistoryAt root.toAuthoritativeRoot.toLedgerRoot :=
          ⟨V.cofinal.pathAt event, compatible.1, compatible.2⟩
        history.generatedCofinalVisit? (fun {other} otherEmitted _ => by
          have same : other = event := Option.some.inj (otherEmitted.symm.trans emitted)
          cases same
          rfl)
      else none

theorem formCofinal_recovers (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot) :
    formCofinal root = some visit := by
  have compatible :
      V.cofinal.pathAt visit.event 0 = root.toAuthoritativeRoot.toRoot.source.initial ∧
      ∀ index, (root.toAuthoritativeRoot.toRoot.evolutionAt
        (V.cofinal.pathAt visit.event index)).nextCurrent? =
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

end MotherNativeAuthority
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
