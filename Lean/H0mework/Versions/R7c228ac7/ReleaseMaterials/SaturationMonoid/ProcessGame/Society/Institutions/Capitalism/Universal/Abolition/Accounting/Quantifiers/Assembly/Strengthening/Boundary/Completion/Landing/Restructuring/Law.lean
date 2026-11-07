import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Vocabulary

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def law : SourceNativeLedgerRestructuringLaw (Landing.source root boundary) where
  vocabulary := vocabulary root boundary
  sourceEventAt := fun {current} _ => match current with
    | .inl cut => .inl ((oldLaw root).sourceEventAt (rawOccurrence root boundary (.inl cut)))
    | .inr phase => .inr (supportAt root boundary (.inr phase))
  obligationAt := fun {current} _ {_} row => obligationAt root boundary current row
  responsibilityKey := fun obligation => (entry root boundary obligation.content).2.1
  anchorKey := fun identity => match identity with
    | .inl old => (oldLaw root).anchorKey old
    | .inr added => added.1
  incidenceKey := fun incidence => match incidence with
    | .inl old => (oldLaw root).incidenceKey old
    | .inr added => added
  lineageKey := fun lineage => match lineage with
    | .inl old => (oldLaw root).lineageKey old
    | .inr added => added
  responsibility_commutes := by
    intro current occurrence support row
    exact congrArg (fun image : WorldEntry root boundary => image.2.1)
      (obligationAt_keeps_the_full_world_entry root boundary current row)
  anchor_commutes := by
    intro current occurrence support row
    rcases row with ⟨key,opened⟩
    cases key with
    | inl old => exact (oldLaw root).anchor_commutes (rawOccurrence root boundary current) ⟨old,opened⟩
    | inr _ => rfl
  incidence_commutes := by
    intro current occurrence support row
    rcases row with ⟨key,opened⟩
    cases key with
    | inl old => exact (oldLaw root).incidence_commutes (rawOccurrence root boundary current) ⟨old,opened⟩
    | inr _ => rfl
  lineage_commutes := by
    intro current occurrence support row
    rcases row with ⟨key,opened⟩
    cases key with
    | inl old => exact (oldLaw root).lineage_commutes (rawOccurrence root boundary current) ⟨old,opened⟩
    | inr _ => rfl
  obligationAt_injective := by
    intro current occurrence support left right same
    have projected := congrArg (fun obligation => entry root boundary obligation.content) same
    have exactEntries := (obligationAt_keeps_the_full_world_entry root boundary current left).symm.trans
      (projected.trans (obligationAt_keeps_the_full_world_entry root boundary current right))
    exact eq_of_heq (Sigma.mk.inj exactEntries).2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
