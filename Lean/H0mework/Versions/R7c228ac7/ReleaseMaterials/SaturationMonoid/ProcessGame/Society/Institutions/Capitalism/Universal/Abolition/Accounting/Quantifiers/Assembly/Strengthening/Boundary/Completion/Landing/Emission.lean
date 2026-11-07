import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def actualHistory : ProductiveFiniteRootHistoryAt (ledgerRoot root boundary) where
  currentAt := Sum.inl
  initial_eq := rfl
  next_eq := fun cut => the_source_compiler_selects_its_computed_next root boundary (.inl cut)

def emittedVisit? : Option (SourceNativeCofinalVisitAt (ledgerRoot root boundary)) :=
  (actualHistory root boundary).generatedCofinalVisit? (by intros; rfl)

theorem the_original_actual_event_generates_the_completed_visit :
    (emittedVisit? root boundary).isSome = true := rfl

def actualVisit : SourceNativeCofinalVisitAt (ledgerRoot root boundary) :=
  (emittedVisit? root boundary).get (the_original_actual_event_generates_the_completed_visit root boundary)

theorem actualVisit_current : (actualVisit root boundary).current = .inr 0 := rfl

theorem actualVisit_raw_event : (actualVisit root boundary).event.val = boundary.event := rfl

theorem actualVisit_raw_target : rawCurrent root boundary (actualVisit root boundary).current = boundary.current := rfl

theorem actualVisit_raw_path (cut : Nat) :
    rawCurrent root boundary ((SchemaV root boundary).cofinal.pathAt (actualVisit root boundary).event cut) =
      V.cofinal.pathAt boundary.event cut :=
  every_emittable_event_keeps_the_original_path root boundary (actualVisit root boundary).event cut

theorem actual_finite_visits_keep_their_original_registered_current (cut : Nat) :
    rawCurrent root boundary ((actualVisit root boundary).history.visitAt cut).current =
      (boundary.history.visitAt cut).current := by
  rw [(actualVisit root boundary).history.visitAt_current]
  rfl

private def selected {current : Current}
    (entry : OpenResponsibilityAt (W root boundary) ((ledgerRoot root boundary).toRoot.supportAt current)) :=
  sourceNativeFiniteLedgerPatchGeneratedEntry? (source root boundary)
    (ledgerCompiler root boundary).ExactTransitionAt (ledgerCompiler root boundary).writeRowSource
    (ledgerCompiler root boundary).terminalRowSource
    ((ledgerCompiler root boundary).compile (emitted root boundary current))
    ((ledgerCompiler root boundary).compilePatch (emitted root boundary current)) entry

private theorem selected_isSome {current : Current}
    (entry : OpenResponsibilityAt (W root boundary) ((ledgerRoot root boundary).toRoot.supportAt current)) :
    (selected root boundary entry).isSome = true := by
  cases current <;> rfl

def generatedRow (visit : SourceNativeTemporalVisitAt (ledgerRoot root boundary))
    (entry : OpenResponsibilityAt (W root boundary) ((ledgerRoot root boundary).toRoot.supportAt visit.current)) :
    ((ledgerRoot root boundary).generatedAtTemporalVisit visit).GeneratedEntryRowAt entry :=
  .ofSourceRow ((selected root boundary entry).get (selected_isSome root boundary entry))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
