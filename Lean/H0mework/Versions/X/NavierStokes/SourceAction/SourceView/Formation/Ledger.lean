import H0mework.Versions.X.NavierStokes.SourceAction.SourceView.Formation.Action.Law

set_option autoImplicit false
namespace SaturationMonoid.NavierStokes.NativeWindowMotherLedgerConsumer
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowMotherOccurrenceMaterial
noncomputable section
variable {nu : Viscosity}

def origin (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) : Anchor seed :=
  NativeWindowMotherActualLaw.restoreAnchor seed
    (fun query => NativeWindowMotherActualLaw.read seed (anchor,query))

theorem origin_eq (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) : origin seed anchor=anchor :=
  NativeWindowMotherActualLaw.whole_occurrence_restored seed anchor

abbrev Ledger (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) :=
  SourceNativeLedgerEvolutionAt (nativeTemporalSource seed) anchor.2

def ledger (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) : Ledger seed anchor :=
  Eq.mp (congrArg (Ledger seed) (origin_eq seed anchor))
    ((nativeTemporalLedgerCompiler seed).compile (origin seed anchor).2)

private theorem transport_value {X : Type*} (P : X → Type*) (value : ∀ x,P x)
    {x y : X} (same : x=y) : Eq.mp (congrArg P same) (value x)=value y := by
  cases same
  rfl

theorem ledger_eq (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) :
    ledger seed anchor=(nativeTemporalLedgerCompiler seed).compile anchor.2 :=
  transport_value (Ledger seed) (fun key => (nativeTemporalLedgerCompiler seed).compile key.2)
    (origin_eq seed anchor)

def successor (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) :
    SourceNativeLedgerGeneratedSuccessorAt anchor.2 (ledger seed anchor) := by
  rw [ledger_eq]
  rcases anchor with ⟨current,support,event⟩
  cases event <;> exact PUnit.unit

theorem successor_target (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) (query : Query) :
    (successor seed anchor).targetCurrent=NativeWindowMotherActualLaw.next seed (anchor,query) :=
  Option.some.inj ((successor seed anchor).next_eq.symm.trans
    (NativeWindowMotherActualLaw.next_compiled seed (anchor,query)))

theorem full_disposition (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed)
    (entry : OpenResponsibilityAt (N seed)
      ((nativeTemporalSource seed).toRootSource.account.supportOf anchor.2)) :
    (ledger seed anchor).entryDisposition entry=
      ((nativeTemporalLedgerCompiler seed).compile anchor.2).entryDisposition entry := by
  rw [ledger_eq]

theorem successor_emitted (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) :
    (successor seed anchor).targetOccurrence=nativeTemporalEmitted seed (successor seed anchor).targetCurrent := by
  have preserved (generated : Ledger seed anchor)
      (same : generated=(nativeTemporalLedgerCompiler seed).compile anchor.2)
      (next : SourceNativeLedgerGeneratedSuccessorAt anchor.2 generated) :
      next.targetOccurrence=nativeTemporalEmitted seed next.targetCurrent := by
    subst generated
    rcases anchor with ⟨current,support,event⟩
    cases event <;> rfl
  exact preserved (ledger seed anchor) (ledger_eq seed anchor) (successor seed anchor)

end
end SaturationMonoid.NavierStokes.NativeWindowMotherLedgerConsumer
