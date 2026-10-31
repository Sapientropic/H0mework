import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (word : RawEvent Party Good Port Technology Instrument)

theorem entries_finite (phase : Phase) :
    Finite (OpenResponsibilityAt (N input frame claim) (support input frame visit claim word phase)) := by
  have targetFinite : Finite (OpenResponsibilityAt frame.N
      (sourceSuccessor input frame visit).targetOccurrence.1) := by
    have all : ∀ actual : SourceNativeLedgerGeneratedSuccessorAt
        (frame.root.emitted visit.current) (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current),
        Finite (OpenResponsibilityAt frame.N actual.targetOccurrence.1) := by
      rw [(frame.program.emit visit.current).generated_eq]
      intro _
      exact RootGeneratedDebtActivationJointSource.Native.Request.Inventory.target_finite frame.program visit.current
    exact all _
  cases phase with
  | pending =>
      exact Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _
        (RootGeneratedDebtActivationJointSource.Native.Request.Inventory.source_finite frame.program visit.current)
  | declared => exact Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _ targetFinite
  | observed => exact Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _ targetFinite

def flow : Compiler.Flow (N input frame claim) where
  Current := Phase
  initial := .pending
  support := support input frame visit claim word
  next := next
  writes := fun phase => by
    classical
    exact match phase with
    | .pending => true
    | .declared => true
    | .observed => false
  evolution := evolution input frame visit claim word
  finite := entries_finite input frame visit claim word
  injective := evolution_injective input frame visit claim word
  open_fibres := open_fibres input frame claim

abbrev V := Compiler.V (flow input frame visit claim word)

abbrev baseRoot := Compiler.livingRoot (flow input frame visit claim word)

def previousInquiry : SourceNativeProjectionLaw (Compiler.ledgerSource (flow input frame visit claim word)) where
  Projection := frame.root.toAuthoritativeRoot.source.projectionLaw.Projection
  ActiveAt := fun projection {_} _ =>
    frame.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt projection (frame.root.emitted visit.current)
  InactiveAt := fun projection {_} _ =>
    frame.root.toAuthoritativeRoot.source.projectionLaw.InactiveAt projection (frame.root.emitted visit.current)
  classify := fun projection {_} _ =>
    frame.root.toAuthoritativeRoot.source.projectionLaw.classify projection (frame.root.emitted visit.current)
  PayloadAt := fun projection {_} _ active =>
    frame.root.toAuthoritativeRoot.source.projectionLaw.PayloadAt projection (frame.root.emitted visit.current) active
  project := fun projection {_} _ active =>
    frame.root.toAuthoritativeRoot.source.projectionLaw.project projection (frame.root.emitted visit.current) active

def root := (baseRoot input frame visit claim word).withProjectionCoface (previousInquiry input frame visit claim word)

def oldProjection (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (root input frame visit claim word).toAuthoritativeRoot.source.projectionLaw.Projection := .component projection

theorem oldProjection_injective : Function.Injective (oldProjection input frame visit claim word) := by
  intro left right same
  injection same

theorem every_previous_inquiry_outcome_is_literal
    (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((root input frame visit claim word).toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (oldProjection input frame visit claim word projection) ((root input frame visit claim word).emitted .pending))
      (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (frame.root.emitted visit.current)) := by
  dsimp only [root,SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeLivingRootClosure.toAuthoritativeRoot,SourceNativeAuthoritySource.withProjectionCoface,
    SourceNativeProjectionLaw.outcomeAt,oldProjection,previousInquiry]
  cases frame.root.source.base.projectionLaw.classify projection (frame.root.emitted visit.current) <;> rfl

#print axioms flow
#print axioms every_previous_inquiry_outcome_is_literal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source
