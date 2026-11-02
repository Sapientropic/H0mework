import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Base
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Transport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (start : Cursor.State input)

abbrev N := world input (ProgrammeSource.N input) start.account.generated

structure Current where
  cursor : Cursor.State input
  native : Nonempty ((process input).Run start.account.current cursor.account.current)
  positive : 0 < Cursor.physicalVisitIndex input cursor

def initial (positive : 0 < Cursor.physicalVisitIndex input start) : Current input start :=
  ⟨start, ⟨.nil⟩, positive⟩

def next (current : Current input start) : Current input start :=
  ⟨Cursor.next input current.cursor,
    current.native.map (fun prior => prior.concatRuns (process input) (Cursor.native input current.cursor)),
    current.positive.trans_le (Cursor.physical_index_monotone input current.cursor)⟩

def supportAt (current : Current input start) : (N input start).Support :=
  support input (ProgrammeSource.N input) (Cursor.baseSupport input current.cursor)
    start.account.generated current.cursor.account current.native

def wholeEvolution (current : Current input start) :
    LedgerWriteEvolutionAt (N input start) ⟨supportAt input start current⟩
      ⟨supportAt input start (next input start current)⟩ :=
  transport input (ProgrammeSource.N input)
    (Cursor.baseSupport input current.cursor) (Cursor.baseSupport input (Cursor.next input current.cursor))
    (Cursor.baseEvolution input current.cursor) (Cursor.baseOwner input current.cursor)
    start.account.generated current.cursor.account current.native (Cursor.action input current.cursor)

abbrev vocabulary : ConstructiveRoot.Vocabulary where
  Current := Current input start
  Anchor := (N input start).Anchor
  Incidence := (N input start).Incidence
  Lineage := (N input start).Lineage
  anchorAt := fun current => (N input start).anchorAt (supportAt input start current)
  incidenceAt := fun current => (N input start).incidenceAt (supportAt input start current)
  lineageAt := fun current => (N input start).lineageAt (supportAt input start current)
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next input start current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary input start

inductive NativeEventAt : (V input start).Current → (N input start).Support → Type
  | emitted (current : Current input start) : NativeEventAt current (supportAt input start current)

def sourceLaw : SourceNativeEventAlgebra (N input start) (V input start) where
  EventAt := NativeEventAt input start
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N input start) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

variable (startPositive : 0 < Cursor.physicalVisitIndex input start)

def source : SourceNativeSource (N input start) (V input start) where
  initial := initial input start startPositive
  law := sourceLaw input start

def emitted (current : Current input start) :
    (source input start startPositive).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt input start current, .emitted current⟩

theorem occurrence_eq_emitted {current : Current input start}
    (occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted input start startPositive current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem generated_next_is_original_native_action (current : Current input start) :
    (next input start current).cursor.account =
      (Cursor.action input current.cursor).next input current.cursor.account := rfl

theorem each_old_claim_stays_on_whole_account (current : Current input start)
    (entry : OpenResponsibilityAt (N input start) (supportAt input start current)) :
    ((wholeEvolution input start current).destination entry).1.claim = entry.claim :=
  ((wholeEvolution input start current).destination entry).2.toDebtLineage.claim_eq.symm

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource
