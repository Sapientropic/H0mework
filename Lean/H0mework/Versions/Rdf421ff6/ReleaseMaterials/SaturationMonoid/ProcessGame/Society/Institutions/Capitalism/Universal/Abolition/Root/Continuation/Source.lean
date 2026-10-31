import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation.World
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Budget

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.Runtime.Frame input)
  (request : Request Party Good Port Technology Instrument)

abbrev Data := RawCurrent Party Good Technology Instrument
abbrev N := world frame.native.N (Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument))

def oldSupport := frame.native.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
  (frame.native.root.emitted frame.visit.current)

def initial : Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument) :=
  Financial.Installation.Runtime.physical input frame

def next (current : Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)) :=
  input.law.step current request

def supportAt (current : Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)) :
    (N input frame).Support := (oldSupport input frame, current)

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)
  Anchor := frame.native.N.Anchor
  Incidence := frame.native.N.Incidence
  Lineage := frame.native.N.Lineage
  anchorAt := fun _ => frame.native.N.anchorAt (oldSupport input frame)
  incidenceAt := fun _ => frame.native.N.incidenceAt (oldSupport input frame)
  lineageAt := fun _ => frame.native.N.lineageAt (oldSupport input frame)
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next input request current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : (V input frame request).Current → (N input frame).Support → Type
  | emitted (current) : EventAt current (supportAt input frame current)

def sourceLaw : SourceNativeEventAlgebra (N input frame) (V input frame request) where
  EventAt := EventAt input frame request
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N input frame) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource (N input frame) (V input frame request) where
  initial := initial input frame
  law := sourceLaw input frame request

def emitted (current : (V input frame request).Current) :
    (source input frame request).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt input frame current, .emitted current⟩

theorem occurrence_eq_emitted {current : (V input frame request).Current}
    (occurrence : (source input frame request).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted input frame request current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

def originalCursor (_current : (V input frame request).Current) := frame.cursor input

theorem initial_preserves_the_original_account_and_pending :
    (originalCursor input frame request (initial input frame)).account = (frame.cursor input).account ∧
      Financial.Installation.Cursor.pending input (originalCursor input frame request (initial input frame)) =
        Financial.Installation.Cursor.pending input (frame.cursor input) := ⟨rfl, rfl⟩

theorem fee_first_write_is_material
    (fee : Review.FeeScope request)
    (paid : Review.PaymentAt input.law request (initial input frame)) :
    (next input request (initial input frame)).stock fee.payer fee.good + fee.amount =
        (initial input frame).stock fee.payer fee.good ∧
      (next input request (initial input frame)).claims = (initial input frame).claims ∧
      (next input request (initial input frame)).clock = (initial input frame).clock ∧
      (next input request (initial input frame)).round = (initial input frame).round := by
  refine ⟨paid.stock_balance fee, paid.original_claims_unchanged fee, ?_, ?_⟩ <;>
    simp only [next, RawLaw.step, if_pos paid.accepted, RawLaw.paidStep]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation
