import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Living
import H0mework.Foundation.Responsibility.JointSource.Native.Image

/-! This adapter reads the installed original observation and the original
native compiler image.  The child admission source reuses these actual
images; it receives no replacement ledger, body result or target current. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

structure NativeFrame where
  N : WorldRelationNetwork
  V : ConstructiveRoot.Vocabulary
  root : SourceNativeLivingRootClosure N V
  program : RootGeneratedDebtActivationJointSource.Native.Program root.toAuthoritativeRoot.toLedgerRoot
  cursor : V.Current → Cursor.State input
  next_exact : ∀ current,
    cursor (V.nativeTarget (program.emit current).write) = Cursor.next input (cursor current)
  projection : root.toAuthoritativeRoot.source.projectionLaw.Projection
  active : ∀ current, root.toAuthoritativeRoot.source.projectionLaw.ActiveAt projection (root.emitted current)
  classify_eq : ∀ current,
    root.toAuthoritativeRoot.source.projectionLaw.classify projection (root.emitted current) = .inl (active current)
  observation_heq : ∀ current, HEq
    (root.toAuthoritativeRoot.source.projectionLaw.project projection (root.emitted current) (active current))
    (observe input (cursor current))
  entrySupport : ∀ support, OpenResponsibilityAt N support
  disposition : ∀ support kind, N.DispositionAt support kind
  openAt_subsingleton : ∀ support responsibility, Subsingleton (N.OpenAt support responsibility)
  origin_injective : ∀ current, Function.Injective (fun entry => ((program.emit current).evolution.origin entry).1)
  destination_injective : ∀ current, Function.Injective (fun entry => ((program.emit current).evolution.destination entry).1)

namespace AccountSource

variable (start : Cursor.State input) (startPositive : 0 < Cursor.physicalVisitIndex input start)

noncomputable def nativeProgram : RootGeneratedDebtActivationJointSource.Native.Program
    (livingRoot input start startPositive).toAuthoritativeRoot.toLedgerRoot where
  emit := fun current =>
    (RootGeneratedDebtActivationJointSource.Native.read?
      (livingRoot input start startPositive).toAuthoritativeRoot.toLedgerRoot current).get (by rfl)

noncomputable def nativeFrame : NativeFrame input where
  N := N input start
  V := V input start
  root := livingRoot input start startPositive
  program := nativeProgram input start startPositive
  cursor := Current.cursor
  next_exact := fun _ => rfl
  projection := .observation
  active := fun _ => ()
  classify_eq := fun _ => rfl
  observation_heq := fun _ => HEq.rfl
  entrySupport := canonicalEntry input start.account.generated
  disposition := canonicalDisposition input start.account.generated
  openAt_subsingleton := world_openAt_subsingleton input start.account.generated
  origin_injective := by
    intro current
    change Function.Injective (fun entry =>
      ((patch input start startPositive current).toLedgerWriteEvolution.origin entry).1)
    rw [patch_origin]
    exact whole_origin_injective input start current
  destination_injective := by
    intro current
    change Function.Injective (fun entry =>
      ((patch input start startPositive current).toLedgerWriteEvolution.destination entry).1)
    rw [patch_destination]
    exact whole_destination_injective input start current

end AccountSource

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
