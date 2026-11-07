import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Ingress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)

local notation "N" => ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)

/-- Only an existing source context is supplied. Its physical state is read from
its native active row; no proposed successor or target coverage is accepted. -/
structure Frame where
  V : ConstructiveRoot.Vocabulary
  root : SourceNativeLivingRootClosure N V
  visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot
  row : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted visit.current))
  rowKey : row.1 = .inr (Responsibility.Family.activationLaw claim).debtId
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit row
  finite : Finite (OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted visit.current)))
  occurrence_eq : ∀ current (occurrence : root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current),
    occurrence = root.emitted current
  open_fibres : ∀ support responsibility, Subsingleton ((N).OpenAt support responsibility)
  basis : Abolition.Root.Registered.Macro.Inquiry.Basis N
  actualLaw : RawLaw Party Good Port Technology Instrument
  members : List Party
  contextFace : SourceNativeRootSemanticFaceAt root visit
  context_heq : HEq contextFace.rootRead (actualLaw,members)

private theorem debt_is_active {network : WorldRelationNetwork} {law : DebtActivationLaw}
    (support : network.Support × Option law.DebtState)
    (opened : DebtOpenAt network law support (.inr law.debtId)) : support.2.isSome = true := by
  rcases support with ⟨old,state⟩
  cases state with
  | none => exact nomatch opened
  | some state => rfl

namespace Frame
variable (frame : Frame (oldN := oldN) claim)

def support : (N).Support :=
  frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    (frame.root.emitted frame.visit.current)

theorem active : (support claim frame).2.isSome = true := by
  have opened := frame.row.2
  rw [frame.rowKey] at opened
  exact debt_is_active (support claim frame) opened

def state : Responsibility.Family.State claim := (support claim frame).2.get (active claim frame)

theorem support_eq : support claim frame = ((support claim frame).1,some (state claim frame)) := by
  exact @Prod.ext oldN.Support (Option (Responsibility.Family.State claim))
    (support claim frame) ((support claim frame).1,some (state claim frame)) rfl
    (Option.some_get (active claim frame)).symm

def updated (word : RawEvent Party Good Port Technology Instrument) : Responsibility.Family.State claim :=
  Responsibility.Family.State.advance claim (state claim frame) frame.actualLaw word

end Frame

def contextComponent [DecidableEq Port]
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (frame : Financial.Installation.NativeFrame input)
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (word : RawEvent Party Good Port Technology Instrument) :
    SourceNativeProjectionLaw (Source.Inquiry.root input frame visit claim word).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => RawLaw Party Good Port Technology Instrument × List Party
  project := fun _ {_} _ _ => (Source.actualLaw input,
    (Financial.Installation.observe input (frame.cursor visit.current)).members)

def contextRoot [DecidableEq Port]
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (frame : Financial.Installation.NativeFrame input)
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (word : RawEvent Party Good Port Technology Instrument) :=
  (Source.Inquiry.root input frame visit claim word).withProjectionCoface (contextComponent claim input frame visit word)

/-- Entry from the already installed same original control-liability root. -/
def ofSource [DecidableEq Port] (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (frame : Financial.Installation.NativeFrame input)
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (word : RawEvent Party Good Port Technology Instrument) (n : Nat) :
    Frame (oldN := frame.N) claim where
  V := Source.V input frame visit claim word
  root := contextRoot claim input frame visit word
  visit := Source.Inquiry.temporalAt input frame visit claim word n
  row := Source.Inquiry.entry input frame claim
    (Source.support input frame visit claim word (Source.Inquiry.visitAt input frame visit claim word n).current)
  rowKey := rfl
  authority := (Source.Inquiry.authorityAt input frame visit claim word n).withProjectionCoface
    (contextComponent claim input frame visit word)
  finite := Source.entries_finite input frame visit claim word _
  occurrence_eq := fun _ occurrence => Compiler.occurrence_eq_emitted (Source.flow input frame visit claim word) occurrence
  open_fibres := Source.open_fibres input frame claim
  basis := Source.Inquiry.basis input frame claim
  actualLaw := Source.actualLaw input
  members := (Financial.Installation.observe input (frame.cursor visit.current)).members
  contextFace := { projection := .component PUnit.unit, active := PUnit.unit, classifier_eq := rfl }
  context_heq := HEq.rfl

theorem ofSource_state [DecidableEq Port]
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (frame : Financial.Installation.NativeFrame input)
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (word : RawEvent Party Good Port Technology Instrument) (n : Nat) :
    Frame.state claim (ofSource claim input frame visit word n) =
      Source.debtState input frame visit claim word (Source.Inquiry.visitAt input frame visit claim word n).current := rfl

theorem ofSource_observed [DecidableEq Port]
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (frame : Financial.Installation.NativeFrame input)
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (word : RawEvent Party Good Port Technology Instrument) :
    Frame.state claim (ofSource claim input frame visit word 1) = Source.observed input frame visit claim word := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry
