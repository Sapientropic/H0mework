import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Compiler.Inspection
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Execution.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Innovation

noncomputable section

-- Coface plumbing reads the compiler value; it must not run recipe search.
attribute [local irreducible] Adequacy.Compiler.compile Adequacy.Compiler.word

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)

def Payload : Type :=
  RawEvent Party Good Port Technology Instrument ×
  Option (Adequacy.Compiler.Plan claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
    frame.actualLaw frame.members) ×
  type_of% (Adequacy.Compiler.inspection claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
    frame.actualLaw frame.members)

def data : Payload claim frame :=
  (Adequacy.Compiler.word claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
    frame.actualLaw frame.members,
   Adequacy.Compiler.compile claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
    frame.actualLaw frame.members,
   Adequacy.Compiler.inspection claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
    frame.actualLaw frame.members)

private def dataComponent (original : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (Data : Type) (value : Data) :
    SourceNativeProjectionLaw original.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => Data
  project := fun _ {_} _ _ => value

def component := dataComponent claim frame (Payload claim frame) (data claim frame)

private def attach (original : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (face : SourceNativeProjectionLaw original.root.toAuthoritativeRoot.toLedgerRoot.source) :
    Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim where
  V := original.V
  root := original.root.withProjectionCoface face
  visit := original.visit
  row := original.row
  rowKey := original.rowKey
  authority := original.authority.withProjectionCoface face
  finite := original.finite
  occurrence_eq := original.occurrence_eq
  open_fibres := original.open_fibres
  basis := original.basis
  actualLaw := original.actualLaw
  members := original.members
  contextFace := { projection := .inherited original.contextFace.projection
                   active := original.contextFace.active
                   classifier_eq := original.contextFace.classifier_eq }
  context_heq := original.context_heq

def native := attach claim frame (component claim frame)

def face : SourceNativeRootSemanticFaceAt (native claim frame).root (native claim frame).visit :=
  { projection := .component PUnit.unit,active := PUnit.unit,classifier_eq := rfl }

def read : Payload claim frame := (face claim frame).rootRead

/-- Selection is read from this root's calculation face. A caller supplies
neither a successful endpoint nor a different word for the funded branch. -/
def word : RawEvent Party Good Port Technology Instrument :=
  (read claim frame).1

theorem read_eq : read claim frame = data claim frame := rfl

theorem word_eq : word claim frame = Adequacy.Compiler.word claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw frame.members :=
  congrArg Prod.fst (read_eq claim frame)

theorem support_eq : Abolition.Accounting.Root.Reentry.Frame.support claim (native claim frame) =
    Abolition.Accounting.Root.Reentry.Frame.support claim frame := rfl

theorem state_eq : Abolition.Accounting.Root.Reentry.Frame.state claim (native claim frame) =
    Abolition.Accounting.Root.Reentry.Frame.state claim frame := by
  have first := Option.some_get (Abolition.Accounting.Root.Reentry.Frame.active claim (native claim frame))
  have second := Option.some_get (Abolition.Accounting.Root.Reentry.Frame.active claim frame)
  exact Option.some.inj (first.trans ((congrArg Prod.snd (support_eq claim frame)).trans second.symm))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Execution.Source
