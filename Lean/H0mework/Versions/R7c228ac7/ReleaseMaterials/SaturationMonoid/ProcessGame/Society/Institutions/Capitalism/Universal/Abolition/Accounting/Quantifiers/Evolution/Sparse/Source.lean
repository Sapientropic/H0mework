import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Reply
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.TemporalMemory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

inductive Projection
  | reply | compilation | history

def component : SourceNativeProjectionLaw (Gate.native claim current word).root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .reply => Reply claim current word
    | .history => TemporalMemory.View current.root.toAuthoritativeRoot.toLedgerRoot
    | .compilation => SourceNativeInquiryCompilationTokenAt
      (U7 := current.basis.U7) (calculus := current.basis.calculus)
      (oldTheory := current.root.toAuthoritativeRoot.source.lawSurface)
      current.row PUnit.unit (ULift.up.{1,0} occurrence) .answered (Reply claim current word)
  project := fun projection {_} _ _ => match projection with
    | .reply => Sparse.reply claim current word
    | .history => TemporalMemory.read current.root.toAuthoritativeRoot.toLedgerRoot current.visit
    | .compilation => .canonical (Sparse.reply claim current word)

def native : Current (oldN := oldN) claim where
  V := current.V
  root := (Gate.native claim current word).root.withProjectionCoface (component claim current word)
  visit := current.visit
  row := current.row
  rowKey := current.rowKey
  authority := (Gate.native claim current word).authority.withProjectionCoface (component claim current word)
  basis := current.basis
  actualLaw := current.actualLaw
  members := current.members
  contextFace := { projection := .inherited (Gate.native claim current word).contextFace.projection
                   active := (Gate.native claim current word).contextFace.active
                   classifier_eq := (Gate.native claim current word).contextFace.classifier_eq }
  context_heq := (Gate.native claim current word).context_heq

def replyFace : SourceNativeRootSemanticFaceAt (native claim current word).root current.visit :=
  { projection := .component Projection.reply,active := PUnit.unit,classifier_eq := rfl }

def readReply : Reply claim current word := (replyFace claim current word).rootRead

theorem readReply_eq : readReply claim current word = Sparse.reply claim current word := rfl

def historyFace : SourceNativeRootSemanticFaceAt (native claim current word).root current.visit :=
  { projection := .component Projection.history,active := PUnit.unit,classifier_eq := rfl }

def readHistory := (historyFace claim current word).rootRead

theorem readHistory_eq : readHistory claim current word =
    TemporalMemory.read current.root.toAuthoritativeRoot.toLedgerRoot current.visit := rfl

theorem state_eq : Current.state claim (native claim current word) = Current.state claim current := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Source
