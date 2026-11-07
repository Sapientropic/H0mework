import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Account
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Renewal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Mechanism

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

abbrev Programme := Evolution.Mechanism.Programme claim

variable (frame : Current (oldN := oldN) claim)
  (programme : Programme claim) (input : Request Party Good Port Technology Instrument)

def Payload : Type := Programme claim × Request Party Good Port Technology Instrument

def component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => Payload claim
  project := fun _ {_} _ _ => (programme,input)

/-- Only source code and this one actual nature input are installed. No stream,
future state table, replacement row or supplied endpoint is carried here. -/
def native : Current (oldN := oldN) claim where
  V := frame.V
  root := frame.root.withProjectionCoface (component claim frame programme input)
  visit := frame.visit
  row := frame.row
  rowKey := frame.rowKey
  authority := frame.authority.withProjectionCoface (component claim frame programme input)
  basis := frame.basis
  actualLaw := frame.actualLaw
  members := frame.members
  contextFace := { projection := .inherited frame.contextFace.projection
                   active := frame.contextFace.active
                   classifier_eq := frame.contextFace.classifier_eq }
  context_heq := frame.context_heq

def face : SourceNativeRootSemanticFaceAt (native claim frame programme input).root (native claim frame programme input).visit where
  projection := .component PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def read : Payload claim := (face claim frame programme input).rootRead

theorem read_eq : read claim frame programme input = (programme,input) := rfl

theorem source_state_is_the_same_original_row :
    Current.state claim (native claim frame programme input) = Current.state claim frame := by
  have current := Option.some_get (Current.active claim (native claim frame programme input))
  have old := Option.some_get (Current.active claim frame)
  exact Option.some.inj (current.trans old.symm)

/-- A newly emitted protocol is interpreted at the actual original physical
cursor and law. Its own old initial field cannot refill stock, claims or time. -/
def currentMechanism : Trials.Mechanism Party Good Port Technology Instrument :=
  let selected := (read claim frame programme input).1.choose
    (Current.state claim (native claim frame programme input))
  { selected with code := { selected.code with
      law := (native claim frame programme input).actualLaw
      initial := (Current.state claim (native claim frame programme input)).raw } }

def word : RawEvent Party Good Port Technology Instrument :=
  (currentMechanism claim frame programme input).word (read claim frame programme input).2

theorem mechanism_is_chosen_before_the_nature_input :
    HEq (currentMechanism claim frame programme input).policy
      (programme.choose (Current.state claim frame)).policy := by
  unfold currentMechanism
  rw [read_eq,source_state_is_the_same_original_row]
  exact HEq.rfl

theorem the_emitted_mechanism_uses_the_actual_original_current :
    (currentMechanism claim frame programme input).code.initial = (Current.state claim frame).raw ∧
      (currentMechanism claim frame programme input).code.law = frame.actualLaw := by
  constructor
  · exact congrArg Responsibility.Family.State.raw (source_state_is_the_same_original_row claim frame programme input)
  · rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Mechanism
