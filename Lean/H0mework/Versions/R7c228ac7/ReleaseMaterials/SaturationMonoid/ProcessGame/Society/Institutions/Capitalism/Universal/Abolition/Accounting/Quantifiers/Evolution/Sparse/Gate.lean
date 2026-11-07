import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Input

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Gate

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

def evaluation := Priority.Policy.evaluate claim (Current.state claim (Input.native claim current word))
  (Current.readLaw claim (Input.native claim current word)) (Current.readMembers claim (Input.native claim current word))
  (Input.readWord claim current word)

def renewal := Priority.Selection.renewalVerdict claim (Current.state claim (Input.native claim current word))
  (Current.readLaw claim (Input.native claim current word)) (Current.readMembers claim (Input.native claim current word))
  (Input.readWord claim current word)

inductive Projection
  | evaluation | renewal

def component : SourceNativeProjectionLaw (Input.native claim current word).root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} _ _ => match projection with
    | .evaluation => type_of% (evaluation claim current word)
    | .renewal => type_of% (renewal claim current word)
  project := fun projection {_} _ _ => match projection with
    | .evaluation => evaluation claim current word
    | .renewal => renewal claim current word

def native : Current (oldN := oldN) claim where
  V := current.V
  root := (Input.native claim current word).root.withProjectionCoface (component claim current word)
  visit := current.visit
  row := current.row
  rowKey := current.rowKey
  authority := (Input.native claim current word).authority.withProjectionCoface (component claim current word)
  basis := current.basis
  actualLaw := current.actualLaw
  members := current.members
  contextFace := { projection := .inherited (Input.native claim current word).contextFace.projection
                   active := (Input.native claim current word).contextFace.active
                   classifier_eq := (Input.native claim current word).contextFace.classifier_eq }
  context_heq := (Input.native claim current word).context_heq

def evaluationFace : SourceNativeRootSemanticFaceAt (native claim current word).root current.visit :=
  { projection := .component Projection.evaluation,active := PUnit.unit,classifier_eq := rfl }

def renewalFace : SourceNativeRootSemanticFaceAt (native claim current word).root current.visit :=
  { projection := .component Projection.renewal,active := PUnit.unit,classifier_eq := rfl }

def readEvaluation := (evaluationFace claim current word).rootRead

def readRenewal := (renewalFace claim current word).rootRead

def executableWord := (readEvaluation claim current word).executableWord

theorem state_eq : Current.state claim (native claim current word) = Current.state claim current := rfl

theorem executableWord_eq : executableWord claim current word =
    (Priority.Policy.evaluate claim (Current.state claim current) current.actualLaw current.members word).executableWord := by
  change (evaluation claim current word).executableWord = _
  unfold evaluation
  rw [Input.state_eq,Current.readLaw_eq,Current.readMembers_eq,Input.readWord_eq]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Gate
