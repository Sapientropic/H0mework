import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Input

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
  | input | context

def component : SourceNativeProjectionLaw current.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} _ _ => match projection with
    | .input => RawEvent Party Good Port Technology Instrument
    | .context => RawLaw Party Good Port Technology Instrument × List Party
  project := fun projection {_} _ _ => match projection with
    | .input => word
    | .context => Current.readContext claim current

def native : Current (oldN := oldN) claim where
  V := current.V
  root := current.root.withProjectionCoface (component claim current word)
  visit := current.visit
  row := current.row
  rowKey := current.rowKey
  authority := current.authority.withProjectionCoface (component claim current word)
  basis := current.basis
  actualLaw := current.actualLaw
  members := current.members
  contextFace := { projection := .component Projection.context,active := PUnit.unit,classifier_eq := rfl }
  context_heq := heq_of_eq (Current.readContext_eq claim current)

def inputFace : SourceNativeRootSemanticFaceAt (native claim current word).root current.visit :=
  { projection := .component Projection.input,active := PUnit.unit,classifier_eq := rfl }

def readWord : RawEvent Party Good Port Technology Instrument := (inputFace claim current word).rootRead

theorem readWord_eq : readWord claim current word = word := rfl

theorem state_eq : Current.state claim (native claim current word) = Current.state claim current := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Input
