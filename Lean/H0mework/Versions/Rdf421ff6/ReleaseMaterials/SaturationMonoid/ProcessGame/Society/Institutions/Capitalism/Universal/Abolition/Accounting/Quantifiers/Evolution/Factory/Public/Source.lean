import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Law

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

abbrev Answer := RawLaw Party Good Port Technology Instrument × List Party

def answer : Answer (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  (law current,Context.readMembers current)

inductive Projection
  | preparation | compilation

def component : SourceNativeProjectionLaw current.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .preparation => Answer (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
    | .compilation => SourceNativeInquiryCompilationTokenAt
      (U7 := current.basis.U7) (calculus := current.basis.calculus)
      (oldTheory := current.root.toAuthoritativeRoot.source.lawSurface)
      current.row PUnit.unit (ULift.up.{1,0} occurrence) .answered
        (Answer (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  project := fun projection {_} _ _ => match projection with
    | .preparation => answer current
    | .compilation => .canonical (answer current)

def native : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N where
  V := current.V
  root := current.root.withProjectionCoface (component current)
  visit := current.visit
  row := current.row
  authority := current.authority.withProjectionCoface (component current)
  basis := current.basis
  raw := current.raw
  rawFace := { projection := .inherited current.rawFace.projection
               active := current.rawFace.active,classifier_eq := current.rawFace.classifier_eq }
  raw_heq := current.raw_heq
  actualLaw := current.actualLaw
  members := current.members
  contextFace := { projection := .inherited current.contextFace.projection
                   active := current.contextFace.active,classifier_eq := current.contextFace.classifier_eq }
  context_heq := current.context_heq

def preparationFace : SourceNativeRootSemanticFaceAt (native current).root current.visit :=
  { projection := .component Projection.preparation,active := PUnit.unit,classifier_eq := rfl }

def readAnswer := (preparationFace current).rootRead

theorem readAnswer_eq : readAnswer current = answer current := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Source
