import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (origin : Source.OriginAt input frame visit claim)
  (word : RawEvent Party Good Port Technology Instrument)
  (originalAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (Source.sourceEntry input frame visit))

def basis : Abolition.Root.Registered.Macro.Inquiry.Basis frame.N where
  entry := frame.entrySupport
  disposition := frame.disposition

inductive Projection
  | compilation | input

def component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .input => RawEvent Party Good Port Technology Instrument
    | .compilation => SourceNativeInquiryCompilationTokenAt
        (U7 := (basis input frame).U7) (calculus := (basis input frame).calculus)
        (oldTheory := frame.root.toAuthoritativeRoot.source.lawSurface)
        (frame.entrySupport occurrence.1) PUnit.unit (ULift.up.{1,0} occurrence) .answered
        (Responsibility.Family.State claim)
  project := fun projection {_} _ _ => match projection with
    | .input => word
    | .compilation => .canonical (Source.declared input frame visit claim)

/-- A source coface preserves the actual native programme and every prior
projection. Its compulsory branch is selected by the inquiry compiler below. -/
def native : Financial.Installation.NativeFrame input where
  N := frame.N
  V := frame.V
  root := frame.root.withProjectionCoface (component input frame visit claim word)
  program := frame.program
  cursor := frame.cursor
  next_exact := frame.next_exact
  projection := .inherited frame.projection
  active := frame.active
  classify_eq := frame.classify_eq
  observation_heq := frame.observation_heq
  entrySupport := frame.entrySupport
  disposition := frame.disposition
  openAt_subsingleton := frame.openAt_subsingleton
  origin_injective := frame.origin_injective
  destination_injective := frame.destination_injective

def authority := originalAuthority.withProjectionCoface (component input frame visit claim word)

include origin in
theorem installedOrigin : Source.OriginAt input (native input frame visit claim word) visit claim where
  law := origin.law
  before := origin.before
  word := origin.word
  history := origin.history
  accounted := origin.accounted

def inputFace : SourceNativeRootSemanticFaceAt (native input frame visit claim word).root visit where
  projection := .component .input
  active := PUnit.unit
  classifier_eq := rfl

def sourceWord : RawEvent Party Good Port Technology Instrument :=
  (inputFace input frame visit claim word).rootRead

theorem sourceWord_eq : sourceWord input frame visit claim word = word := rfl

def generated := Action.generated input (native input frame visit claim word) visit claim
  (installedOrigin input frame visit claim origin word) (sourceWord input frame visit claim word)
  (authority input frame visit claim word originalAuthority)

def program : SourceNativeInquiryCompilationProgramAt (native input frame visit claim word).root visit
    (basis input frame).U7 (basis input frame).calculus
    (native input frame visit claim word).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1,0} ((native input frame visit claim word).root.emitted visit.current))
    (Source.sourceEntry input (native input frame visit claim word) visit)
    (authority input frame visit claim word originalAuthority) where
  compile := fun _ => .debtAdmission (generated input frame visit claim origin word originalAuthority)

def state : RootInquiryStateAt frame.N frame.V where
  root := (native input frame visit claim word).root
  visit := visit
  U7 := (basis input frame).U7
  calculus := (basis input frame).calculus
  Query := PUnit
  entryAt := fun _ => Source.sourceEntry input (native input frame visit claim word) visit
  authorityAt := fun _ => authority input frame visit claim word originalAuthority
  compilationProgramAt := fun query => by
    cases query
    exact program input frame visit claim origin word originalAuthority
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component .compilation
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation :=
  ⟨_,_,RootInquiryEngineStateAt.create (state input frame visit claim origin word originalAuthority)⟩

theorem the_original_root_compiler_selects_the_compulsory_actual_admission :
    (state input frame visit claim origin word originalAuthority).compileInquiry PUnit.unit =
      .debtAdmission (generated input frame visit claim origin word originalAuthority) := rfl

#print axioms native
#print axioms state
#print axioms the_original_root_compiler_selects_the_compulsory_actual_admission

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Installation
