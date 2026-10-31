import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Initial

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Countermodels.Nonattainment
noncomputable section

theorem the_native_source_keeps_the_same_reader (current : Position input) :
    current.native.reader = current.reader := rfl

theorem the_raw_source_keeps_the_same_reader (current : Position input)
    (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    (current.raw complete).reader = current.reader := rfl

theorem the_actual_proposal_is_read_from_the_same_source_code
    (current : Position input) (n : Nat) (same : current.reader = reader n) :
    current.actual.proposal current.reader = reader n current.actual.readerCursor current.actual.actual.account :=
  congrArg (fun code : Macro.Raw.Reader input 0 0 => code current.actual.readerCursor current.actual.actual.account) same

theorem the_source_reader_selects_its_exact_word_index
    (n index : Nat) (cursor : Physical.Cursor Bool Bool Unit Nat Unit)
    (account : (Epoch.Finance.process input 0 0).GeneratedState)
    (same : cursor.past.length - initialHistory.length = index) :
    reader n cursor account = ((programme n)[index]?).getD .advance := by
  unfold reader
  rw [same]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
