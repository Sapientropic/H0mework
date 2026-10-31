import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Validity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Countermodels.Nonattainment
noncomputable section

def reader (n : Nat) : Macro.Raw.Reader input 0 0 := fun cursor _ =>
  ((programme n)[cursor.past.length - initialHistory.length]?).getD .advance

def initial (n : Nat) : Position input := Position.initial family (firstStart n) (reader n)

theorem the_actual_initial_cut_is_the_original_account (n : Nat) :
    (initial n).actual.actual.account = Native.originalAccount := rfl

theorem the_source_first_body_has_work (n : Nat) :
    Public.Inquiry.HasWork (initial n).frame (initial n).actual.actual := Or.inl rfl

theorem the_source_first_body_does_not_reissue_a_claim (n : Nat) :
    Public.Accounting.registration? input 0 0 0 0 [] (initial n).start (initial n).actual.actual = none := rfl

theorem the_first_body_is_actually_resolved_by_the_root (n : Nat) :
    (initial n).native.inquiry.erase = (RootInquiryProcessNode.answered (initial n).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (initial n).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (initial n).native.inquiry) :=
  Position.native_is_the_actual_root_resolution _ (the_source_first_body_has_work n)
    (the_source_first_body_does_not_reissue_a_claim n)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
