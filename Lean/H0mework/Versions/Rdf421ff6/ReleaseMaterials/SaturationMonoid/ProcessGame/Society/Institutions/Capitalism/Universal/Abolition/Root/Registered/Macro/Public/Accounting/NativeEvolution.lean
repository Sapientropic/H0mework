import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.SourceStep
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Evolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)

private def unchanged (atSupport : world.Support) :
    { evolution : LedgerWriteEvolutionAt world ⟨atSupport⟩ ⟨atSupport⟩ //
      Financial.Installation.KeepsKeys evolution } := by
  refine ⟨{ destination := fun entry => ⟨entry, .carried rfl HEq.rfl⟩
            origin := fun entry => ⟨entry, .carried rfl HEq.rfl⟩ }, ?_⟩
  exact ⟨fun _ => rfl, fun _ => rfl⟩

def nativeEvolutionWithKeys (current : Current input depth count anchor) :
    { evolution : LedgerWriteEvolutionAt world ⟨support input depth count family current⟩
        ⟨support input depth count family (nativeNext input depth count prefixLimit renewalLimit oldPast start current)⟩ //
      Financial.Installation.KeepsKeys evolution } := by
  by_cases paid : current.bodyPaid = true
  · rw [nativeNext, dif_pos paid]
    cases found : item? input depth count prefixLimit renewalLimit oldPast start current with
    | none => exact unchanged _
    | some item =>
        rcases current with ⟨progress⟩
        cases progress with
        | none => cases paid
        | some financial => exact ⟨family.itemEvolution financial.account financial.native item,
            family.item_keys financial.account financial.native item⟩
  · have same := the_unexecuted_body_is_the_original_initial_state current paid
    subst current
    exact unchanged family.currentSupport

def nativeEvolution (current : Current input depth count anchor) :
    LedgerWriteEvolutionAt world ⟨support input depth count family current⟩
      ⟨support input depth count family (nativeNext input depth count prefixLimit renewalLimit oldPast start current)⟩ :=
  (nativeEvolutionWithKeys input depth count prefixLimit renewalLimit oldPast start family current).val

#print axioms nativeEvolutionWithKeys
#print axioms nativeEvolution

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
