import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Step
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Family

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

def support (current : Current input depth count anchor) : world.Support := family.support current.account current.native

def owner (current : Current input depth count anchor) : OpenResponsibilityAt world (support input depth count family current) :=
  family.owner current.account current.native

private def stationary (base : WorldRelationNetwork) (atSupport : base.Support) :
    LedgerWriteEvolutionAt base ⟨atSupport⟩ ⟨atSupport⟩ where
  destination := fun entry => ⟨entry, .carried rfl HEq.rfl⟩
  origin := fun entry => ⟨entry, .carried rfl HEq.rfl⟩

private def stationaryWithKeys (base : WorldRelationNetwork) (atSupport : base.Support) :
    { evolution : LedgerWriteEvolutionAt base ⟨atSupport⟩ ⟨atSupport⟩ //
      Financial.Installation.KeepsKeys evolution } := by
  refine ⟨stationary base atSupport, ?_⟩
  exact ⟨fun _ => rfl, fun _ => rfl⟩

def evolutionWithKeys (current : Current input depth count anchor) :
    { evolution : LedgerWriteEvolutionAt world ⟨support input depth count family current⟩
        ⟨support input depth count family (next input depth count prefixLimit renewalLimit oldPast start current)⟩ //
      Financial.Installation.KeepsKeys evolution } := by
  by_cases paid : current.bodyPaid = true
  · rw [next, dif_pos paid]
    cases found : item? input depth count prefixLimit renewalLimit oldPast start current with
    | none => exact stationaryWithKeys world _
    | some item =>
        dsimp only
        cases issued : Epoch.Finance.readNewClaim input depth count item with
        | some claim => exact stationaryWithKeys world _
        | none =>
            rcases current with ⟨progress⟩
            cases progress with
            | none => cases paid
            | some financial => exact ⟨family.itemEvolution financial.account financial.native item,
                family.item_keys financial.account financial.native item⟩
  · have same := the_unexecuted_body_is_the_original_initial_state current paid
    subst current
    exact stationaryWithKeys world family.currentSupport

def wholeEvolution (current : Current input depth count anchor) :
    LedgerWriteEvolutionAt world ⟨support input depth count family current⟩
      ⟨support input depth count family (next input depth count prefixLimit renewalLimit oldPast start current)⟩ :=
  (evolutionWithKeys input depth count prefixLimit renewalLimit oldPast start family current).val

#print axioms support
#print axioms wholeEvolution

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
