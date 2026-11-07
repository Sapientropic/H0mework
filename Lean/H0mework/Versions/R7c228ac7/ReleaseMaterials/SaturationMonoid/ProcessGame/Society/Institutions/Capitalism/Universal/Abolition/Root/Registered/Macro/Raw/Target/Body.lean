import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData.Reentry
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Macro.Data

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (data : Continuation.FinancialData frame) (reader : Reader input depth count)
  {current : frame.V.Current} (germ : GermAt frame data reader current)

abbrev family := (data.familyAt current germ.ready).val
abbrev seedEq := next_seed_is_generated_by_the_original_history frame data reader germ

def bareFrame := { Reentry.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
  germ.snapshot germ.raw (family frame data reader germ) (seedEq frame data reader germ) with
  nativeOrigin := frame.nativeOrigin }

def financialData : Continuation.FinancialData (bareFrame frame data reader germ) :=
  ReviewSource.Native.Macro.inheritCreator
    (Continuation.FinancialData.reentry (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      germ.snapshot germ.raw (family frame data reader germ) (seedEq frame data reader germ)) frame.nativeOrigin

def basis : Inquiry.Basis frame.N := Reentry.basis input depth count (family frame data reader germ)

abbrev bodyInitial := Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
  germ.snapshot germ.raw 0
abbrev bodyNext := Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
  germ.snapshot germ.raw 0 (bodyInitial frame data reader germ)

theorem initial_world_is_literal : (bareFrame frame data reader germ).N = frame.N := rfl

theorem initial_support_is_the_original_current :
    (bareFrame frame data reader germ).sourceSupport (bodyInitial frame data reader germ) =
      frame.sourceSupport current :=
  (Reentry.initial_support_is_the_same_current_world (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    germ.snapshot germ.raw (family frame data reader germ) (seedEq frame data reader germ)).trans
    (data.familyAt current germ.ready).property

theorem first_body_retains_the_complete_original_account :
    (bodyNext frame data reader germ).account = frame.account current :=
  seedEq frame data reader germ

theorem first_body_releases_the_same_actual_inventory :
    (bodyNext frame data reader germ).position = 0 ∧
      Accounting.pending (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
        germ.snapshot germ.raw 0 (bodyNext frame data reader germ) =
        Inventory.items (review := review) input depth count prefixLimit renewalLimit germ.snapshot germ.raw := ⟨rfl, rfl⟩

theorem first_body_executes_the_original_selected_physical_source :
    Accounting.physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
        germ.snapshot germ.raw 0 (bodyNext frame data reader germ) =
      Physical.stateAt input depth count prefixLimit renewalLimit
        (Physical.next (Mandatory.executionCursor (review := review) input depth count prefixLimit renewalLimit germ.snapshot germ.raw)).past := rfl

theorem first_body_generates_ready :
    (financialData frame data reader germ).Ready
      ((bareFrame frame data reader germ).next (bodyInitial frame data reader germ)) :=
  Continuation.FinancialData.reentry_body_generates_the_same_financial_dictionary (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    germ.snapshot germ.raw (family frame data reader germ) (seedEq frame data reader germ)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.initial_support_is_the_original_current
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.first_body_retains_the_complete_original_account
