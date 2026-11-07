import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Cursor
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Visits

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Material.shared seed claim))

local notation "F" => Runtime.flow seed claim
local notation "R" => Runtime.Inquiry.root seed claim

def entry (current : FinancialCurrent seed) := (family seed claim enough).entry (Runtime.support seed claim current)

theorem the_original_base_key_is_the_same_in_every_current (left right : FinancialCurrent seed) :
    (entry seed claim enough left).1 = (entry seed claim enough right).1 :=
  (family seed claim enough).entry_key _ _

theorem the_actual_native_next_carries_this_same_original_base_entry (current : FinancialCurrent seed) :
    (R).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
      (Abolition.Accounting.Root.Compiler.nextEq F current) (entry seed claim enough current) =
        entry seed claim enough (Runtime.next seed claim current) := by
  apply Financial.Installation.entry_eq_of_key
  · exact (Abolition.Accounting.Root.Compiler.canonical_key_of_flow F current _ _
      ((Runtime.every_original_key_survives_the_joint_actual_write seed claim current).1 _)).trans
        (the_original_base_key_is_the_same_in_every_current seed claim enough _ _)
  · exact Admission.fibres seed claim _

def initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt R
    (Abolition.Accounting.Root.Compiler.initialVisit F) (entry seed claim enough (Runtime.initial seed)) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow R _
    (Abolition.Accounting.Root.Compiler.generatedRow F (Abolition.Accounting.Root.Compiler.initialVisit F) _)

def nextAuthorityAt (visit : SourceNativeTemporalVisitAt (R).toAuthoritativeRoot.toLedgerRoot)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt R visit (entry seed claim enough visit.current)) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt R
      (visit.next (Abolition.Accounting.Root.Compiler.nextEq F visit.current))
      (entry seed claim enough (Runtime.next seed claim visit.current)) :=
  the_actual_native_next_carries_this_same_original_base_entry seed claim enough visit.current ▸
    authority.next (Abolition.Accounting.Root.Compiler.nextEq F visit.current)

def authorityAt : (n : Nat) → SourceNativeLivingTemporalCausalEntryAuthorityAt R (Runtime.temporalAt seed claim n)
    (entry seed claim enough (Runtime.visitAt seed claim n).current)
  | 0 => nextAuthorityAt seed claim enough (Abolition.Accounting.Root.Compiler.initialVisit F)
      (initialAuthority seed claim enough)
  | n + 1 => nextAuthorityAt seed claim enough (Runtime.temporalAt seed claim n) (authorityAt n)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
