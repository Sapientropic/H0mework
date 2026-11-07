import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Context

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

local notation "F" => flow seed claim
local notation "R" => Inquiry.root seed claim

theorem canonical_debt_entry (actual : FinancialCurrent seed) :
    (R).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (Abolition.Accounting.Root.Compiler.nextEq F actual)
      (Inquiry.entry seed claim (support seed claim actual)) =
        Inquiry.entry seed claim (support seed claim (next seed claim actual)) := by
  apply Financial.Installation.entry_eq_of_key
  · exact Abolition.Accounting.Root.Compiler.canonical_key_of_flow F actual _ _
      ((every_original_key_survives_the_joint_actual_write seed claim actual).1 _)
  · exact Admission.fibres seed claim _

def initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt R
    (Abolition.Accounting.Root.Compiler.initialVisit F) (Inquiry.entry seed claim (support seed claim (initial seed))) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow R _
    (Abolition.Accounting.Root.Compiler.generatedRow F (Abolition.Accounting.Root.Compiler.initialVisit F) _)

def nextAuthorityAt
    (visit : SourceNativeTemporalVisitAt (R).toAuthoritativeRoot.toLedgerRoot)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt R visit
      (Inquiry.entry seed claim (support seed claim visit.current))) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt R (visit.next (Abolition.Accounting.Root.Compiler.nextEq F visit.current))
      (Inquiry.entry seed claim (support seed claim (next seed claim visit.current))) :=
  canonical_debt_entry seed claim visit.current ▸ authority.next (Abolition.Accounting.Root.Compiler.nextEq F visit.current)

def visitAt : Nat → RootVisit (R).toAuthoritativeRoot.toRoot
  | 0 => (R).toAuthoritativeRoot.toRoot.initialVisit.next (Abolition.Accounting.Root.Compiler.nextEq F (initial seed))
  | n + 1 => (visitAt n).next (Abolition.Accounting.Root.Compiler.nextEq F (visitAt n).current)

def temporalAt (n : Nat) : SourceNativeTemporalVisitAt (R).toAuthoritativeRoot.toLedgerRoot := .finite (visitAt seed claim n)

def authorityAt : (n : Nat) → SourceNativeLivingTemporalCausalEntryAuthorityAt R (temporalAt seed claim n)
    (Inquiry.entry seed claim (support seed claim (visitAt seed claim n).current))
  | 0 => nextAuthorityAt seed claim (Abolition.Accounting.Root.Compiler.initialVisit F) (initialAuthority seed claim)
  | n + 1 => nextAuthorityAt seed claim (temporalAt seed claim n) (authorityAt n)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
