import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Installation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Visits
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private theorem next_visit_eq {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {atRoot : SourceNativeLedgerRootClosure N V} (atVisit : SourceNativeTemporalVisitAt atRoot)
    {left right : V.Current} (same : left = right)
    (first : (atRoot.toRoot.evolutionAt atVisit.current).nextCurrent? = some left)
    (second : (atRoot.toRoot.evolutionAt atVisit.current).nextCurrent? = some right) :
    atVisit.next first = atVisit.next second := by cases same; rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (visit : SourceNativeTemporalVisitAt (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot)

local notation "F" => flow seed claim visit
local notation "R" => root seed claim visit
local notation "initial" => Abolition.Accounting.Root.Compiler.initialVisit F

def productiveEntry (atVisit : SourceNativeTemporalVisitAt (R).toAuthoritativeRoot.toLedgerRoot) :
    OpenResponsibilityAt (NewN seed claim) ((R).toAuthoritativeRoot.toRoot.supportAt atVisit.current) :=
  debtEntry (N := base seed claim) (law := Responsibility.Family.activationLaw seed.claim)
    (sourceSupport seed claim visit) (familyState seed claim (Runtime.sharedAt seed claim visit.current))

def canonicalVisit := (initial).next (Abolition.Accounting.Root.Compiler.nextEq F ())

def initialProductiveAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt R initial
    (productiveEntry seed claim visit initial) :=
  .generatedFromInitialRow R _ (Abolition.Accounting.Root.Compiler.generatedRow F initial _)

theorem canonical_productive_entry :
    (R).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
      (Abolition.Accounting.Root.Compiler.nextEq F ()) (productiveEntry seed claim visit initial) =
        productiveEntry seed claim visit (canonicalVisit seed claim visit) := by
  apply Financial.Installation.entry_eq_of_key
  · exact Abolition.Accounting.Root.Compiler.canonical_key_of_flow F () _ _ rfl
  · exact fibres seed claim _

def canonicalProductiveAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt R
    (canonicalVisit seed claim visit) (productiveEntry seed claim visit (canonicalVisit seed claim visit)) :=
  canonical_productive_entry seed claim visit ▸
    (initialProductiveAuthority seed claim visit).next (Abolition.Accounting.Root.Compiler.nextEq F ())

variable (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Runtime.Inquiry.root seed claim)
  visit (Origin.row seed claim visit))

theorem returned_visit_is_the_same_canonical_next :
    nextVisit seed claim visit sourceAuthority = canonicalVisit seed claim visit :=
  next_visit_eq initial (Abolition.Accounting.Root.Compiler.successor_current F ())
    (Abolition.Accounting.Root.Compiler.successor F ()).next_eq (Abolition.Accounting.Root.Compiler.nextEq F ())

def returnedProductiveAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt R
    (nextVisit seed claim visit sourceAuthority) (productiveEntry seed claim visit (nextVisit seed claim visit sourceAuthority)) :=
  (returned_visit_is_the_same_canonical_next seed claim visit sourceAuthority).symm ▸
    canonicalProductiveAuthority seed claim visit

def successor : Sparse.Current (oldN := base seed claim) seed.claim where
  V := V seed claim visit
  root := R
  visit := nextVisit seed claim visit sourceAuthority
  row := productiveEntry seed claim visit (nextVisit seed claim visit sourceAuthority)
  rowKey := rfl
  authority := returnedProductiveAuthority seed claim visit sourceAuthority
  basis := basis seed claim
  actualLaw := (originalContext seed claim visit).1
  members := (originalContext seed claim visit).2
  contextFace := contextFace seed claim visit (nextVisit seed claim visit sourceAuthority)
  context_heq := HEq.rfl

def nextSparse (n : Nat) : Sparse.Current (oldN := base seed claim) seed.claim :=
  successor seed claim (Runtime.temporalAt seed claim n) (Runtime.authorityAt seed claim n)

theorem actual_resumption_is_the_same_sparse_current :
    (RootInquiryProcessNode.answered (presentation seed claim visit sourceAuthority) PUnit.unit).erase =
      Sparse.Current.erase seed.claim (successor seed claim visit sourceAuthority) :=
  the_actual_process_resumes_at_the_same_normalized_root seed claim visit sourceAuthority

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
