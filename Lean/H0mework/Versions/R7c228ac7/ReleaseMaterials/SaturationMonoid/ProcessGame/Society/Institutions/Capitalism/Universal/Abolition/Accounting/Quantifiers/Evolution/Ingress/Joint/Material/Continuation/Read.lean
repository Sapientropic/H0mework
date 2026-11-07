import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (visit : SourceNativeTemporalVisitAt (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot)
  (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Runtime.Inquiry.root seed claim)
    visit (Origin.row seed claim visit))

theorem successor_state_is_the_one_actual_source_state :
    Sparse.Current.state seed.claim (successor seed claim visit sourceAuthority) =
      familyState seed claim (Runtime.sharedAt seed claim visit.current) := rfl

theorem successor_preserves_every_actual_coordinate :
    (Sparse.Current.state seed.claim (successor seed claim visit sourceAuthority)).raw =
        (Runtime.sharedAt seed claim visit.current).raw ∧
      (Sparse.Current.state seed.claim (successor seed claim visit sourceAuthority)).remaining =
        (Runtime.sharedAt seed claim visit.current).productive ∧
      (Sparse.Current.state seed.claim (successor seed claim visit sourceAuthority)).declared =
        (Runtime.sharedAt seed claim visit.current).productiveDeclared := ⟨rfl,rfl,rfl⟩

theorem successor_preserves_its_original_identity_and_claim :
    (successor seed claim visit sourceAuthority).row.1 = .inr (Responsibility.Family.originalId seed.claim) ∧
      (successor seed claim visit sourceAuthority).row.claim = .inr seed.claim := ⟨rfl,rfl⟩

theorem successor_preserves_its_actual_budget :
    (successor seed claim visit sourceAuthority).row.progressBudget =
      Current.productiveBudget seed claim (Runtime.sharedAt seed claim visit.current) := rfl

theorem successor_preserves_the_actual_payment :
    Responsibility.Family.State.isPaid seed.claim
        (Sparse.Current.state seed.claim (successor seed claim visit sourceAuthority)) ↔
      Current.productivePaid seed claim (Runtime.sharedAt seed claim visit.current) := Iff.rfl

theorem successor_uses_the_same_source_interpreter_and_roster :
    Sparse.Current.readLaw seed.claim (successor seed claim visit sourceAuthority) = actualLaw seed ∧
      Sparse.Current.readMembers seed.claim (successor seed claim visit sourceAuthority) = seed.current.members := ⟨rfl,rfl⟩

theorem successor_excludes_every_capital_relation :
    Global.NoCapital (Sparse.Current.readLaw seed.claim (successor seed claim visit sourceAuthority)) := by
  rw [(successor_uses_the_same_source_interpreter_and_roster seed claim visit sourceAuthority).1]
  exact seed.noCapital

theorem nextSparse_state (n : Nat) :
    Sparse.Current.state seed.claim (nextSparse seed claim n) =
      familyState seed claim (Runtime.sharedAt seed claim (Runtime.temporalAt seed claim n).current) := rfl

theorem nextSparse_base_support (n : Nat) :
    (Sparse.Current.support seed.claim (nextSparse seed claim n)).1 =
      Runtime.support seed claim (Runtime.temporalAt seed claim n).current := rfl

theorem nextSparse_paid_iff (n : Nat) :
    Responsibility.Family.State.isPaid seed.claim (Sparse.Current.state seed.claim (nextSparse seed claim n)) ↔
      Current.productivePaid seed claim (Runtime.sharedAt seed claim (Runtime.temporalAt seed claim n).current) := Iff.rfl

theorem nextSparse_no_capital (n : Nat) : Global.NoCapital (Sparse.Current.readLaw seed.claim (nextSparse seed claim n)) :=
  successor_excludes_every_capital_relation seed claim (Runtime.temporalAt seed claim n) (Runtime.authorityAt seed claim n)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
