import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryServiceSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawNativeReconfirmation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {Index : Type} (bound : ProgrammeFamily base scope Index) (inputs : Index)
  (original : Claim bound inputs) (first second : Position bound inputs)

structure Conditions : Prop where
  old : original.position.ordinal < first.ordinal
  pending : (through bound inputs original first.ordinal).isPending bound inputs = true
  sameVisit : second.ordinal = first.ordinal
  ordered : first.index.val < second.index.val
  signed : Submission (scope := scope) (first.item bound inputs).request
  accepted : (Mandate.law base scope).Valid (first.item bound inputs).before (first.item bound inputs).request
  active : (first.item bound inputs).before.technology.holder.isSome = true ∨
    (first.item bound inputs).before.technology.offered.isSome = true
  signer : (first.item bound inputs).request.signer = original.signer bound inputs
  withdrawal : Withdrawal (scope := scope) (second.item bound inputs).before (second.item bound inputs).request
  snapshot : (second.item bound inputs).before.technology = (first.item bound inputs).before.technology
  paid : (Mandate.law base scope).Valid (second.item bound inputs).before (second.item bound inputs).request

instance : Decidable (Conditions bound inputs original first second) :=
  decidable_of_iff
    (original.position.ordinal < first.ordinal ∧
      (through bound inputs original first.ordinal).isPending bound inputs = true ∧
      second.ordinal = first.ordinal ∧ first.index.val < second.index.val ∧
      Submission (scope := scope) (first.item bound inputs).request ∧
      (Mandate.law base scope).Valid (first.item bound inputs).before (first.item bound inputs).request ∧
      ((first.item bound inputs).before.technology.holder.isSome = true ∨
        (first.item bound inputs).before.technology.offered.isSome = true) ∧
      (first.item bound inputs).request.signer = original.signer bound inputs ∧
      Withdrawal (scope := scope) (second.item bound inputs).before (second.item bound inputs).request ∧
      (second.item bound inputs).before.technology = (first.item bound inputs).before.technology ∧
      (Mandate.law base scope).Valid (second.item bound inputs).before (second.item bound inputs).request)
    ⟨fun h => by rcases h with ⟨a,b,c,d,e,f,g,h,i,j,k⟩; exact ⟨a,b,c,d,e,f,g,h,i,j,k⟩,
      fun h => ⟨h.old,h.pending,h.sameVisit,h.ordered,h.signed,h.accepted,h.active,h.signer,h.withdrawal,h.snapshot,h.paid⟩⟩

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem withdrawal_is_not_submission
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (action : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (withdrawal : Withdrawal (scope := scope) current action) : ¬ Submission (scope := scope) action := by
  rcases action with ⟨signer, consents, purpose, gates, operation⟩
  cases operation <;> simp_all [Submission, Withdrawal]

theorem raw_items_generate_the_same_original_reconfirmation_and_paid_attempt
    (conditions : Conditions bound inputs original first second) :
    ∃ receipt : Reconfirmation bound inputs original,
      readReconfirmation bound inputs original first = some receipt ∧
      receipt.target.position = first ∧
      ReconfirmationClosure.advances bound inputs original first receipt = true ∧
      readReconfirmation bound inputs original second = none ∧
      ∃ attempt : Attempt bound inputs receipt.target,
        readAttempt bound inputs receipt.target second = some attempt ∧
        (Mandate.law base scope).Valid (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request := by
  obtain ⟨target, decoded⟩ : ∃ target, read bound inputs first = some target := by
    simp only [Mandate.Challenge.read, dif_pos conditions.signed, dif_pos conditions.accepted, dif_pos conditions.active]
    exact ⟨_, rfl⟩
  have position := read_position bound inputs first target decoded
  have later : Later bound inputs original.position target.position := by
    rw [position]; exact Or.inl conditions.old
  have signer : target.signer bound inputs = original.signer bound inputs := by
    unfold Claim.signer; rw [position]; exact conditions.signer
  obtain ⟨receipt, renewed, targetExact⟩ : ∃ receipt : Reconfirmation bound inputs original,
      readReconfirmation bound inputs original first = some receipt ∧ receipt.target = target := by
    simp only [readReconfirmation, decoded, dif_pos (And.intro later signer)]
    exact ⟨_, rfl, rfl⟩
  have targetPosition : receipt.target.position = first := by rw [targetExact]; exact position
  have forward : ReconfirmationClosure.advances bound inputs original first receipt = true := by
    have within := Cross.Programme.local_through_within bound original first.ordinal first.ordinal conditions.old (Nat.le_refl _)
    unfold ReconfirmationClosure.advances
    cases before : through bound inputs original first.ordinal with
    | closed state archive slots =>
      have pending := conditions.pending
      simp only [before, History.isPending] at pending
      cases pending
    | pending previous state slots =>
      rw [before] at within
      change (previous.claim bound inputs).position.ordinal < first.ordinal at within
      apply decide_eq_true
      rw [targetPosition]
      exact Or.inl within
  have unsigned := withdrawal_is_not_submission (second.item bound inputs).before (second.item bound inputs).request conditions.withdrawal
  have noRead : read bound inputs second = none := by simp only [Mandate.Challenge.read, dif_neg unsigned]
  have noRenewal : readReconfirmation bound inputs original second = none := by simp only [readReconfirmation, noRead]
  have attemptLater : Later bound inputs receipt.target.position second := by
    rw [targetPosition]
    exact Or.inr ⟨conditions.sameVisit.symm, conditions.ordered⟩
  have snapshot : (second.item bound inputs).before.technology = receipt.target.snapshot bound inputs := by
    unfold Claim.snapshot; rw [targetPosition]; exact conditions.snapshot
  obtain ⟨attempt, attempted⟩ : ∃ attempt : Attempt bound inputs receipt.target,
      readAttempt bound inputs receipt.target second = some attempt := by
    simp only [readAttempt, dif_pos (And.intro attemptLater (And.intro conditions.withdrawal snapshot))]
    exact ⟨_, rfl⟩
  have attemptPosition : attempt.position = second := by
    unfold readAttempt at attempted
    split at attempted
    · cases Option.some.inj attempted; rfl
    · cases attempted
  refine ⟨receipt, renewed, targetPosition, forward, noRenewal, attempt, attempted, ?_⟩
  rw [attemptPosition]; exact conditions.paid

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawNativeReconfirmation
