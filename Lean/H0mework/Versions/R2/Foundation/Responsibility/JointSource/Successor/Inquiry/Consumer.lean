import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Birth

/-! The existing debt-admission resolver consumes the actual residual birth.
Its next inquiry reads the same generated target root and complete ledger. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Consumer
open SourceOperationEffects RootInquiryCompletion CompilerFromPacketSourceLaw

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (packetAt : (current : V.Current) → Packet old.root.toAuthoritativeRoot.toLedgerRoot current)
variable (environment : {current : V.Current} →
  old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current → Env Value Var)
variable (depth : Nat)

def sourcePresentation : RootInquiryStatePresentation where
  N := World registered
  V := JointV registered packetAt
  state := .create (birthState old registered packetAt environment depth)

def targetState := mathState (Source.currentState old registered packetAt depth)
  (Source.request old registered packetAt environment depth) (Source.programme old registered packetAt depth) 0

def targetPresentation : RootInquiryStatePresentation where
  N := World (Source.request old registered packetAt environment depth)
  V := JointV (Source.request old registered packetAt environment depth) (Source.programme old registered packetAt depth)
  state := .create (targetState old registered packetAt environment depth)

theorem target_root : (targetState old registered packetAt environment depth).root =
    (born old registered packetAt environment depth).targetRoot := rfl

theorem target_visit : (targetState old registered packetAt environment depth).visit =
    (born old registered packetAt environment depth).targetVisit := rfl

theorem born_next : (born old registered packetAt environment depth).targetAnswerAndNext.nextCurrent =
    ⟨JointV (Source.request old registered packetAt environment depth) (Source.programme old registered packetAt depth),
      (targetState old registered packetAt environment depth).root.toAuthoritativeRoot,
      (targetState old registered packetAt environment depth).visit⟩ :=
  (born old registered packetAt environment depth).targetAnswerAndNext_next_eq

theorem successor_valid : (targetPresentation old registered packetAt environment depth).erase =
    (RootInquiryProcessNode.answered (sourcePresentation old registered packetAt environment depth) PUnit.unit).erase ∧
    (RootInquiryProcessNode.active (sourcePresentation old registered packetAt environment depth)).PreservesGeneratedLivingLawAt
      PUnit.unit (.active (targetPresentation old registered packetAt environment depth)) := by
  apply RootInquiryProcessNode.active_debtAdmission_successor_valid
    (sourcePresentation old registered packetAt environment depth)
    (targetPresentation old registered packetAt environment depth) PUnit.unit
    ((residualBirthProgram old registered packetAt environment depth).generate
      ((Source.currentState old registered packetAt depth).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (Source.currentState old registered packetAt depth).visit))
    (birth_compiles old registered packetAt environment depth)
  · exact (congrArg (fun current =>
      (⟨World (Source.request old registered packetAt environment depth), current⟩ : AnyAuthoritativeRootCurrent.{u}))
      (born_next old registered packetAt environment depth)).symm
  · exact HEq.rfl

end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
