import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Target
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Source

/-! The source's actual paid residual changes the existing mathematical
inquiry compiler at the same root and visit. No future query table is added. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry
open SourceOperationEffects DebtActivationWorld RootInquiryCompletion CompilerFromPacketSourceLaw
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (packetAt : (current : V.Current) → Packet old.root.toAuthoritativeRoot.toLedgerRoot current)
variable (environment : {current : V.Current} →
  old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current → Env Value Var)
variable (depth : Nat)

abbrev currentState := Source.currentState old registered packetAt depth
abbrev residual := Source.request old registered packetAt environment depth
abbrev residualProgramme := Source.programme old registered packetAt depth
abbrev residualPaid := Source.firstStep old registered packetAt environment depth

theorem residual_action : sourceAction (currentState old registered packetAt depth)
    (residual old registered packetAt environment depth) (residualProgramme old registered packetAt depth) =
      .inr (residualPaid old registered packetAt environment depth) :=
  (sourceAction_eq (currentState old registered packetAt depth) (residual old registered packetAt environment depth)
    (residualProgramme old registered packetAt depth)).trans
    (Source.firstStep_generated old registered packetAt environment depth)

def residualBirthProgram : SourceNativeDebtAdmissionActualActionProgramAt
    (currentState old registered packetAt depth).root (currentState old registered packetAt depth).visit
    ((currentState old registered packetAt depth).entryAt PUnit.unit)
    ((currentState old registered packetAt depth).authorityAt PUnit.unit) :=
  birthProgram (currentState old registered packetAt depth) PUnit.unit
    (residual old registered packetAt environment depth) (residualProgramme old registered packetAt depth)
    (mathAuthority old registered packetAt depth) (residualPaid old registered packetAt environment depth)
    (residual_action old registered packetAt environment depth)

def residualCompilation (query : PUnit) : SourceNativeInquiryCompilationProgramAt
    (currentState old registered packetAt depth).root (currentState old registered packetAt depth).visit
    (currentState old registered packetAt depth).U7 (currentState old registered packetAt depth).calculus
    (currentState old registered packetAt depth).root.toAuthoritativeRoot.source.lawSurface
    query ((currentState old registered packetAt depth).emitInquiry query)
    ((currentState old registered packetAt depth).entryAt query)
    ((currentState old registered packetAt depth).authorityAt query) where
  compile := fun event => .debtAdmission ((residualBirthProgram old registered packetAt environment depth).generate event)

def birthState : RootInquiryStateAt (World registered) (JointV registered packetAt) where
  root := (currentState old registered packetAt depth).root
  visit := (currentState old registered packetAt depth).visit
  U7 := (currentState old registered packetAt depth).U7
  calculus := (currentState old registered packetAt depth).calculus
  Query := PUnit
  entryAt := (currentState old registered packetAt depth).entryAt
  authorityAt := (currentState old registered packetAt depth).authorityAt
  compilationProgramAt := residualCompilation old registered packetAt environment depth
  compilationFaceAt := fun query => by
    cases query
    exact { projection := ((currentState old registered packetAt depth).compilationFaceAt PUnit.unit).projection
            active := ((currentState old registered packetAt depth).compilationFaceAt PUnit.unit).active
            classifier_eq := ((currentState old registered packetAt depth).compilationFaceAt PUnit.unit).classifier_eq
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ _ _ impossible
    exact nomatch impossible

theorem birth_compiles : (birthState old registered packetAt environment depth).compileInquiry PUnit.unit =
    .debtAdmission ((residualBirthProgram old registered packetAt environment depth).generate
      ((currentState old registered packetAt depth).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (currentState old registered packetAt depth).visit)) := rfl

theorem birth_root : (birthState old registered packetAt environment depth).root =
    (currentState old registered packetAt depth).root := rfl

theorem birth_visit : (birthState old registered packetAt environment depth).visit =
    (currentState old registered packetAt depth).visit := rfl

def born := ((residualBirthProgram old registered packetAt environment depth).generate
  ((currentState old registered packetAt depth).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    (currentState old registered packetAt depth).visit)).target

end RootGeneratedDebtActivationJointSource.Successor.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
