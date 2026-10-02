import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Assembly

/-! Actual mathematical entry authority follows the same complete patch.
Answer and compilation consume the two tokens installed before emission. -/

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

abbrev targetRoot := Assembly.targetRoot old registered packetAt
abbrev initial : Current registered := ⟨old.visit.current, initialEvent registered⟩

def finiteVisit : Nat → RootVisit (targetRoot old registered packetAt).toAuthoritativeRoot.toRoot
  | 0 => (targetRoot old registered packetAt).toAuthoritativeRoot.toRoot.initialVisit
  | depth + 1 => (finiteVisit depth).next rfl

def temporalVisit (depth : Nat) := SourceNativeTemporalVisitAt.finite (finiteVisit old registered packetAt depth)

theorem patch_destination_math (current : Current registered) :
    ((patch registered packetAt current).toLedgerWriteEvolution.destination
      (CompilerFromPacketSourceLaw.mathEntry registered current)).1 =
      CompilerFromPacketSourceLaw.mathEntry registered (targetCurrent registered packetAt current) :=
  (congrArg (fun evolution => (evolution.destination (CompilerFromPacketSourceLaw.mathEntry registered current)).1)
    (patch_fold registered packetAt current)).trans
    (join_destination_math (packetAt current.1) current.2)

private def initialRow :
    ((targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (temporalVisit old registered packetAt 0)).GeneratedEntryRowAt
      (CompilerFromPacketSourceLaw.mathEntry registered (initial old registered)) :=
  (((targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (temporalVisit old registered packetAt 0)).canonicalGeneratedEntryRow?
      (CompilerFromPacketSourceLaw.mathEntry registered (initial old registered))).get (by rfl)

private def authorityAt : (depth : Nat) → SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetRoot old registered packetAt) (temporalVisit old registered packetAt depth)
    (CompilerFromPacketSourceLaw.mathEntry registered (finiteVisit old registered packetAt depth).current)
  | 0 => .generatedFromInitialRow (targetRoot old registered packetAt) _ (initialRow old registered packetAt)
  | depth + 1 => by
      have next := (authorityAt depth).next (by rfl)
      have entryEq : (targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (by rfl)
          (CompilerFromPacketSourceLaw.mathEntry registered (finiteVisit old registered packetAt depth).current) =
          CompilerFromPacketSourceLaw.mathEntry registered (finiteVisit old registered packetAt (depth + 1)).current :=
        patch_destination_math old registered packetAt (finiteVisit old registered packetAt depth).current
      exact entryEq ▸ next

def mathCurrent (depth : Nat) := (finiteVisit old registered packetAt (depth + 1)).current
def mathVisit (depth : Nat) := temporalVisit old registered packetAt (depth + 1)
def mathEntry (depth : Nat) := CompilerFromPacketSourceLaw.mathEntry registered (mathCurrent old registered packetAt depth)
def mathAuthority (depth : Nat) := authorityAt old registered packetAt (depth + 1)

def rawFace (depth : Nat) : SourceNativeRootSemanticFaceAt
    (targetRoot old registered packetAt) (mathVisit old registered packetAt depth) where
  projection := (Assembly.rawInstallation old registered packetAt).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def completeFace (depth : Nat) : SourceNativeRootSemanticFaceAt
    (targetRoot old registered packetAt) (mathVisit old registered packetAt depth) where
  projection := (Assembly.completeInstallation old registered packetAt).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def mathAnswerFace (depth : Nat) : SourceNativeRootSemanticFaceAt
    (targetRoot old registered packetAt) (mathVisit old registered packetAt depth) where
  projection := (Assembly.oldInstallation old registered packetAt).embed (.inr PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

def mathConsumer (depth : Nat) : SourceNativeInquiryAnswerConsumerAt PUnit.unit
    (ULift.up.{u + 1, u} ((targetRoot old registered packetAt).emitted (mathCurrent old registered packetAt depth)))
    (mathEntry old registered packetAt depth) (mathAnswerFace old registered packetAt depth) where
  projection := (Assembly.consumerInstallation old registered packetAt).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def mathCompilation (depth : Nat) : SourceNativeInquiryCompilationProgramAt
    (targetRoot old registered packetAt) (mathVisit old registered packetAt depth)
    (Assembly.U7 old registered) (Assembly.calculus old registered)
    (Assembly.base old registered packetAt).lawSurface PUnit.unit
    (ULift.up.{u + 1, u} ((targetRoot old registered packetAt).emitted (mathCurrent old registered packetAt depth)))
    (mathEntry old registered packetAt depth) (mathAuthority old registered packetAt depth) where
  compile := fun _ => .answered (mathAnswerFace old registered packetAt depth) (mathConsumer old registered packetAt depth)

def mathState (depth : Nat) : RootInquiryStateAt (World registered) (JointV registered packetAt) where
  root := targetRoot old registered packetAt
  visit := mathVisit old registered packetAt depth
  U7 := Assembly.U7 old registered
  calculus := Assembly.calculus old registered
  Query := PUnit
  entryAt := fun _ => mathEntry old registered packetAt depth
  authorityAt := fun _ => mathAuthority old registered packetAt depth
  compilationProgramAt := fun query => by cases query; exact mathCompilation old registered packetAt depth
  compilationFaceAt := fun query => by
    cases query
    exact { projection := (Assembly.compilationInstallation old registered packetAt).embed PUnit.unit
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ _ _ impossible
    exact nomatch impossible

theorem math_compiles (depth : Nat) : (mathState old registered packetAt depth).compileInquiry PUnit.unit =
    .answered (mathAnswerFace old registered packetAt depth) (mathConsumer old registered packetAt depth) := rfl

theorem math_read (depth : Nat) : (mathAnswerFace old registered packetAt depth).rootRead =
    Native.mathReadout registered (mathCurrent old registered packetAt depth) := rfl

end RootGeneratedDebtActivationJointSource.Successor.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
