import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.WorldClassification

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherFullCompiler MotherSourcePrograms MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source) (point : Point source)

def CertificateFor : (branch : EvolutionAt V point.1) → (target : TargetFor source branch) →
    LedgerFor source point.2 branch target → Type
  | .nativeWrite _, _, whole => ExactLedgerRestructuringCertificationAt law point.2 whole
  | .relationWrite _, _, whole => ExactLedgerRestructuringCertificationAt law point.2 whole
  | .continuedTransport _, _, whole => ExactLedgerRestructuringCertificationAt law point.2 whole
  | .borromeanRedirect _, _, whole => ExactLedgerRestructuringCertificationAt law point.2 whole
  | .faithfulTerminal _, _, _ => PUnit

def branchCertificateEquiv (branch : EvolutionAt V point.1) (structural : source.toRootSource.actual.compile point.2 = branch)
    (body : Sigma (LedgerFor source point.2 branch)) :
    SourceNativeLedgerRestructuringCertificationAt law
      (fromGraph source point.2 ⟨branch, ⟨(bodyEquiv source point.2 branch).symm body, structural⟩⟩) ≃
        CertificateFor law point branch body.1 body.2 := by
  cases branch <;> exact Equiv.refl _

def bodyCertificateEquiv (body : Sigma (LedgerFor source point.2 (source.toRootSource.actual.compile point.2))) :
    SourceNativeLedgerRestructuringCertificationAt law
      ((compilationEquiv source point.2).symm ((bodyEquiv source point.2 _).symm body)) ≃
        CertificateFor law point (source.toRootSource.actual.compile point.2) body.1 body.2 :=
  branchCertificateEquiv law point _ rfl body

def compiledCertificateEquiv (compiled : SourceNativeLedgerEvolutionAt source point.2) :
    SourceNativeLedgerRestructuringCertificationAt law compiled ≃
      CertificateFor law point (source.toRootSource.actual.compile point.2)
        (bodyOfCompilation point compiled).1 (bodyOfCompilation point compiled).2 :=
  (Equiv.cast (congrArg (SourceNativeLedgerRestructuringCertificationAt law)
    (((compilationEquiv source point.2).trans (bodyEquiv source point.2 _)).symm_apply_apply compiled).symm)).trans
      (bodyCertificateEquiv law point (bodyOfCompilation point compiled))

def castBodyCertificate {left right : EvolutionAt V point.1} (same : left = right)
    (body : Sigma (LedgerFor source point.2 left)) : CertificateFor law point left body.1 body.2 ≃
    CertificateFor law point right
      ((Equiv.cast (congrArg (fun branch => Sigma (LedgerFor source point.2 branch)) same)) body).1
      ((Equiv.cast (congrArg (fun branch => Sigma (LedgerFor source point.2 branch)) same)) body).2 := by
  cases same
  exact Equiv.refl _

def castExactCertificate {s s' t t' : N.Support} (hs : s = s') (ht : t = t')
    (whole : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩) : ExactLedgerRestructuringCertificationAt law point.2 whole ≃
      ExactLedgerRestructuringCertificationAt law point.2
        ((Equiv.cast (congrArg₂ (fun a b => LedgerWriteEvolutionAt N ⟨a⟩ ⟨b⟩) hs ht)) whole) := by
  cases hs
  cases ht
  exact Equiv.refl _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
