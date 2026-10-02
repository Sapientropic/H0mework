import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.CertificateBody

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherFullCompiler MotherSourcePrograms MotherFullPatches MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

private theorem event_cast_support {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) {a b : V.Current} (same : a = b)
    (event : source.toRootSource.actual.OccurrenceAt a) :
    ((Equiv.cast (congrArg source.toRootSource.actual.OccurrenceAt same)) event).1 = event.1 := by
  cases same
  rfl

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (law : SourceNativeLedgerRestructuringLaw original)

def certificateWithTargets (point : Point original) (target : N.Support) (newTarget : G.Support)
    (same : newTarget = n.support target) (whole : LedgerWriteEvolutionAt N ⟨point.2.1⟩ ⟨target⟩) :
    ExactLedgerRestructuringCertificationAt law point.2 whole ≃
      ExactLedgerRestructuringCertificationAt (worldLaw p law) (pointEquiv p point).2
        ((Equiv.cast (congrArg₂ (fun a b => LedgerWriteEvolutionAt G ⟨a⟩ ⟨b⟩)
          (p.support_eq point.1 point.2).symm same.symm)) (n.wholeLedgerEquiv point.2.1 target whole)) :=
  (normalizedFrame p law point whole).exactEquiv.trans
    (castExactCertificate (worldLaw p law) (pointEquiv p point) (p.support_eq point.1 point.2).symm same.symm
      (n.wholeLedgerEquiv point.2.1 target whole))

def transportBodyCertificate (point : Point original) (branch : EvolutionAt V point.1)
    (target : TargetFor original branch) (whole : LedgerFor original point.2 branch target) :
    CertificateFor law point branch target whole ≃
      CertificateFor (worldLaw p law) (pointEquiv p point) (v.evolution point.1 branch)
        (targetEquiv p branch target) (ledgerForEquiv p point.2 branch target whole) := by
  cases branch with
  | nativeWrite write =>
      have targetSupport := (event_cast_support generated (v.native_eq point.1 write).symm
        (p.event (V.nativeTarget write) target)).trans (p.support_eq (V.nativeTarget write) target)
      exact certificateWithTargets p law point target.1 _ targetSupport whole
  | relationWrite write =>
      have targetSupport := (event_cast_support generated (v.relation_eq point.1 write).symm
        (p.event (V.relationTarget write) target)).trans (p.support_eq (V.relationTarget write) target)
      exact certificateWithTargets p law point target.1 _ targetSupport whole
  | continuedTransport write =>
      have targetSupport := (event_cast_support generated (v.continued_eq point.1 write).symm
        (p.event (V.continuedTarget write) target)).trans (p.support_eq (V.continuedTarget write) target)
      exact certificateWithTargets p law point target.1 _ targetSupport whole
  | borromeanRedirect write =>
      have targetSupport := (event_cast_support generated (v.redirect_eq point.1 write).symm
        (p.event (V.redirectTarget write) target)).trans (p.support_eq (V.redirectTarget write) target)
      exact certificateWithTargets p law point target.1 _ targetSupport whole
  | faithfulTerminal => exact Equiv.refl _

/-- The complete original certification travels through exactly the same
full Compilation equivalence used by the original source/compiler recovery. -/
def fullCertificateEquiv (point : Point original) (compiled : SourceNativeLedgerEvolutionAt original point.2) :
    SourceNativeLedgerRestructuringCertificationAt law compiled ≃
      SourceNativeLedgerRestructuringCertificationAt (worldLaw p law) (fullCompilationEquiv p point.2 compiled) :=
  let body := bodyOfCompilation point compiled
  let mapped : Sigma (LedgerFor generated (pointEquiv p point).2
      (v.evolution point.1 (original.toRootSource.actual.compile point.2))) :=
    ⟨targetEquiv p _ body.1, ledgerForEquiv p point.2 _ body.1 body.2⟩
  let castBody := (Equiv.cast (congrArg
    (fun branch => Sigma (LedgerFor generated (pointEquiv p point).2 branch)) (p.compile_eq point.1 point.2).symm)) mapped
  (compiledCertificateEquiv law point compiled).trans
    ((transportBodyCertificate p law point _ body.1 body.2).trans
      ((castBodyCertificate (worldLaw p law) (pointEquiv p point) (p.compile_eq point.1 point.2).symm mapped).trans
        (bodyCertificateEquiv (worldLaw p law) (pointEquiv p point) castBody).symm))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
