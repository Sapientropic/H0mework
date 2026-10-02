import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.MergeAcross

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {generated : Sorts} {outputFamilies : Families generated} (ops : Operations generated outputFamilies)
    (sorts : ∀ i, sortsOf law.vocabulary.base i ≃ generated i)
    (families : FamilyMap sorts (familiesOf law.vocabulary) outputFamilies)
    (p : OperationsAcross sorts families (operationsOf law.vocabulary) ops)
    {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {before after : CompleteLiveLedgerAt N} {evolution : LedgerWriteEvolutionAt N before after}

def splitClassificationEquiv {left right : after.Entry} {same : (evolution.origin left).1 = (evolution.origin right).1} :
    SourceNativeSplitClassificationAt law event evolution left right same ≃
      SourceNativeSplitClassificationAt (sourceLaw law ops sorts families p) event evolution left right same where
  toFun := fun value => match value with
    | .identity equality => .identity equality
    | .split coverage => .split (nativeSplitCoverageEquiv law ops sorts families p coverage)
  invFun := fun value => match value with
    | .identity equality => .identity equality
    | .split coverage => .split ((nativeSplitCoverageEquiv law ops sorts families p).symm coverage)
  left_inv := by
    intro value
    cases value with
    | identity => rfl
    | split coverage => exact congrArg SourceNativeSplitClassificationAt.split ((nativeSplitCoverageEquiv law ops sorts families p).symm_apply_apply coverage)
  right_inv := by
    intro value
    cases value with
    | identity => rfl
    | split coverage => exact congrArg SourceNativeSplitClassificationAt.split ((nativeSplitCoverageEquiv law ops sorts families p).apply_symm_apply coverage)

def mergeClassificationEquiv {left right : before.Entry} {same : (evolution.destination left).1 = (evolution.destination right).1} :
    SourceNativeMergeClassificationAt law event evolution left right same ≃
      SourceNativeMergeClassificationAt (sourceLaw law ops sorts families p) event evolution left right same where
  toFun := fun value => match value with
    | .identity equality => .identity equality
    | .merge coverage => .merge (nativeMergeCoverageEquiv law ops sorts families p coverage)
  invFun := fun value => match value with
    | .identity equality => .identity equality
    | .merge coverage => .merge ((nativeMergeCoverageEquiv law ops sorts families p).symm coverage)
  left_inv := by
    intro value
    cases value with
    | identity => rfl
    | merge coverage => exact congrArg SourceNativeMergeClassificationAt.merge ((nativeMergeCoverageEquiv law ops sorts families p).symm_apply_apply coverage)
  right_inv := by
    intro value
    cases value with
    | identity => rfl
    | merge coverage => exact congrArg SourceNativeMergeClassificationAt.merge ((nativeMergeCoverageEquiv law ops sorts families p).apply_symm_apply coverage)

def exactCertificateBodyEquiv : ExactLedgerRestructuringCertificationAt law event evolution ≃
    SplitClassificationSection (law := law) (event := event) evolution × MergeClassificationSection (law := law) (event := event) evolution where
  toFun := fun value => (fun pair => value.split pair.val.1 pair.val.2 pair.property, fun pair => value.merge pair.val.1 pair.val.2 pair.property)
  invFun := fun value => exactOfSections evolution value.1 value.2
  left_inv := fun value => by cases value; rfl
  right_inv := fun value => by cases value; rfl

def nativeExactEquiv : ExactLedgerRestructuringCertificationAt law event evolution ≃
    ExactLedgerRestructuringCertificationAt (sourceLaw law ops sorts families p) event evolution :=
  (exactCertificateBodyEquiv law).trans
    ((Equiv.prodCongr (Equiv.piCongrRight (fun _ => splitClassificationEquiv law ops sorts families p))
      (Equiv.piCongrRight (fun _ => mergeClassificationEquiv law ops sorts families p))).trans
        (exactCertificateBodyEquiv (sourceLaw law ops sorts families p)).symm)

def nativeCertificationEquiv (compiled : SourceNativeLedgerEvolutionAt source event) :
    SourceNativeLedgerRestructuringCertificationAt law compiled ≃
      SourceNativeLedgerRestructuringCertificationAt (sourceLaw law ops sorts families p) compiled := by
  cases compiled with
  | nativeWrite => exact nativeExactEquiv law ops sorts families p
  | relationWrite => exact nativeExactEquiv law ops sorts families p
  | continuedTransport => exact nativeExactEquiv law ops sorts families p
  | borromeanRedirect => exact nativeExactEquiv law ops sorts families p
  | faithfulTerminal => exact Equiv.refl _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
