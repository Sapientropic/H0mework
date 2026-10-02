import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.WorldMerge

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherFullCompiler MotherSourcePrograms MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    {p : MotherNativeSourceOrigin.Presentation n v original generated}
    {law : SourceNativeLedgerRestructuringLaw original} {point : Point original}
    {before after : CompleteLiveLedgerAt N} {newBefore newAfter : CompleteLiveLedgerAt G}
    {whole : LedgerWriteEvolutionAt N before after} {image : LedgerWriteEvolutionAt G newBefore newAfter}
    (frame : WorldFrame p law point whole image)

def WorldFrame.splitClassificationEquiv (left right : after.Entry) {same : (whole.origin left).1 = (whole.origin right).1} :
    SourceNativeSplitClassificationAt law point.2 whole left right same ≃
      SourceNativeSplitClassificationAt (worldLaw p law) (pointEquiv p point).2 image (frame.after left) (frame.after right)
        ((frame.origin_iff left right).mp same) where
  toFun := fun value => match value with
    | .identity equality => .identity (congrArg frame.after equality)
    | .split coverage => .split (frame.splitCoverageEquiv left right coverage)
  invFun := fun value => match value with
    | .identity equality => .identity (frame.after.injective equality)
    | .split coverage => .split ((frame.splitCoverageEquiv left right).symm coverage)
  left_inv := by
    intro value
    cases value with
    | identity => rfl
    | split coverage => exact congrArg SourceNativeSplitClassificationAt.split ((frame.splitCoverageEquiv left right).symm_apply_apply coverage)
  right_inv := by
    intro value
    cases value with
    | identity => rfl
    | split coverage => exact congrArg SourceNativeSplitClassificationAt.split ((frame.splitCoverageEquiv left right).apply_symm_apply coverage)

def WorldFrame.mergeClassificationEquiv (left right : before.Entry) {same : (whole.destination left).1 = (whole.destination right).1} :
    SourceNativeMergeClassificationAt law point.2 whole left right same ≃
      SourceNativeMergeClassificationAt (worldLaw p law) (pointEquiv p point).2 image (frame.before left) (frame.before right)
        ((frame.destination_iff left right).mp same) where
  toFun := fun value => match value with
    | .identity equality => .identity (congrArg frame.before equality)
    | .merge coverage => .merge (frame.mergeCoverageEquiv left right coverage)
  invFun := fun value => match value with
    | .identity equality => .identity (frame.before.injective equality)
    | .merge coverage => .merge ((frame.mergeCoverageEquiv left right).symm coverage)
  left_inv := by
    intro value
    cases value with
    | identity => rfl
    | merge coverage => exact congrArg SourceNativeMergeClassificationAt.merge ((frame.mergeCoverageEquiv left right).symm_apply_apply coverage)
  right_inv := by
    intro value
    cases value with
    | identity => rfl
    | merge coverage => exact congrArg SourceNativeMergeClassificationAt.merge ((frame.mergeCoverageEquiv left right).apply_symm_apply coverage)

def WorldFrame.splitContextEquiv : SplitContext whole ≃ SplitContext image :=
  Equiv.subtypeEquiv (Equiv.prodCongr frame.after frame.after) (fun pair => frame.origin_iff pair.1 pair.2)

def WorldFrame.mergeContextEquiv : MergeContext whole ≃ MergeContext image :=
  Equiv.subtypeEquiv (Equiv.prodCongr frame.before frame.before) (fun pair => frame.destination_iff pair.1 pair.2)

def WorldFrame.exactEquiv : ExactLedgerRestructuringCertificationAt law point.2 whole ≃
    ExactLedgerRestructuringCertificationAt (worldLaw p law) (pointEquiv p point).2 image :=
  (exactCertificateBodyEquiv law).trans
    ((Equiv.prodCongr
      (Equiv.piCongr frame.splitContextEquiv (fun pair => frame.splitClassificationEquiv pair.val.1 pair.val.2))
      (Equiv.piCongr frame.mergeContextEquiv (fun pair => frame.mergeClassificationEquiv pair.val.1 pair.val.2))).trans
        (exactCertificateBodyEquiv (worldLaw p law)).symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
