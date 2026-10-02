import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Law
import H0mework.Foundation.Responsibility.JointSource.Native.Scope

/-! Every classifier is read from the original source compiler. Its actual
children, parents and all proof-relevant receipt data survive the disjoint
vocabulary; membership is recovered from that full carrier without choice. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring
open SourceOperationEffects DebtActivationWorld

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (program : Program old.toLedgerRoot) {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)

def imageCertificate (current : V.Current) :
    ExactLedgerRestructuringCertificationAt (originalLaw old) (old.emitted current)
      (program.emit current).evolution := by
  have receipt := old.source.restructuringSource.compiler.certifyRestructuring (old.emitted current)
  exact Eq.mp (congrArg (SourceNativeLedgerRestructuringCertificationAt (originalLaw old))
    (program.emit current).generated_eq) receipt

private def castPacketCertificate {current next : V.Current}
    {target actual : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt next}
    (same : target = actual)
    (packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt old.toLedgerRoot.source.ledgerCompiler.writeRowSource
      (old.emitted current) ⟨old.toLedgerRoot.source.source.toRootSource.account.supportOf target⟩,
      LedgerCompleteFiniteCoverageAt rows)
    (receipt : ExactLedgerRestructuringCertificationAt (originalLaw old) (old.emitted current)
      (FiniteGeneratedLedgerWritePatchAt.complete packet.1 packet.2).toLedgerWriteEvolution) :
    ExactLedgerRestructuringCertificationAt (originalLaw old) (old.emitted current)
      (FiniteGeneratedLedgerWritePatchAt.complete
        ((same ▸ packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt old.toLedgerRoot.source.ledgerCompiler.writeRowSource
          (old.emitted current) ⟨old.toLedgerRoot.source.source.toRootSource.account.supportOf actual⟩,
          LedgerCompleteFiniteCoverageAt rows).1)
        ((same ▸ packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt old.toLedgerRoot.source.ledgerCompiler.writeRowSource
          (old.emitted current) ⟨old.toLedgerRoot.source.source.toRootSource.account.supportOf actual⟩,
          LedgerCompleteFiniteCoverageAt rows).2)).toLedgerWriteEvolution := by
  cases same
  exact receipt

def foldCertificate (current : Current registered) :
    ExactLedgerRestructuringCertificationAt (originalLaw old) (old.emitted current.1)
      (oldFold program registered current) := by
  have original := imageCertificate old program current.1
  have folded : ExactLedgerRestructuringCertificationAt (originalLaw old) (old.emitted current.1)
      (FiniteGeneratedLedgerWritePatchAt.complete (program.emit current.1).rows
        (program.emit current.1).coverage).toLedgerWriteEvolution := by
    rw [(program.emit current.1).fold_eq]
    exact original
  exact castPacketCertificate old (image_target program registered current)
    ⟨(program.emit current.1).rows, (program.emit current.1).coverage⟩ folded

private theorem oldMember_isSome (entries : List (Original old).Obligation)
    (entry : (vocabulary old registered).Obligation)
    (member : entry ∈ entries.map (oldObligation old registered)) : (readOld old registered entry).isSome := by
  obtain ⟨prior, _member, same⟩ := List.mem_map.mp member
  cases same
  rw [readOld_old]
  rfl

private def oldMember (entries : List (Original old).Obligation)
    (entry : (vocabulary old registered).Obligation)
    (member : entry ∈ entries.map (oldObligation old registered)) :
    { prior : (Original old).Obligation // prior ∈ entries ∧ oldObligation old registered prior = entry } :=
  ⟨(readOld old registered entry).get (oldMember_isSome old registered entries entry member), by
    obtain ⟨prior, priorMember, same⟩ := List.mem_map.mp member
    cases same
    have got := Option.some.inj ((Option.some_get
      (oldMember_isSome old registered entries (oldObligation old registered prior) member)).trans
      (readOld_old old registered prior))
    rw [got]
    exact ⟨priorMember, rfl⟩⟩

def oldAnchorTransport
    {first second : MinimalRegistrableSourceAnchor (Original old).base.SourceObservation
      (Original old).base.Scope (Original old).base.Lineage}
    (receipt : SourceAnchorTransport first second) :
    SourceAnchorTransport (oldAnchor old first) (oldAnchor old second) where
  toFun := Sum.map receipt.toFun id
  injective := Sum.map_injective.mpr ⟨receipt.injective, Function.injective_id⟩
  map_identity := congrArg Sum.inl receipt.map_identity
  map_complement := by
    rintro (prior | current)
    · exact congrArg Sum.inl (receipt.map_complement prior)
    · rfl
  scope_eq := congrArg Sum.inl receipt.scope_eq
  lineage_eq := congrArg Sum.inl receipt.lineage_eq

def splitReceipt {parent : (Original old).Obligation} (receipt : SplitReceipt (Original old) parent) :
    SplitReceipt (vocabulary old registered) (oldObligation old registered parent) where
  sourceEvent := .inl receipt.sourceEvent
  sourceOwnership :=
    { anchor_eq := congrArg (oldAnchor old) receipt.sourceOwnership.anchor_eq
      incidence_eq := congrArg Sum.inl receipt.sourceOwnership.incidence_eq }
  children := receipt.children.map (oldObligation old registered)
  children_nonempty := fun empty => receipt.children_nonempty (List.map_eq_nil_iff.mp empty)
  coverage := ⟨receipt.children.map AdmittedObligation.content,
    ⟨by rw [List.map_map, List.map_map]; rfl⟩, receipt.coverage⟩
  descendant := fun child member =>
    let prior := oldMember old registered receipt.children child member
    Eq.mp (congrArg (fun current : (vocabulary old registered).Obligation => (vocabulary old registered).DescendantAt
      (.inl receipt.sourceEvent) (oldObligation old registered parent).sourceIncidence
      (oldObligation old registered parent).content current.sourceIncidence current.content) prior.property.2)
      (receipt.descendant prior.val prior.property.1)
  anchorTransport := fun child member =>
    let prior := oldMember old registered receipt.children child member
    Eq.mp (congrArg (fun current : (vocabulary old registered).Obligation => SourceAnchorTransport
      (oldObligation old registered parent).sourceAnchor current.sourceAnchor) prior.property.2)
      (oldAnchorTransport old (receipt.anchorTransport prior.val prior.property.1))
  lineage := fun child member =>
    let prior := oldMember old registered receipt.children child member
    Eq.mp (congrArg (fun current : (vocabulary old registered).Obligation => SameDebtLineage (oldObligation old registered parent) current) prior.property.2)
      (congrArg Sum.inl (receipt.lineage prior.val prior.property.1))
  localDischarge := fun child member =>
    let prior := oldMember old registered receipt.children child member
    Eq.mp (congrArg (fun current : (vocabulary old registered).Obligation => (vocabulary old registered).LocalDischargePreservedAt
      (.inl receipt.sourceEvent) (oldObligation old registered parent).content current.content) prior.property.2)
      (receipt.localDischarge prior.val prior.property.1)

def mergeReceipt (receipt : MergeReceipt (Original old)) : MergeReceipt (vocabulary old registered) where
  sourceEvent := .inl receipt.sourceEvent
  parents := receipt.parents.map (oldObligation old registered)
  parents_nonempty := fun empty => receipt.parents_nonempty (List.map_eq_nil_iff.mp empty)
  target := oldObligation old registered receipt.target
  sourceOwnership :=
    { anchor_eq := congrArg (oldAnchor old) receipt.sourceOwnership.anchor_eq
      incidence_eq := congrArg Sum.inl receipt.sourceOwnership.incidence_eq }
  coverage := ⟨receipt.parents.map AdmittedObligation.content,
    ⟨by rw [List.map_map, List.map_map]; rfl⟩, receipt.coverage⟩
  ancestor := fun parent member =>
    let prior := oldMember old registered receipt.parents parent member
    Eq.mp (congrArg (fun current : (vocabulary old registered).Obligation => (vocabulary old registered).DescendantAt
      (.inl receipt.sourceEvent) current.sourceIncidence current.content
      (oldObligation old registered receipt.target).sourceIncidence
      (oldObligation old registered receipt.target).content) prior.property.2)
      (receipt.ancestor prior.val prior.property.1)
  anchorTransport := fun parent member =>
    let prior := oldMember old registered receipt.parents parent member
    Eq.mp (congrArg (fun current : (vocabulary old registered).Obligation => SourceAnchorTransport current.sourceAnchor
      (oldObligation old registered receipt.target).sourceAnchor) prior.property.2)
      (oldAnchorTransport old (receipt.anchorTransport prior.val prior.property.1))
  lineage := fun parent member =>
    let prior := oldMember old registered receipt.parents parent member
    Eq.mp (congrArg (fun current : (vocabulary old registered).Obligation => SameDebtLineage current (oldObligation old registered receipt.target)) prior.property.2)
      (congrArg Sum.inl (receipt.lineage prior.val prior.property.1))
  localDischarge := fun parent member =>
    let prior := oldMember old registered receipt.parents parent member
    Eq.mp (congrArg (fun current : (vocabulary old registered).Obligation => (vocabulary old registered).LocalDischargePreservedAt
      (.inl receipt.sourceEvent) current.content (oldObligation old registered receipt.target).content) prior.property.2)
      (receipt.localDischarge prior.val prior.property.1)


variable (current : (JointV program registered).Current)

private theorem original_origin_eq
    (first second : OpenResponsibilityAt N
      (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted (targetCurrent program registered current).1)))
    (same : ((patch program registered current).toLedgerWriteEvolution.origin
      (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent program registered current).2.state) first)).1 =
      ((patch program registered current).toLedgerWriteEvolution.origin
        (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent program registered current).2.state) second)).1) :
    ((oldFold program registered current).origin first).1 = ((oldFold program registered current).origin second).1 :=
  RootGeneratedDebtActivationJointSource.Native.oldEntry_injective
    ((patch_origin_old program registered current first).symm.trans
      (same.trans (patch_origin_old program registered current second)))

private theorem original_destination_eq
    (first second : OpenResponsibilityAt N
      (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted current.1)))
    (same : ((patch program registered current).toLedgerWriteEvolution.destination
      (oldEntry (law := MathLaw old registered) (state? := some current.2.state) first)).1 =
      ((patch program registered current).toLedgerWriteEvolution.destination
        (oldEntry (law := MathLaw old registered) (state? := some current.2.state) second)).1) :
    ((oldFold program registered current).destination first).1 = ((oldFold program registered current).destination second).1 :=
  RootGeneratedDebtActivationJointSource.Native.oldEntry_injective
    ((patch_destination_old program registered current first).symm.trans
      (same.trans (patch_destination_old program registered current second)))

private def castSplit {first second : (vocabulary old registered).Obligation} (same : first = second)
    (receipt : SplitReceipt (vocabulary old registered) second) : SplitReceipt (vocabulary old registered) first :=
  Eq.mpr (congrArg (SplitReceipt (vocabulary old registered)) same) receipt

private theorem castSplit_source {first second : (vocabulary old registered).Obligation} (same : first = second)
    (receipt : SplitReceipt (vocabulary old registered) second) :
    (castSplit old registered same receipt).sourceEvent = receipt.sourceEvent := by cases same; rfl

private theorem castSplit_children {first second : (vocabulary old registered).Obligation} (same : first = second)
    (receipt : SplitReceipt (vocabulary old registered) second) :
    (castSplit old registered same receipt).children = receipt.children := by cases same; rfl

variable (left right : OpenResponsibilityAt N
  (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted (targetCurrent program registered current).1)))
variable (same : ((patch program registered current).toLedgerWriteEvolution.origin
  (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent program registered current).2.state) left)).1 =
  ((patch program registered current).toLedgerWriteEvolution.origin
    (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent program registered current).2.state) right)).1)

def splitCoverage
    (original : SourceNativeSplitCoverageAt (originalLaw old) (old.emitted current.1)
      (oldFold program registered current) left right (original_origin_eq old program registered current left right same)) :
    SourceNativeSplitCoverageAt (law old program registered) (emitted program registered current)
      (patch program registered current).toLedgerWriteEvolution
      (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent program registered current).2.state) left)
      (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent program registered current).2.state) right) same := by
  let parentEq : (law old program registered).obligationAt (emitted program registered current)
      ((patch program registered current).toLedgerWriteEvolution.origin
        (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent program registered current).2.state) left)).1 =
      oldObligation old registered ((originalLaw old).obligationAt (old.emitted current.1)
        ((oldFold program registered current).origin left).1) := by
    exact congrArg ((law old program registered).obligationAt (emitted program registered current))
      (patch_origin_old program registered current left)
  let receipt := castSplit old registered parentEq (splitReceipt old registered original.receipt)
  refine SourceNativeSplitCoverageAt.ofReceipt receipt ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp only [receipt]
    rw [castSplit_source]
    exact congrArg Sum.inl original.sourceEvent_eq
  · dsimp only [receipt]
    rw [castSplit_children]
    exact List.mem_map_of_mem (f := oldObligation old registered) original.left_member
  · dsimp only [receipt]
    rw [castSplit_children]
    exact List.mem_map_of_mem (f := oldObligation old registered) original.right_member
  · intro target targetEq
    rcases target with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior =>
        have oldEq := original_origin_eq old program registered current ⟨prior, opened⟩ left targetEq
        dsimp only [receipt]
        rw [castSplit_children]
        exact List.mem_map_of_mem (f := oldObligation old registered) (original.covers_target ⟨prior, opened⟩ oldEq)
    | inr debt =>
        rcases opened with ⟨⟨idEq⟩⟩
        cases idEq
        have incompatible := (patch_origin_math program registered current).symm.trans
          (targetEq.trans (patch_origin_old program registered current left))
        exact nomatch congrArg Sigma.fst incompatible
  · intro target targetEq
    rcases target with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior =>
        have budgets := congrArg OpenResponsibilityAt.progressBudget
          (patch_origin_old program registered current left)
        exact lt_of_lt_of_eq (original.childProgressBudget_strictlyDebited ⟨prior, opened⟩
          (original_origin_eq old program registered current ⟨prior, opened⟩ left targetEq)) budgets.symm
    | inr debt =>
        rcases opened with ⟨⟨idEq⟩⟩
        cases idEq
        have incompatible := (patch_origin_math program registered current).symm.trans
          (targetEq.trans (patch_origin_old program registered current left))
        exact nomatch congrArg Sigma.fst incompatible
  · intro child member
    have mapped : child ∈ original.receipt.children.map (oldObligation old registered) := by
      dsimp only [receipt] at member
      rw [castSplit_children] at member
      exact member
    let prior := oldMember old registered original.receipt.children child mapped
    let target := original.no_phantom_child prior.val prior.property.1
    refine ⟨oldEntry (law := MathLaw old registered)
      (state? := some (targetCurrent program registered current).2.state) target.val, ?_, ?_⟩
    · exact (congrArg (oldObligation old registered) target.property.1).trans prior.property.2
    · exact (patch_origin_old program registered current target.val).trans
        ((congrArg (oldEntry (law := MathLaw old registered) (state? := some current.2.state)) target.property.2).trans
          (patch_origin_old program registered current left).symm)

omit left right same in
 def mergeCoverage
    (left right : OpenResponsibilityAt N (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted current.1)))
    (same : ((patch program registered current).toLedgerWriteEvolution.destination
      (oldEntry (law := MathLaw old registered) (state? := some current.2.state) left)).1 =
      ((patch program registered current).toLedgerWriteEvolution.destination
        (oldEntry (law := MathLaw old registered) (state? := some current.2.state) right)).1)
    (original : SourceNativeMergeCoverageAt (originalLaw old) (old.emitted current.1)
      (oldFold program registered current) left right (original_destination_eq old program registered current left right same)) :
    SourceNativeMergeCoverageAt (law old program registered) (emitted program registered current)
      (patch program registered current).toLedgerWriteEvolution
      (oldEntry (law := MathLaw old registered) (state? := some current.2.state) left)
      (oldEntry (law := MathLaw old registered) (state? := some current.2.state) right) same := by
  let receipt := mergeReceipt old registered original.receipt
  refine SourceNativeMergeCoverageAt.ofReceipt receipt ?_ ?_ ?_ ?_ ?_ ?_
  · exact congrArg Sum.inl original.sourceEvent_eq
  · exact (congrArg (oldObligation old registered) original.target_eq).trans
      (congrArg ((law old program registered).obligationAt (emitted program registered current))
        (patch_destination_old program registered current left)).symm
  · exact List.mem_map_of_mem (f := oldObligation old registered) original.left_member
  · exact List.mem_map_of_mem (f := oldObligation old registered) original.right_member
  · intro source sourceEq
    rcases source with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior =>
        exact List.mem_map_of_mem (f := oldObligation old registered) (original.covers_source ⟨prior, opened⟩
          (original_destination_eq old program registered current ⟨prior, opened⟩ left sourceEq))
    | inr debt =>
        rcases opened with ⟨⟨idEq⟩⟩
        cases idEq
        have incompatible := (patch_destination_math program registered current).symm.trans
          (sourceEq.trans (patch_destination_old program registered current left))
        exact nomatch congrArg Sigma.fst incompatible
  · intro parent member
    let prior := oldMember old registered original.receipt.parents parent member
    let source := original.no_phantom_parent prior.val prior.property.1
    refine ⟨oldEntry (law := MathLaw old registered) (state? := some current.2.state) source.val, ?_, ?_⟩
    · exact (congrArg (oldObligation old registered) source.property.1).trans prior.property.2
    · exact (patch_destination_old program registered current source.val).trans
        ((congrArg (oldEntry (law := MathLaw old registered)
          (state? := some (targetCurrent program registered current).2.state)) source.property.2).trans
            (patch_destination_old program registered current left).symm)


omit left right same in
def certificate : ExactLedgerRestructuringCertificationAt (law old program registered)
    (emitted program registered current) (patch program registered current).toLedgerWriteEvolution where
  split := by
    rintro ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            let oldSame := original_origin_eq old program registered current ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same
            cases (foldCertificate old program registered current).split ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ oldSame with
            | identity equality =>
                exact .identity (congrArg (oldEntry (law := MathLaw old registered)
                  (state? := some (targetCurrent program registered current).2.state)) equality)
            | split original =>
                exact .split (splitCoverage old program registered current ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same original)
        | inr debt =>
            rcases secondOpen with ⟨⟨idEq⟩⟩
            cases idEq
            have incompatible := (patch_origin_old program registered current ⟨first, firstOpen⟩).symm.trans
              (same.trans (patch_origin_math program registered current))
            exact nomatch congrArg Sigma.fst incompatible
    | inr debt =>
        rcases firstOpen with ⟨⟨idEq⟩⟩
        cases idEq
        cases second with
        | inl second =>
            have incompatible := (patch_origin_math program registered current).symm.trans
              (same.trans (patch_origin_old program registered current ⟨second, secondOpen⟩))
            exact nomatch congrArg Sigma.fst incompatible
        | inr second => rcases secondOpen with ⟨⟨idEq⟩⟩; cases idEq; exact .identity rfl
  merge := by
    rintro ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            let oldSame := original_destination_eq old program registered current ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same
            cases (foldCertificate old program registered current).merge ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ oldSame with
            | identity equality =>
                exact .identity (congrArg (oldEntry (law := MathLaw old registered) (state? := some current.2.state)) equality)
            | merge original =>
                exact .merge (mergeCoverage old program registered current ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same original)
        | inr debt =>
            rcases secondOpen with ⟨⟨idEq⟩⟩
            cases idEq
            have incompatible := (patch_destination_old program registered current ⟨first, firstOpen⟩).symm.trans
              (same.trans (patch_destination_math program registered current))
            exact nomatch congrArg Sigma.fst incompatible
    | inr debt =>
        rcases firstOpen with ⟨⟨idEq⟩⟩
        cases idEq
        cases second with
        | inl second =>
            have incompatible := (patch_destination_math program registered current).symm.trans
              (same.trans (patch_destination_old program registered current ⟨second, secondOpen⟩))
            exact nomatch congrArg Sigma.fst incompatible
        | inr second => rcases secondOpen with ⟨⟨idEq⟩⟩; cases idEq; exact .identity rfl

end RootGeneratedDebtActivationJointSource.Native.Restructuring
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
