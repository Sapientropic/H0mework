import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Law
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Certificate

/-! The original compiler's whole-write restructuring receipt is lifted
through the actual joint mathematical action, independently of finite coverage. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Restructuring
open SourceOperationEffects DebtActivationWorld DebtActivationLedger CompilerFromPacketSourceLaw
open Native.Restructuring (originalLaw Original MathLaw vocabulary oldObligation mathObligation readOld readOld_old oldObligation_injective splitReceipt mergeReceipt)

private def certificateOfGenerated
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}} {source : SourceNativeSource N V}
    (originalLaw : SourceNativeLedgerRestructuringLaw source)
    {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated)
    (receipt : SourceNativeLedgerRestructuringCertificationAt originalLaw generated) :
    ExactLedgerRestructuringCertificationAt originalLaw occurrence successor.ledgerEvolution := by
  cases generated with
  | nativeWrite => exact receipt
  | relationWrite => exact receipt
  | continuedTransport => exact receipt
  | borromeanRedirect => exact receipt
  | faithfulTerminal => exact nomatch successor

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)

/-- Read the original full certificate at its exact generated successor. -/
def originalCertificate {current : V.Current} (packet : Packet old.toLedgerRoot current) :
    ExactLedgerRestructuringCertificationAt (originalLaw old) (old.emitted current) packet.ledgerEvolution :=
  certificateOfGenerated (originalLaw old) packet.successor
    (old.source.restructuringSource.compiler.certifyRestructuring (old.emitted current))


private def castCertificate {sourceLedger : CompleteLiveLedgerAt N} {target actual : N.Support}
    {current : V.Current} {occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current}
    (same : target = actual)
    (rows : LedgerWriteEvolutionAt N sourceLedger ⟨target⟩)
    (receipt : ExactLedgerRestructuringCertificationAt (originalLaw old) occurrence rows) :
    ExactLedgerRestructuringCertificationAt (originalLaw old) occurrence (same ▸ rows) := by
  cases same
  exact receipt

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)
variable (packetAt : (current : V.Current) → Packet old.toLedgerRoot current)

def foldCertificate (current : Current registered) :
    ExactLedgerRestructuringCertificationAt (originalLaw old) (old.emitted current.1)
      (originalFold (packetAt current.1)) :=
  castCertificate old
    (congrArg (old.toLedgerRoot.source.source.toRootSource.account.supportOf) (packetAt current.1).target_emitted)
    (packetAt current.1).ledgerEvolution (originalCertificate old (packetAt current.1))

private theorem whole_destination_old (current : Current registered)
    (entry : OpenResponsibilityAt N (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted current.1))) :
    ((whole registered packetAt current).destination
      (oldEntry (law := MathLaw old registered) (state? := some current.2.state) entry)).1 =
    oldEntry (law := MathLaw old registered) (state? := some (targetCurrent registered packetAt current).2.state)
      ((originalFold (packetAt current.1)).destination entry).1 :=
  join_destination_old (packetAt current.1) current.2 entry

private theorem whole_origin_old (current : Current registered)
    (entry : OpenResponsibilityAt N
      (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted (targetCurrent registered packetAt current).1))) :
    ((whole registered packetAt current).origin
      (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent registered packetAt current).2.state) entry)).1 =
    oldEntry (law := MathLaw old registered) (state? := some current.2.state)
      ((originalFold (packetAt current.1)).origin entry).1 :=
  join_origin_old (packetAt current.1) current.2 entry

private theorem whole_destination_math (current : Current registered) :
    ((whole registered packetAt current).destination
      (debtEntry (N := N) (law := MathLaw old registered)
        (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted current.1)) current.2.state)).1 =
    debtEntry (N := N) (law := MathLaw old registered)
      (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted (targetCurrent registered packetAt current).1))
      (targetCurrent registered packetAt current).2.state :=
  join_destination_math (packetAt current.1) current.2

private theorem whole_origin_math (current : Current registered) :
    ((whole registered packetAt current).origin
      (debtEntry (N := N) (law := MathLaw old registered)
        (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted (targetCurrent registered packetAt current).1))
        (targetCurrent registered packetAt current).2.state)).1 =
    debtEntry (N := N) (law := MathLaw old registered)
      (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted current.1)) current.2.state :=
  join_origin_math (packetAt current.1) current.2

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

variable (current : (JointV registered packetAt).Current)

private theorem original_origin_eq
    (first second : OpenResponsibilityAt N
      (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted (targetCurrent registered packetAt current).1)))
    (same : ((whole registered packetAt current).origin
      (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent registered packetAt current).2.state) first)).1 =
      ((whole registered packetAt current).origin
        (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent registered packetAt current).2.state) second)).1) :
    ((originalFold (packetAt current.1)).origin first).1 = ((originalFold (packetAt current.1)).origin second).1 :=
  RootGeneratedDebtActivationJointSource.Native.oldEntry_injective
    ((whole_origin_old old registered packetAt current first).symm.trans
      (same.trans (whole_origin_old old registered packetAt current second)))

private theorem original_destination_eq
    (first second : OpenResponsibilityAt N
      (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted current.1)))
    (same : ((whole registered packetAt current).destination
      (oldEntry (law := MathLaw old registered) (state? := some current.2.state) first)).1 =
      ((whole registered packetAt current).destination
        (oldEntry (law := MathLaw old registered) (state? := some current.2.state) second)).1) :
    ((originalFold (packetAt current.1)).destination first).1 = ((originalFold (packetAt current.1)).destination second).1 :=
  RootGeneratedDebtActivationJointSource.Native.oldEntry_injective
    ((whole_destination_old old registered packetAt current first).symm.trans
      (same.trans (whole_destination_old old registered packetAt current second)))

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
  (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted (targetCurrent registered packetAt current).1)))
variable (same : ((whole registered packetAt current).origin
  (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent registered packetAt current).2.state) left)).1 =
  ((whole registered packetAt current).origin
    (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent registered packetAt current).2.state) right)).1)

def splitCoverage
    (original : SourceNativeSplitCoverageAt (originalLaw old) (old.emitted current.1)
      (originalFold (packetAt current.1)) left right (original_origin_eq old registered packetAt current left right same)) :
    SourceNativeSplitCoverageAt (law old registered packetAt) (emitted registered packetAt current)
      (whole registered packetAt current)
      (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent registered packetAt current).2.state) left)
      (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent registered packetAt current).2.state) right) same := by
  let parentEq : (law old registered packetAt).obligationAt (emitted registered packetAt current)
      ((whole registered packetAt current).origin
        (oldEntry (law := MathLaw old registered) (state? := some (targetCurrent registered packetAt current).2.state) left)).1 =
      oldObligation old registered ((originalLaw old).obligationAt (old.emitted current.1)
        ((originalFold (packetAt current.1)).origin left).1) := by
    exact congrArg ((law old registered packetAt).obligationAt (emitted registered packetAt current))
      (whole_origin_old old registered packetAt current left)
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
        have oldEq := original_origin_eq old registered packetAt current ⟨prior, opened⟩ left targetEq
        dsimp only [receipt]
        rw [castSplit_children]
        exact List.mem_map_of_mem (f := oldObligation old registered) (original.covers_target ⟨prior, opened⟩ oldEq)
    | inr debt =>
        rcases opened with ⟨⟨idEq⟩⟩
        cases idEq
        have incompatible := (whole_origin_math old registered packetAt current).symm.trans
          (targetEq.trans (whole_origin_old old registered packetAt current left))
        exact nomatch congrArg Sigma.fst incompatible
  · intro target targetEq
    rcases target with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior =>
        have budgets := congrArg OpenResponsibilityAt.progressBudget
          (whole_origin_old old registered packetAt current left)
        exact lt_of_lt_of_eq (original.childProgressBudget_strictlyDebited ⟨prior, opened⟩
          (original_origin_eq old registered packetAt current ⟨prior, opened⟩ left targetEq)) budgets.symm
    | inr debt =>
        rcases opened with ⟨⟨idEq⟩⟩
        cases idEq
        have incompatible := (whole_origin_math old registered packetAt current).symm.trans
          (targetEq.trans (whole_origin_old old registered packetAt current left))
        exact nomatch congrArg Sigma.fst incompatible
  · intro child member
    have mapped : child ∈ original.receipt.children.map (oldObligation old registered) := by
      dsimp only [receipt] at member
      rw [castSplit_children] at member
      exact member
    let prior := oldMember old registered original.receipt.children child mapped
    let target := original.no_phantom_child prior.val prior.property.1
    refine ⟨oldEntry (law := MathLaw old registered)
      (state? := some (targetCurrent registered packetAt current).2.state) target.val, ?_, ?_⟩
    · exact (congrArg (oldObligation old registered) target.property.1).trans prior.property.2
    · exact (whole_origin_old old registered packetAt current target.val).trans
        ((congrArg (oldEntry (law := MathLaw old registered) (state? := some current.2.state)) target.property.2).trans
          (whole_origin_old old registered packetAt current left).symm)

omit left right same in
 def mergeCoverage
    (left right : OpenResponsibilityAt N (old.toLedgerRoot.source.source.toRootSource.account.supportOf (old.emitted current.1)))
    (same : ((whole registered packetAt current).destination
      (oldEntry (law := MathLaw old registered) (state? := some current.2.state) left)).1 =
      ((whole registered packetAt current).destination
        (oldEntry (law := MathLaw old registered) (state? := some current.2.state) right)).1)
    (original : SourceNativeMergeCoverageAt (originalLaw old) (old.emitted current.1)
      (originalFold (packetAt current.1)) left right (original_destination_eq old registered packetAt current left right same)) :
    SourceNativeMergeCoverageAt (law old registered packetAt) (emitted registered packetAt current)
      (whole registered packetAt current)
      (oldEntry (law := MathLaw old registered) (state? := some current.2.state) left)
      (oldEntry (law := MathLaw old registered) (state? := some current.2.state) right) same := by
  let receipt := mergeReceipt old registered original.receipt
  refine SourceNativeMergeCoverageAt.ofReceipt receipt ?_ ?_ ?_ ?_ ?_ ?_
  · exact congrArg Sum.inl original.sourceEvent_eq
  · exact (congrArg (oldObligation old registered) original.target_eq).trans
      (congrArg ((law old registered packetAt).obligationAt (emitted registered packetAt current))
        (whole_destination_old old registered packetAt current left)).symm
  · exact List.mem_map_of_mem (f := oldObligation old registered) original.left_member
  · exact List.mem_map_of_mem (f := oldObligation old registered) original.right_member
  · intro source sourceEq
    rcases source with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior =>
        exact List.mem_map_of_mem (f := oldObligation old registered) (original.covers_source ⟨prior, opened⟩
          (original_destination_eq old registered packetAt current ⟨prior, opened⟩ left sourceEq))
    | inr debt =>
        rcases opened with ⟨⟨idEq⟩⟩
        cases idEq
        have incompatible := (whole_destination_math old registered packetAt current).symm.trans
          (sourceEq.trans (whole_destination_old old registered packetAt current left))
        exact nomatch congrArg Sigma.fst incompatible
  · intro parent member
    let prior := oldMember old registered original.receipt.parents parent member
    let source := original.no_phantom_parent prior.val prior.property.1
    refine ⟨oldEntry (law := MathLaw old registered) (state? := some current.2.state) source.val, ?_, ?_⟩
    · exact (congrArg (oldObligation old registered) source.property.1).trans prior.property.2
    · exact (whole_destination_old old registered packetAt current source.val).trans
        ((congrArg (oldEntry (law := MathLaw old registered)
          (state? := some (targetCurrent registered packetAt current).2.state)) source.property.2).trans
            (whole_destination_old old registered packetAt current left).symm)


omit left right same in
def wholeCertificate : ExactLedgerRestructuringCertificationAt (law old registered packetAt)
    (emitted registered packetAt current) (whole registered packetAt current) where
  split := by
    rintro ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            let oldSame := original_origin_eq old registered packetAt current ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same
            cases (foldCertificate old registered packetAt current).split ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ oldSame with
            | identity equality =>
                exact .identity (congrArg (oldEntry (law := MathLaw old registered)
                  (state? := some (targetCurrent registered packetAt current).2.state)) equality)
            | split original =>
                exact .split (splitCoverage old registered packetAt current ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same original)
        | inr debt =>
            rcases secondOpen with ⟨⟨idEq⟩⟩
            cases idEq
            have incompatible := (whole_origin_old old registered packetAt current ⟨first, firstOpen⟩).symm.trans
              (same.trans (whole_origin_math old registered packetAt current))
            exact nomatch congrArg Sigma.fst incompatible
    | inr debt =>
        rcases firstOpen with ⟨⟨idEq⟩⟩
        cases idEq
        cases second with
        | inl second =>
            have incompatible := (whole_origin_math old registered packetAt current).symm.trans
              (same.trans (whole_origin_old old registered packetAt current ⟨second, secondOpen⟩))
            exact nomatch congrArg Sigma.fst incompatible
        | inr second => rcases secondOpen with ⟨⟨idEq⟩⟩; cases idEq; exact .identity rfl
  merge := by
    rintro ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            let oldSame := original_destination_eq old registered packetAt current ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same
            cases (foldCertificate old registered packetAt current).merge ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ oldSame with
            | identity equality =>
                exact .identity (congrArg (oldEntry (law := MathLaw old registered) (state? := some current.2.state)) equality)
            | merge original =>
                exact .merge (mergeCoverage old registered packetAt current ⟨first, firstOpen⟩ ⟨second, secondOpen⟩ same original)
        | inr debt =>
            rcases secondOpen with ⟨⟨idEq⟩⟩
            cases idEq
            have incompatible := (whole_destination_old old registered packetAt current ⟨first, firstOpen⟩).symm.trans
              (same.trans (whole_destination_math old registered packetAt current))
            exact nomatch congrArg Sigma.fst incompatible
    | inr debt =>
        rcases firstOpen with ⟨⟨idEq⟩⟩
        cases idEq
        cases second with
        | inl second =>
            have incompatible := (whole_destination_math old registered packetAt current).symm.trans
              (same.trans (whole_destination_old old registered packetAt current ⟨second, secondOpen⟩))
            exact nomatch congrArg Sigma.fst incompatible
        | inr second => rcases secondOpen with ⟨⟨idEq⟩⟩; cases idEq; exact .identity rfl


/-- The actual finite row plus generated remainder has the same complete write. -/
def certificate (current : Current registered) :
    ExactLedgerRestructuringCertificationAt (law old registered packetAt)
      (emitted registered packetAt current) (patch registered packetAt current).toLedgerWriteEvolution := by
  rw [patch_fold]
  exact wholeCertificate old registered packetAt current

end RootGeneratedDebtActivationJointSource.Successor.Restructuring
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
