import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.PairInventoryCoverage.Address

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.PaidStepDependentCutGate

open CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceOperationScalarInventoryLift

universe u

namespace A
export Cursor.Native.Feed.PairAccumulation (writtenCount earlier_birth_iff)
end A
namespace B
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Births (birthIndex_strictMono)
end B
namespace C
export Cursor.Native.Feed.Continuation.Source (continuous)
end C
namespace F
export Cursor.Native.Feed.Source (dynamicFeed)
end F
namespace H
export Cursor.Native.Feed.PairHistory (PairExposure expose birthWrite birthReceipt)
end H
namespace P
export SourceOperationPaidRelations (words events events_trace exposure stepOccurrence
  stepOccurrence_before_length AtStep ReadStep paidCut paidCut_word)
end P
namespace S
export Cursor.Native.Feed.Continuation.Actor.Source (birth)
end S
namespace V
export Cursor.Native.Feed.PairInventoryCoverage
  (anchor birthTraces actual_full_trace originalTrace PairRelationAt originalStepAt
    OriginalStepAt.cut)
end V
namespace W
export SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence (transport_position)
end W

private theorem birth_order (depth count : Nat) : StrictMono (S.birth depth count) :=
  B.birthIndex_strictMono (C.continuous depth count) (F.dynamicFeed depth count)

private abbrev stageTwo (depth count : Nat) : Nat := S.birth depth count 1 + 1

private def retainedTwo (depth count : Nat) : H.PairExposure depth count (stageTwo depth count) :=
  H.expose depth count _ (Nat.succ_le_succ ((birth_order depth count).monotone (by decide : 0 ≤ 1)))

attribute [local irreducible] retainedTwo

private theorem twoWritten (depth count : Nat) : A.writtenCount depth count (stageTwo depth count) = 2 := by
  have second := (A.earlier_birth_iff depth count (stageTwo depth count) 1).mp le_rfl
  have rise := birth_order depth count (by decide : 1 < 2)
  have noThird : ¬ 2 < A.writtenCount depth count (stageTwo depth count) := by
    intro third
    have past : S.birth depth count 2 + 1 ≤ S.birth depth count 1 + 1 :=
      (A.earlier_birth_iff depth count (stageTwo depth count) 2).mpr third
    omega
  omega

private theorem prefixOne (depth count : Nat) :
    V.birthTraces depth count 1 = (H.birthWrite depth count 0).trace := by
  simp only [V.birthTraces, List.nil_append]

private theorem twoTrace (depth count : Nat) :
    (retainedTwo depth count).stored.trace = [V.anchor depth count] ++
      ((H.birthWrite depth count 0).trace ++ (H.birthWrite depth count 1).trace) := by
  have full := (V.actual_full_trace (retainedTwo depth count)).2.2
  have reindex := congrArg
    (fun n : Nat => List.replicate (n - 1) (V.anchor depth count) ++ V.birthTraces depth count n)
    (twoWritten depth count)
  have blocks : V.birthTraces depth count 2 =
      (H.birthWrite depth count 0).trace ++ (H.birthWrite depth count 1).trace := by
    simp only [V.birthTraces, List.nil_append]
  exact full.trans (reindex.trans (congrArg ([V.anchor depth count] ++ ·) blocks))

private def firstSegment (depth count : Nat) :
    SourceInventoryTraceSegment (H.birthWrite depth count 0) (retainedTwo depth count).stored :=
  ⟨[V.anchor depth count], (H.birthWrite depth count 1).trace,
    by simpa only [List.append_assoc] using twoTrace depth count⟩

private def secondSegment (depth count : Nat) :
    SourceInventoryTraceSegment (H.birthWrite depth count 1) (retainedTwo depth count).stored :=
  ⟨[V.anchor depth count] ++ (H.birthWrite depth count 0).trace, [],
    by simpa only [List.append_nil, List.append_assoc] using twoTrace depth count⟩

private abbrev StepIndex (depth count ordinal : Nat) :=
  Fin (P.words (V.originalTrace depth count ordinal)).length

set_option backward.isDefEq.respectTransparency false in
private def firstOccurrence (depth count : Nat) (index : StepIndex depth count 0) :
    V.PairRelationAt (depth := depth) (count := count) (retainedTwo depth count).stored :=
  (P.stepOccurrence (V.originalTrace depth count 0) index).transport (firstSegment depth count)

set_option backward.isDefEq.respectTransparency false in
private def secondOccurrence (depth count : Nat) (index : StepIndex depth count 1) :
    V.PairRelationAt (depth := depth) (count := count) (retainedTwo depth count).stored :=
  (P.stepOccurrence (V.originalTrace depth count 1) index).transport (secondSegment depth count)

set_option backward.isDefEq.respectTransparency false in
private theorem firstAddress (depth count : Nat) (index : StepIndex depth count 0) :
    (firstOccurrence depth count index).before.length =
      1 + (V.birthTraces depth count 0).length + (1 + index.val) := by
  let trace := V.originalTrace depth count 0
  let segment := firstSegment depth count
  exact (W.transport_position (P.stepOccurrence trace index) segment).trans
    (congrArg (fun slot : Nat => segment.before.length + slot) (P.stepOccurrence_before_length trace index))

set_option backward.isDefEq.respectTransparency false in
private theorem secondAddress (depth count : Nat) (index : StepIndex depth count 1) :
    (secondOccurrence depth count index).before.length =
      1 + (V.birthTraces depth count 1).length + (1 + index.val) := by
  let trace := V.originalTrace depth count 1
  let segment := secondSegment depth count
  have offset := (W.transport_position (P.stepOccurrence trace index) segment).trans
    (congrArg (fun slot : Nat => segment.before.length + slot) (P.stepOccurrence_before_length trace index))
  have before : segment.before.length = 1 + (V.birthTraces depth count 1).length := by
    change ([V.anchor depth count] ++ (H.birthWrite depth count 0).trace).length = _
    rw [List.length_append, List.length_singleton, prefixOne]
  exact offset.trans (congrArg (fun start : Nat => start + (1 + index.val)) before)

private theorem exposureLength {T : Type u} {Value Var : T → Type u}
    [∀ target, AddCommGroup (Value target)] {s : T} {environment : Env Value Var}
    {raw last : Expr Value Var s} (trace : Trace environment raw last) :
    (P.exposure trace).trace.length = 1 + (P.words trace).length := by
  change (PresentedRelationEventAt.generator raw :: RootedAccountedUnfolding.traceBranches (P.events trace)).length = _
  simp only [P.events_trace, List.length_cons, List.length_map, Nat.add_comm]

set_option backward.isDefEq.respectTransparency false in
private theorem firstBirthLength (depth count : Nat) :
    (H.birthWrite depth count 0).trace.length =
      1 + (P.words (V.originalTrace depth count 0)).length :=
  exposureLength (V.originalTrace depth count 0)

private theorem sameTwoBlockAddress (prefixSize width : Nat → Nat)
    (zeroPrefix : prefixSize 0 = 0) (onePrefix : prefixSize 1 = 1 + width 0)
    {birth actual index read : Nat} (old : birth < 2) (selected : actual < 2)
    (inside : index < width birth) (actualInside : read < width actual)
    (position : 1 + prefixSize birth + (1 + index) = 1 + prefixSize actual + (1 + read)) :
    actual = birth ∧ read = index := by
  have olds : birth = 0 ∨ birth = 1 := by omega
  have actuals : actual = 0 ∨ actual = 1 := by omega
  rcases olds with oldZero | oldOne <;> rcases actuals with actualZero | actualOne
  · have oldHead := (congrArg prefixSize oldZero).trans zeroPrefix
    have actualHead := (congrArg prefixSize actualZero).trans zeroPrefix
    exact ⟨actualZero.trans oldZero.symm, by omega⟩
  · have oldHead := (congrArg prefixSize oldZero).trans zeroPrefix
    have actualHead := (congrArg prefixSize actualOne).trans onePrefix
    have widthBound := inside.trans_le (congrArg width oldZero).le
    omega
  · have oldHead := (congrArg prefixSize oldOne).trans onePrefix
    have actualHead := (congrArg prefixSize actualZero).trans zeroPrefix
    have widthBound := actualInside.trans_le (congrArg width actualZero).le
    omega
  · have oldHead := (congrArg prefixSize oldOne).trans onePrefix
    have actualHead := (congrArg prefixSize actualOne).trans onePrefix
    exact ⟨actualOne.trans oldOne.symm, by omega⟩

private def TypedCut {T : Type u} {Value Var : T → Type u}
    [∀ target, AddCommGroup (Value target)] {s : T} {environment : Env Value Var}
    {raw last : Expr Value Var s} (trace : Trace environment raw last) (slot : Nat)
    (word : Formal ℤ Value Var s) (cut : P.AtStep trace slot) : Prop :=
  cut.past.length = slot ∧ cut.past.append (.cons cut.step cut.future) = trace ∧
    word = relation (R := ℤ) environment (.inl ⟨cut.entry, cut.exit, cut.step.toDerivation⟩)

private theorem paidCutAccepted {T : Type u} {Value Var : T → Type u}
    [∀ target, AddCommGroup (Value target)] {s : T} {environment : Env Value Var}
    {raw last : Expr Value Var s} (trace : Trace environment raw last) {position : Nat}
    {word : Formal ℤ Value Var s} (selected : P.ReadStep trace position word) :
    TypedCut trace selected.index.val word (P.paidCut trace selected.index) :=
  ⟨(P.paidCut trace selected.index).position_eq, (P.paidCut trace selected.index).trace_eq,
    selected.word_eq.symm.trans (P.paidCut_word trace selected.index)⟩

attribute [local irreducible] V.originalTrace V.originalStepAt

set_option backward.isDefEq.respectTransparency false in
private def CutAccepted {depth count stage : Nat} (retained : H.PairExposure depth count stage)
    (event : V.PairRelationAt (depth := depth) (count := count) retained.stored)
    (birth index : Nat) : Prop :=
  let located := @V.originalStepAt depth count stage retained event
  let cut := @V.OriginalStepAt.cut depth count stage retained event located
  located.birth.val = birth ∧ located.selected.index.val = index ∧
    TypedCut (V.originalTrace depth count located.birth.val) located.selected.index.val event.word cut

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
private theorem acceptCut {depth count stage : Nat} (retained : H.PairExposure depth count stage)
    (event : V.PairRelationAt (depth := depth) (count := count) retained.stored)
    (two : A.writtenCount depth count stage = 2) {birth : Nat} (old : birth < 2)
    (index : StepIndex depth count birth)
    (address : event.before.length = 1 + (V.birthTraces depth count birth).length + (1 + index.val)) :
    CutAccepted retained event birth index.val := by
  let located := @V.originalStepAt depth count stage retained event
  let prefixSize (ordinal : Nat) := (V.birthTraces depth count ordinal).length
  let width (ordinal : Nat) := (P.words (V.originalTrace depth count ordinal)).length
  have zeroPrefix : prefixSize 0 = 0 := rfl
  have onePrefix : prefixSize 1 = 1 + width 0 :=
    (congrArg List.length (prefixOne depth count)).trans (firstBirthLength depth count)
  have past : located.birth.val < 2 := located.birth.isLt.trans_le two.le
  have spine : A.writtenCount depth count stage - 1 = 1 := by rw [two]
  have actualAddress := located.offset_eq.trans (congrArg
    (fun slot : Nat => (A.writtenCount depth count stage - 1) + prefixSize located.birth.val + slot)
    located.selected.position_eq)
  have same : 1 + prefixSize birth + (1 + index.val) =
      1 + prefixSize located.birth.val + (1 + located.selected.index.val) :=
    address.symm.trans (actualAddress.trans (congrArg
      (fun head : Nat => head + prefixSize located.birth.val + (1 + located.selected.index.val)) spine))
  obtain ⟨born, step⟩ :=
    sameTwoBlockAddress prefixSize width zeroPrefix onePrefix old past index.isLt located.selected.index.isLt same
  exact ⟨born, step, paidCutAccepted (V.originalTrace depth count located.birth.val) located.selected⟩

set_option cleanup.letToHave false in
/-- Both actual steps use the original two birth blocks and retain their typed cuts. -/
theorem two_actual_paid_cuts (depth count : Nat)
    (first : StepIndex depth count 0) (second : StepIndex depth count 1) :
    CutAccepted (retainedTwo depth count) (firstOccurrence depth count first) 0 first.val ∧
    CutAccepted (retainedTwo depth count) (secondOccurrence depth count second) 1 second.val :=
  ⟨acceptCut (retainedTwo depth count) (firstOccurrence depth count first) (twoWritten depth count)
      (by decide : 0 < 2) first (firstAddress depth count first),
    acceptCut (retainedTwo depth count) (secondOccurrence depth count second) (twoWritten depth count)
      (by decide : 1 < 2) second (secondAddress depth count second)⟩

run_cmd IO.eprintln "CP528_CONTROL + two_actual_paid_cuts"

set_option cleanup.letToHave false in
/-- The actual generator at slot zero is excluded from the relation address domain. -/
theorem actual_anchor_has_no_relation_address (depth count : Nat) :
    let retained := retainedTwo depth count
    retained.stored.trace[0]? = some (V.anchor depth count) ∧
    ¬ ∃ event : V.PairRelationAt (depth := depth) (count := count) retained.stored, event.before.length = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [twoTrace, List.singleton_append, List.getElem?_cons_zero]
  · rintro ⟨event, atAnchor⟩
    let located := @V.originalStepAt depth count (stageTwo depth count) (retainedTwo depth count) event
    have actualAddress : event.before.length = (A.writtenCount depth count (stageTwo depth count) - 1) +
        (V.birthTraces depth count located.birth.val).length + located.localIndex := located.offset_eq
    have stepAddress := located.selected.position_eq
    have spine : A.writtenCount depth count (stageTwo depth count) - 1 = 1 := by rw [twoWritten]
    omega

run_cmd IO.eprintln "CP528_CONTROL - actual_anchor_has_no_relation_address"

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.PaidStepDependentCutGate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
