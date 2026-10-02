import H0mework.Foundation.Responsibility.JointSource.Native.Readback
/-! The source's actual paid branch makes the canonical complete patch and
its existing joint payer agree on every full Sigma receipt. Proof-dependent
endpoint transports preserve the data and commute with the paired action. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native
open SourceOperationEffects DebtActivationWorld DebtActivationLedger
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (program : Program lower)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)
private theorem mpr_heq {A B : Sort (u + 1)} (same : A = B) (value : B) :
    HEq (Eq.mpr same value) value := by cases same; rfl

private theorem sum_right {L R C : Type u} (selected : L ⊕ R)
    (left : (value : L) → selected = .inl value → C)
    (right : (value : R) → selected = .inr value → C)
    (value : R) (same : selected = .inr value) :
    Sum.rec (motive := fun output => selected = output → C) left right selected rfl = right value same := by
  cases same
  rfl

private theorem old_paid (current : Current registered)
    (paid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) current.2.state)
    (action : mathAction current.2 = .inr paid)
    (index : Fin (oldRows program registered current).size) :
    HEq (oldRowEvolution program registered current index)
      (jointOldEvolution (law := Idle.law registered.input.environment registered.input.expression)
        paid.2 ((oldRows program registered current).rowAt index).evolution) := by
  unfold oldRowEvolution
  refine HEq.trans (mpr_heq _ _) ?_
  refine HEq.trans (heq_of_eq (sum_right _ _ _ paid action)) ?_
  dsimp only
  exact eqRec_heq_iff.mpr HEq.rfl
private theorem math_paid (current : Current registered)
    (paid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) current.2.state)
    (action : mathAction current.2 = .inr paid) :
    HEq (mathRowEvolution program registered current)
      (.transferred (debtStepReceipt (law := Idle.law registered.input.environment registered.input.expression)
          (lower.source.source.toRootSource.account.supportOf (lower.emitted current.1)) paid.2)
        ((native program registered current).baseLedger.destination current.2.owner).2.toDebtLineage.lineage_eq rfl
        (Nat.le_of_lt ((Idle.law registered.input.environment registered.input.expression).step_budget_lt paid.2)) :
        LedgerEntryEvolutionAt (World registered) (mathSource registered current)
          (debtEntry (N := N) (law := Idle.law registered.input.environment registered.input.expression)
            (lower.source.source.toRootSource.account.supportOf (native program registered current).targetOccurrence) paid.1)) := by
  unfold mathRowEvolution
  refine HEq.trans (mpr_heq _ _) ?_
  refine HEq.trans (mpr_heq _ _) ?_
  refine HEq.trans (heq_of_eq (sum_right _ _ _ paid action)) ?_
  dsimp only
  exact eqRec_heq_iff.mpr HEq.rfl

private theorem row_old (current : Current registered) (index : Fin (oldRows program registered current).size) :
    HEq (rowEvolution program registered current index.castSucc) (oldRowEvolution program registered current index) := by
  unfold rowEvolution
  refine HEq.trans (heq_of_eq (Fin.lastCases_castSucc index)) ?_
  exact mpr_heq _ _

private theorem row_math (current : Current registered) :
    HEq (rowEvolution program registered current (Fin.last _)) (mathRowEvolution program registered current) := by
  unfold rowEvolution
  refine HEq.trans (heq_of_eq Fin.lastCases_last) ?_
  exact mpr_heq _ _

private theorem sigma_heq {W : WorldRelationNetwork.{u}}
    {sourceTarget leftTarget rightTarget : W.Support} {source : OpenResponsibilityAt W sourceTarget}
    {left : Σ target : OpenResponsibilityAt W leftTarget, LedgerEntryEvolutionAt W source target}
    {right : Σ target : OpenResponsibilityAt W rightTarget, LedgerEntryEvolutionAt W source target}
    (same : leftTarget = rightTarget) (entries : HEq left.1 right.1) (receipts : HEq left.2 right.2) :
    HEq left right := by
  cases same
  exact heq_of_eq (Sigma.ext (eq_of_heq entries) receipts)

private theorem old_state_heq {W : WorldRelationNetwork.{u}} {scope : DebtActivationLaw.{u}}
    {support : W.Support} {first second : scope.DebtState}
    (same : first = second) (entry : OpenResponsibilityAt W support) :
    HEq (oldEntry (law := scope) (state? := some first) entry)
      (oldEntry (law := scope) (state? := some second) entry) := by
  cases same
  rfl

private theorem debt_state_heq {W : WorldRelationNetwork.{u}} {scope : DebtActivationLaw.{u}}
    {support : W.Support} {first second : scope.DebtState} (same : first = second) :
    HEq (debtEntry (N := W) (law := scope) support first)
      (debtEntry (N := W) (law := scope) support second) := by cases same; rfl

private theorem debt_transfer_heq {W : WorldRelationNetwork.{u}} {scope : DebtActivationLaw.{u}}
    {sourceSupport leftTarget rightTarget : W.Support} {source target : scope.DebtState}
    (same : leftTarget = rightTarget)
    (receipt : (ExtendedNetwork W scope).DispositionAt (sourceSupport, some source) .transfer)
    (leftLineage : W.lineageAt sourceSupport = W.lineageAt leftTarget)
    (rightLineage : W.lineageAt sourceSupport = W.lineageAt rightTarget)
    (budget : scope.budget target ≤ scope.budget source) :
    HEq (.transferred receipt leftLineage rfl budget : LedgerEntryEvolutionAt (ExtendedNetwork W scope)
      (debtEntry (N := W) (law := scope) sourceSupport source) (debtEntry (N := W) (law := scope) leftTarget target))
      (.transferred receipt rightLineage rfl budget : LedgerEntryEvolutionAt (ExtendedNetwork W scope)
      (debtEntry (N := W) (law := scope) sourceSupport source) (debtEntry (N := W) (law := scope) rightTarget target)) := by
  cases same
  rfl

private theorem next_paid (current : Current registered)
    (paid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) current.2.state)
    (action : mathAction current.2 = .inr paid) :
    (targetCurrent program registered current).2.state = paid.1 := by
  exact (native program registered current).next_state.trans (by
    unfold mathTarget
    rw [action])

private theorem source_cast {W : WorldRelationNetwork.{u}} {scope : DebtActivationLaw.{u}}
    {sourceSupport targetSupport : W.Support} {source target : scope.DebtState}
    {selected actual : OpenResponsibilityAt W sourceSupport} {next : OpenResponsibilityAt W targetSupport}
    (step : scope.StepAt source target) (same : selected = actual)
    (receipt : LedgerEntryEvolutionAt W selected next) :
    HEq
      (Eq.mp (congrArg (fun entry => LedgerEntryEvolutionAt (ExtendedNetwork W scope)
        (oldEntry (law := scope) (state? := some source) entry)
        (oldEntry (law := scope) (state? := some target) next)) same)
        (jointOldEvolution step receipt))
      (jointOldEvolution step
        (Eq.mp (congrArg (fun entry => LedgerEntryEvolutionAt W entry next) same) receipt)) := by
  cases same
  rfl

private theorem paid_old_fold (current : Current registered)
    (paid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) current.2.state)
    (action : mathAction current.2 = .inr paid) :
    HEq (patch program registered current).toLedgerWriteEvolution.destination
      (jointStepLedgerEvolution (law := Idle.law registered.input.environment registered.input.expression)
        (oldFold program registered current) current.2.owner paid.2).destination := by
  have targetEq : supportAt registered (targetCurrent program registered current) =
      (lower.source.source.toRootSource.account.supportOf (lower.emitted (targetCurrent program registered current).1), some paid.1) :=
    congrArg (fun state : SourceOperationExecutionDebt.State registered.input.environment registered.input.expression =>
      (lower.source.source.toRootSource.account.supportOf (lower.emitted (targetCurrent program registered current).1), some state))
      (next_paid program registered current paid action)
  apply Function.hfunext rfl
  intro left right same
  cases same
  rcases left with ⟨responsibility, opened⟩
  cases responsibility with
  | inl old =>
      let entry : OpenResponsibilityAt N (lower.source.source.toRootSource.account.supportOf (lower.emitted current.1)) :=
        ⟨old, opened⟩
      change HEq ((patch program registered current).toLedgerWriteEvolution.destination
        (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
          (state? := some current.2.state) entry)) _
      apply sigma_heq targetEq
      · exact (heq_of_eq (patch_destination_old program registered current entry)).trans
          (old_state_heq (scope := Idle.law registered.input.environment registered.input.expression)
            (W := N) (next_paid program registered current paid action) _)
      · unfold patch FiniteGeneratedLedgerWritePatchAt.toLedgerWriteEvolution
        simp only [FiniteGeneratedLedgerWritePatchAt.completeEvolution, coverage, rows]
        change HEq (Eq.mp _ (rowEvolution program registered current
          ((oldCoverage program registered current).destinationIndex entry).castSucc))
          (jointOldEvolution (law := Idle.law registered.input.environment registered.input.expression)
            paid.2 ((oldFold program registered current).destination entry).2)
        refine HEq.trans (eqRec_heq_iff.mpr ((row_old program registered current _).trans
          (old_paid program registered current paid action _))) ?_
        have moved := source_cast (W := N)
          (scope := Idle.law registered.input.environment registered.input.expression) paid.2
          ((oldCoverage program registered current).destination_sound entry)
          ((oldRows program registered current).rowAt ((oldCoverage program registered current).destinationIndex entry)).evolution
        exact (eqRec_heq_iff.mpr HEq.rfl).symm.trans moved
  | inr debt =>
      rcases opened with ⟨⟨equal⟩⟩
      subst debt
      change HEq ((patch program registered current).toLedgerWriteEvolution.destination (mathSource registered current)) _
      apply sigma_heq targetEq
      · exact heq_of_eq (patch_destination_math program registered current) |>.trans (by
          unfold mathTargetEntry
          exact debt_state_heq (W := N) (scope := Idle.law registered.input.environment registered.input.expression)
            (next_paid program registered current paid action))
      · change HEq (Eq.mp _ (rowEvolution program registered current (Fin.last _))) _
        refine HEq.trans (eqRec_heq_iff.mpr ((row_math program registered current).trans
          (math_paid program registered current paid action))) ?_
        exact debt_transfer_heq (W := N) (scope := Idle.law registered.input.environment registered.input.expression)
          (congrArg (lower.source.source.toRootSource.account.supportOf)
            (native program registered current).target_emitted) _ _ _ _

private theorem cast_packet_fold {current next : V.Current}
    {target actual : lower.source.source.toRootSource.actual.OccurrenceAt next}
    (same : target = actual)
    (packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
      (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf target⟩,
      LedgerCompleteFiniteCoverageAt rows) :
    HEq ((FiniteGeneratedLedgerWritePatchAt.complete
      ((same ▸ packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
        (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf actual⟩,
        LedgerCompleteFiniteCoverageAt rows).1)
      ((same ▸ packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
        (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf actual⟩,
        LedgerCompleteFiniteCoverageAt rows).2)).toLedgerWriteEvolution)
      ((FiniteGeneratedLedgerWritePatchAt.complete packet.1 packet.2).toLedgerWriteEvolution) := by
  cases same
  rfl

private theorem oldFold_native (current : Current registered) :
    HEq (oldFold program registered current) (native program registered current).baseLedger :=
  (cast_packet_fold (image_target program registered current)
    ⟨(program.emit current.1).rows, (program.emit current.1).coverage⟩).trans
    (heq_of_eq (program.emit current.1).fold_eq)

private theorem joint_destination_base {W : WorldRelationNetwork.{u}} {scope : DebtActivationLaw.{u}}
    {sourceSupport firstTarget secondTarget : W.Support} {source target : scope.DebtState}
    {first : LedgerWriteEvolutionAt W ⟨sourceSupport⟩ ⟨firstTarget⟩}
    {second : LedgerWriteEvolutionAt W ⟨sourceSupport⟩ ⟨secondTarget⟩}
    (same : firstTarget = secondTarget) (receipts : HEq first second)
    (owner : OpenResponsibilityAt W sourceSupport) (step : scope.StepAt source target) :
    HEq (jointStepLedgerEvolution first owner step).destination
      (jointStepLedgerEvolution second owner step).destination := by
  cases same
  cases eq_of_heq receipts
  rfl

theorem paid_destination (current : Current registered)
    (paid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) current.2.state)
    (action : mathAction current.2 = .inr paid) :
    HEq (patch program registered current).toLedgerWriteEvolution.destination
      (jointStepLedgerEvolution (law := Idle.law registered.input.environment registered.input.expression)
        (native program registered current).baseLedger current.2.owner paid.2).destination :=
  (paid_old_fold program registered current paid action).trans
    (joint_destination_base
      (congrArg (lower.source.source.toRootSource.account.supportOf)
        (native program registered current).target_emitted.symm)
      (oldFold_native program registered current) current.2.owner paid.2)

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
