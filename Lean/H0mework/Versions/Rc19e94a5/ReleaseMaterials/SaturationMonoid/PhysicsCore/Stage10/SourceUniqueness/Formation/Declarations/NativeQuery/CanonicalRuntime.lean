import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.ReceiptReadback
import H0mework.Foundation.Runtime.Activation

/-!
# Canonical micro runtime of the original duration inquiry root

Every process state is the old `MotherNativeQuery.visitAt`; its successor is
that visit's existing generated next. The facade inventories every query
projection already installed in the old declaration source. The law is fixed
before the process is created, and no runtime state or answer is caller-made.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

def visitDepth? (current : SourceNativeLivingRootCurrentAt N) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

def finiteVisit (law : MotherPhysicalLaws.Law) :
    Nat → RootVisit (livingRoot law).toAuthoritativeRoot.toRoot
  | 0 => (livingRoot law).toAuthoritativeRoot.toRoot.initialVisit
  | depth + 1 => (finiteVisit law depth).next rfl

theorem visitAt_eq_finite (law : MotherPhysicalLaws.Law) (depth : Nat) :
    visitAt law depth = SourceNativeTemporalVisitAt.finite (finiteVisit law depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change (visitAt law depth).next rfl =
        (SourceNativeTemporalVisitAt.finite (finiteVisit law depth)).next rfl
      rw [ih]

theorem visitAt_depth (law : MotherPhysicalLaws.Law) (depth : Nat) :
    visitDepth? ⟨V, livingRoot law, visitAt law depth⟩ = some depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [visitAt_eq_finite]
      change some (ProductiveFiniteRootHistoryAt.causalDepth
        (finiteVisit law depth).history + 1) = some (depth + 1)
      have previous :
          ProductiveFiniteRootHistoryAt.causalDepth
            (finiteVisit law depth).history = depth := by
        rw [visitAt_eq_finite] at ih
        change some (ProductiveFiniteRootHistoryAt.causalDepth
          (finiteVisit law depth).history) = some depth at ih
        exact Option.some.inj ih
      rw [previous]

def process (law : MotherPhysicalLaws.Law) : SourceNativeLivingRootProcess N where
  State := Nat
  stateAt := fun depth => ⟨V, livingRoot law, visitAt law depth⟩
  stateAt_injective := by
    intro left right same
    have depths := congrArg visitDepth? same
    rw [visitAt_depth law left, visitAt_depth law right] at depths
    exact Option.some.inj depths
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

def facade (law : MotherPhysicalLaws.Law) : SourceNativeLivingRuntimeFacade N where
  process := process law
  FaceAt := fun runtime => QueryAt law runtime.state
  componentAt := fun _ _ => projectionLaw law
  installationAt := fun _ _ => queryInstallation law
  projectionAt := fun runtime query =>
    (⟨anchorAt law runtime.state, query⟩, 0)

def seed (law : MotherPhysicalLaws.Law) : LivingRuntimeState (process law) :=
  (facade law).seed

def runtimeAt (law : MotherPhysicalLaws.Law) (depth : Nat) :
    LivingRuntimeState (process law) :=
  (seed law).advance depth

theorem runtimeAt_state (law : MotherPhysicalLaws.Law) (depth : Nat) :
    (runtimeAt law depth).state = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change Nat.succ (runtimeAt law depth).state = Nat.succ depth
      exact congrArg Nat.succ ih

theorem runtimeAt_original_visit (law : MotherPhysicalLaws.Law) (depth : Nat) :
    (runtimeAt law depth).current.visit = visitAt law depth := by
  change visitAt law (runtimeAt law depth).state = visitAt law depth
  rw [runtimeAt_state]

theorem runtimeAt_tick_original_next (law : MotherPhysicalLaws.Law) (depth : Nat) :
    (runtimeAt law depth).tick.nextCurrent =
      (process law).stateAt (depth + 1) := by
  have nextState : (process law).successor (runtimeAt law depth).state = depth + 1 := by
    change Nat.succ (runtimeAt law depth).state = Nat.succ depth
    exact congrArg Nat.succ (runtimeAt_state law depth)
  rw [LivingRuntimeState.tick_nextCurrent_eq]
  rw [nextState]

theorem runtime_readout_original_projection
    (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law))
    (query : QueryAt law runtime.state) :
    HEq ((facade law).readoutAt runtime query)
      ((projectionLaw law).outcomeAt
        (⟨anchorAt law runtime.state, query⟩, 0)
        (anchorAt law runtime.state).2) := HEq.rfl

theorem runtime_other_anchor_inactive
    (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law))
    (key : Key law) (tag : Fin 3)
    (different : key.1 ≠ anchorAt law runtime.state) :
    (projectionLaw law).classify (key, tag) runtime.emittedOccurrence =
      .inr ⟨different⟩ :=
  other_anchor_inactive law key tag
    (current := runtime.current.visit.current)
    (occurrence := runtime.emittedOccurrence) different

theorem runtime_receipt_inquiry_consumer
    (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law))
    (query : QueryAt law runtime.state)
    (generator : MotherPhysicalSource.Generator) (coefficient : ℤ) :
    let depth := runtime.state
    let anchor := anchorAt law depth
    let key : Key law := ⟨anchor, query⟩
    ((RawGeneratedRoot.CofinalAction.faithfulLaw
        (MotherPhysicalSource.receiptAction law)).faithfulAt anchor.2
        ).freeEvaluation (Finsupp.single generator coefficient) =
          coefficient • (MotherPhysicalSource.evaluatorAt law anchor.2).root generator ∧
      HEq ((facade law).readoutAt runtime query)
        ((projectionLaw law).outcomeAt (key, 0) anchor.2) ∧
      (answer law key).2.1 =
        ((RawGeneratedRoot.CofinalAction.faithfulLaw
          (MotherPhysicalSource.receiptAction law)).faithfulAt
            anchor.2).settleWithResidual ∧
      HEq ((inquiryAt law depth).compileInquiry query).answerReadout
        (answer law key) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        ((livingRoot law).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      HEq (((livingRoot law).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        runtime.current.visit.current).entryDisposition
          (RawGeneratedRoot.entry dynamics runtime.current.visit.current))
        (LedgerEntryDispositionAt.evolved
          (LedgerEntryEvolutionAt.transferred
            (dynamics.emit runtime.current.visit.current)
              rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt N
              (RawGeneratedRoot.entry dynamics runtime.current.visit.current)
              (RawGeneratedRoot.entry dynamics
                (dynamics.update (dynamics.emit runtime.current.visit.current))))) ∧
      runtime.tick.nextCurrent =
        (process law).stateAt ((process law).successor runtime.state) ∧
      ((livingRoot law).toAuthoritativeRoot.toRoot.evolutionAt
        runtime.current.visit.current).nextCurrent? =
          some (dynamics.update (dynamics.emit runtime.current.visit.current)) := by
  have sourceFact := MotherPhysicalSource.physical_receipt_equation_ledger_next
    law runtime.current.visit.current generator coefficient
  have facadeFact := (facade law).readoutAt_factorizes runtime query
  have inquiryFact := original_inquiry_receipt_readback law runtime.state query
  exact ⟨sourceFact.1, runtime_readout_original_projection law runtime query,
    inquiryFact.1, inquiryFact.2.1, facadeFact.2.2.1,
    inquiryFact.2.2.1, facadeFact.2.2.2.2, inquiryFact.2.2.2⟩

#print axioms visitAt_depth
#print axioms runtimeAt_original_visit
#print axioms runtimeAt_tick_original_next
#print axioms runtime_other_anchor_inactive
#print axioms runtime_receipt_inquiry_consumer

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
