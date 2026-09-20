import H0mework.Physics.Revision.InquiryPrograms

/-! The macro registry preserves exact temporal histories. Its two source
epochs are distinguished by their actual initial ledger: the original
quadratic boundary is open, while the material ingress retains the already
settled first-assembly boundary. No artificial epoch label carries physics. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext
open StageTenPhysicalRoot

noncomputable section

def oldInquiryPresentation (n : Nat) : RootInquiryStatePresentation where
  N := OldN
  V := V
  state := .create (oldReadInquiryState (physicalRuntimeVisit n))

def cartanInquiryPresentation : RootInquiryStatePresentation where
  N := OldN
  V := V
  state := .create cartanActionInquiryState

def materialInquiryPresentation (n : Nat) : RootInquiryStatePresentation where
  N := MaterialN
  V := MaterialV
  state := .create (materialReadInquiryState (n + 1))

inductive MacroState
  | original (index : Fin 3)
  | cartanAction
  | material (index : Nat)

def macroPresentation : MacroState → RootInquiryStatePresentation
  | .original index => oldInquiryPresentation index
  | .cartanAction => cartanInquiryPresentation
  | .material index => materialInquiryPresentation index

private def postCofinalDepth {N : WorldRelationNetwork} {W : Vocabulary}
    {root : SourceNativeLedgerRootClosure N W} {current : W.Current} :
    SourceNativePostCofinalReachableAt root current → Nat
  | .cofinal _ => 0
  | .step prior _ => postCofinalDepth prior + 1

def temporalDepth {N : WorldRelationNetwork} {W : Vocabulary}
    {root : SourceNativeLedgerRootClosure N W} {current : W.Current} :
    SourceNativeTemporalReachableAt root current → Nat
  | .finite history => ProductiveFiniteRootHistoryAt.causalDepth history
  | .postCofinal history => postCofinalDepth history

theorem temporalDepth_next {N : WorldRelationNetwork} {W : Vocabulary}
    {root : SourceNativeLedgerRootClosure N W} {current next : W.Current}
    (history : SourceNativeTemporalReachableAt root current)
    (next_eq : (root.toRoot.evolutionAt current).nextCurrent? = some next) :
    temporalDepth (history.next next_eq) = temporalDepth history + 1 := by
  cases history <;> rfl

def erasedDepth (value : AnyAuthoritativeRootCurrent) : Nat :=
  temporalDepth value.current.visit.history

private theorem oldVisit_depth (n : Nat) :
    temporalDepth (physicalRuntimeVisit n).history = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp only [physicalRuntimeVisit, livingRootNextVisit]
      exact (temporalDepth_next (physicalRuntimeVisit n).history _).trans
        (congrArg (· + 1) ih)

private theorem materialVisit_depth (n : Nat) :
    temporalDepth (materialVisit n).history = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp only [materialVisit]
      exact (temporalDepth_next (materialVisit n).history _).trans
        (congrArg (· + 1) ih)

private theorem original_depth (n : Nat) :
    erasedDepth (oldInquiryPresentation n).erase = n := oldVisit_depth n

private theorem material_depth (n : Nat) :
    erasedDepth (materialInquiryPresentation n).erase = n + 1 :=
  materialVisit_depth (n + 1)

def InitiallySettled (value : AnyAuthoritativeRootCurrent) : Prop :=
  ∃ identifies : value.N.Responsibility = RootResidualPayload,
    ∀ responsibility,
      value.N.OpenAt
          (value.current.root.toRoot.supportAt
            value.current.root.toRoot.source.initial) responsibility →
        (identifies ▸ responsibility).coframeBoundary = .settled

theorem old_not_initiallySettled
    (visit : SourceNativeTemporalVisitAt sourceNativeRoot) :
    ¬ InitiallySettled ⟨OldN, ⟨V, authoritativeRoot, visit⟩⟩ := by
  rintro ⟨identifies, settled⟩
  have identifies_eq : identifies = rfl := Subsingleton.elim _ _
  cases identifies_eq
  have impossible := settled (rootResidualAt Initial) ⟨rfl⟩
  cases impossible

private theorem material_initiallySettled
    (visit : SourceNativeTemporalVisitAt materialLivingRoot.toAuthoritativeRoot.toLedgerRoot) :
    InitiallySettled ⟨MaterialN, ⟨MaterialV, materialAuthoritativeRoot, visit⟩⟩ := by
  refine ⟨rfl, ?_⟩
  intro responsibility opened
  change MaterialOpenAt (.inl firstAssemblyCurrent) responsibility at opened
  cases opened.exact
  rfl

private theorem original_ne_material (oldIndex newIndex : Nat) :
    (oldInquiryPresentation oldIndex).erase ≠
      (materialInquiryPresentation newIndex).erase := by
  intro equal
  have settled := material_initiallySettled (materialVisit (newIndex + 1))
  exact old_not_initiallySettled (physicalRuntimeVisit oldIndex)
    ((congrArg InitiallySettled equal).mpr settled)

private theorem action_ne_material (newIndex : Nat) :
    cartanInquiryPresentation.erase ≠ (materialInquiryPresentation newIndex).erase := by
  intro equal
  have settled := material_initiallySettled (materialVisit (newIndex + 1))
  exact old_not_initiallySettled afterGravityTemporalVisit
    ((congrArg InitiallySettled equal).mpr settled)

theorem macroPresentation_erase_injective :
    Function.Injective (fun state => (macroPresentation state).erase) := by
  intro left right equal
  cases left with
  | original i =>
      cases right with
      | original j =>
          have depths := congrArg erasedDepth equal
          change erasedDepth (oldInquiryPresentation i).erase =
            erasedDepth (oldInquiryPresentation j).erase at depths
          rw [original_depth, original_depth] at depths
          exact congrArg MacroState.original (Fin.ext depths)
      | cartanAction =>
          have depths := congrArg erasedDepth equal
          change erasedDepth (oldInquiryPresentation i).erase = 3 at depths
          rw [original_depth] at depths
          omega
      | material j => exact False.elim (original_ne_material i j equal)
  | cartanAction =>
      cases right with
      | original j =>
          have depths := congrArg erasedDepth equal
          change 3 = erasedDepth (oldInquiryPresentation j).erase at depths
          rw [original_depth] at depths
          omega
      | cartanAction => rfl
      | material j => exact False.elim (action_ne_material j equal)
  | material i =>
      cases right with
      | original j => exact False.elim (original_ne_material j i equal.symm)
      | cartanAction => exact False.elim (action_ne_material i equal.symm)
      | material j =>
          have depths := congrArg erasedDepth equal
          change erasedDepth (materialInquiryPresentation i).erase =
            erasedDepth (materialInquiryPresentation j).erase at depths
          rw [material_depth, material_depth] at depths
          exact congrArg MacroState.material (Nat.add_right_cancel depths)

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision
