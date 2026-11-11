import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJointMobiusSourceAdmissions

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKJointMobiusSourceWriteback
open Complex BurnolPhysicalState RootInquiryCompletion
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
local instance writebackLevelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
  L.groups (PairValue OriginalKCombReceiptFeedback.Value) grade target
open private born_word_relation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRSourceReceiptConsumer
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "raw" => C.wholeDebtRJointMobiusSourceCode observation nontrivial depth half
local notation "trace" => C.wholeDebtRJointMobiusSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)

def bornBoundary (field : Fin 2) := R.bornWordMap observation nontrivial half depth ordinal
  (boundary observation nontrivial half depth field)

theorem born_boundary_written (field : Fin 2) : bornBoundary observation nontrivial half depth ordinal field ∈
    (Born.sourceBornHistory observation nontrivial half depth ordinal).relationClosure := by
  have each (word) (belongs : word ∈ PT.words (trace field)) :=
    born_word_relation observation nontrivial half depth word
      (C.whole_debt_R_joint_mobius_source_preserved observation nontrivial depth half field
        (.relation word) (by
          apply List.mem_cons_of_mem
          change .relation word ∈ RootedAccountedUnfolding.traceBranches
            (SourceOperationPaidRelations.events (trace field))
          rw [PT.events_trace]
          exact List.mem_map.mpr ⟨word, belongs, rfl⟩)) ordinal
  have sum_mem : ∀ items : List (Formal ℤ Prog.Value Prog.Var ()),
      (∀ word ∈ items, R.bornWordMap observation nontrivial half depth ordinal word ∈
        (Born.sourceBornHistory observation nontrivial half depth ordinal).relationClosure) →
      R.bornWordMap observation nontrivial half depth ordinal items.sum ∈
        (Born.sourceBornHistory observation nontrivial half depth ordinal).relationClosure := by
    intro items
    induction items with
    | nil => intro _; rw [List.sum_nil, map_zero]; exact Submodule.zero_mem _
    | cons head tail previous =>
        intro all
        rw [List.sum_cons, map_add]
        exact Submodule.add_mem _ (all head List.mem_cons_self)
          (previous (fun word belongs => all word (List.mem_cons_of_mem head belongs)))
  unfold bornBoundary boundary
  rw [← PT.paid_boundary]
  exact sum_mem (PT.words (trace field)) each

theorem actual_born_kernel : ∀ field : Fin 2,
    (Born.actualBornHistory observation nontrivial half depth ordinal).completionProjection
      ((Submodule.inclusion
        (Born.actualBornHistory observation nontrivial half depth ordinal).relationClosure_le_generatorClosure)
        ⟨bornBoundary observation nontrivial half depth ordinal field,
          Born.actual_source_relations_in_born observation nontrivial half depth ordinal
            (born_boundary_written observation nontrivial half depth ordinal field)⟩) = 0 := by
  intro field
  exact (Submodule.Quotient.mk_eq_zero _).2
    (Born.actual_source_relations_in_born observation nontrivial half depth ordinal
      (born_boundary_written observation nontrivial half depth ordinal field))

theorem canonical_next : type_of% (SN.canonical_next (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.canonical_next (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem source_occurrences : (nextFace observation nontrivial half depth ordinal).rootRead.source.occurrences =
    admissions observation nontrivial half depth ordinal :=
  SN.next_source_occurrences (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem actual_compiles : type_of% (SN.compiles (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.compiles (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem source_effect : type_of% (SN.source_effect (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.source_effect (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem source_inverse : type_of% (SN.source_inverse (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.source_inverse (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem inverse_certificate : type_of% (ActualSourceConstantInverse.actual_next_certificate (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := ActualSourceConstantInverse.actual_next_certificate (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem whole_next : type_of% (ActualSourceConstantInverse.original_whole_next (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := ActualSourceConstantInverse.original_whole_next (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem same_ledger : type_of% (SN.same_ledger (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.same_ledger (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem same_visit : type_of% (SN.same_visit (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.same_visit (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)

end OriginalKJointMobiusSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
