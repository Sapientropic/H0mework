import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcedInverseSourceFields

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKForcedInverseSourceWriteback
open Complex BurnolPhysicalState RootInquiryCompletion
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
local instance admissionsLevelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
  L.groups (PairValue OriginalKCombReceiptFeedback.Value) grade target
open private born_inventory from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Native
open private source_word_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPowerWaveSourceWriteback
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "raw" => C.forcedSourceCode observation nontrivial depth half
local notation "trace" => C.forcedSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)

def oldAdmissions : List (AR.Admission before (Engine.stockScalar frame base)) :=
  OriginalKReturnJordanSourceWriteback.admissions observation nontrivial half depth ordinal

def jointAdmissions : List (AR.Admission before (Engine.stockScalar frame base)) :=
  List.ofFn fun index => WN.packetAdmission factory (AS.bornAfterNative native) (WN.oldStock native)
    (WN.oldEnvironment native) (born_inventory native)
    (OriginalKForcedInverseSourceOccurrences.actualOccurrence observation nontrivial half depth ordinal index)

theorem admissions_steps :
    (jointAdmissions observation nontrivial half depth ordinal).length = remaining raw ∧
      0 < (jointAdmissions observation nontrivial half depth ordinal).length := by
  have count : (jointAdmissions observation nontrivial half depth ordinal).length = remaining raw := by
    rw [jointAdmissions, List.length_ofFn]
    exact (PT.complete_steps trace).trans (trace).length_to_const
  refine ⟨count, ?_⟩
  rw [count]
  change 0 < _+1
  omega

def jointWords := List.ofFn fun index :
    OriginalKForcedInverseSourceOccurrences.Index observation nontrivial half depth =>
  ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
    (NW.admissionWord factory packet
      (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
        ((PT.words trace).get index))))

theorem admissions_words :
    (jointAdmissions observation nontrivial half depth ordinal).map (fun admitted => admitted.1.word) =
      jointWords observation nontrivial half depth ordinal := by
  unfold jointAdmissions jointWords
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact (OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative.packet_admission_word
    factory (AS.bornAfterNative native) (WN.oldStock native) (WN.oldEnvironment native)
      (born_inventory native) (OriginalKForcedInverseSourceOccurrences.actualOccurrence
        observation nontrivial half depth ordinal index)).trans
    (congrArg (ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm)
      (OriginalKForcedInverseSourceOccurrences.actual_word observation nontrivial half depth ordinal index))

theorem words_sum : (jointWords observation nontrivial half depth ordinal).sum =
    ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
      (NW.admissionWord factory packet
        (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
          (boundary observation nontrivial half depth)))) := by
  let action :=
    (ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm).toLinearMap.comp
      ((NW.admissionWord factory packet).comp
        ((liftMap (R := ℤ)).comp (R.wordMapAt observation nontrivial half depth (ordinal+1))))
  have indexed : (List.ofFn fun index : OriginalKForcedInverseSourceOccurrences.Index
      observation nontrivial half depth => (PT.words trace).get index) = PT.words trace := List.ofFn_get _
  have transformed := congrArg (List.map action) indexed
  rw [List.map_ofFn] at transformed
  have listed : jointWords observation nontrivial half depth ordinal =
      (PT.words trace).map action := transformed
  rw [listed, ← map_list_sum, PT.paid_boundary]
  rfl

def admissions : List (AR.Admission before (Engine.stockScalar frame base)) :=
  oldAdmissions observation nontrivial half depth ordinal ++ jointAdmissions observation nontrivial half depth ordinal

theorem old_admissions_prefix :
    (admissions observation nontrivial half depth ordinal).take
      (oldAdmissions observation nontrivial half depth ordinal).length =
        oldAdmissions observation nontrivial half depth ordinal := by
  simp only [admissions, List.take_left]

def request := SN.request (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv (admissions observation nontrivial half depth ordinal)
def generatedAction := SN.generatedAction (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv (admissions observation nontrivial half depth ordinal)
def nextFace := SN.nextOriginFace (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv (admissions observation nontrivial half depth ordinal)
def sourceWord := SN.sourceWord (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before (admissions observation nontrivial half depth ordinal)
def nextFullValue := SN.nextFullValue (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv (admissions observation nontrivial half depth ordinal)

theorem source_word_split : sourceWord observation nontrivial half depth ordinal =
    SN.sourceWord (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1)
      frame base before (oldAdmissions observation nontrivial half depth ordinal)+
    SN.sourceWord (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1)
      frame base before (jointAdmissions observation nontrivial half depth ordinal) :=
  source_word_append
    (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1)
    (X := (AS.bornAfterNative native).2.2.1.LowVar) frame base before
    (oldAdmissions observation nontrivial half depth ordinal)
    (jointAdmissions observation nontrivial half depth ordinal)


end OriginalKForcedInverseSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKForcedInverseSourceWriteback"
