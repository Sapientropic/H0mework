import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPrimitiveMobiusSourceFields

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPrimitiveMobiusSourceWriteback
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
local notation "raw" => C.wholeDebtRPrimitiveMobiusSourceCode observation nontrivial depth half
local notation "trace" => C.wholeDebtRPrimitiveMobiusSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)

def oldAdmissions : List (AR.Admission before (Engine.stockScalar frame base)) :=
  OriginalKReciprocalCotestSourceWriteback.admissions observation nontrivial half depth ordinal

def fieldAdmissions (field : Fin 3) : List (AR.Admission before (Engine.stockScalar frame base)) :=
  List.ofFn fun index => WN.packetAdmission factory (AS.bornAfterNative native) (WN.oldStock native)
    (WN.oldEnvironment native) (born_inventory native)
    (OriginalKPrimitiveMobiusSourceOccurrences.actualOccurrence observation nontrivial half depth ordinal field index)

def nativeAdmissions : List (AR.Admission before (Engine.stockScalar frame base)) :=
  fieldAdmissions observation nontrivial half depth ordinal 0 ++
    fieldAdmissions observation nontrivial half depth ordinal 1 ++
      fieldAdmissions observation nontrivial half depth ordinal 2

theorem admissions_steps :
    (∀ field : Fin 3,
      (fieldAdmissions observation nontrivial half depth ordinal field).length = remaining (raw field) ∧
        0 < (fieldAdmissions observation nontrivial half depth ordinal field).length) ∧
    (nativeAdmissions observation nontrivial half depth ordinal).length =
      remaining (raw 0)+remaining (raw 1)+remaining (raw 2) := by
  have each (field : Fin 3) :
      (fieldAdmissions observation nontrivial half depth ordinal field).length = remaining (raw field) ∧
        0 < (fieldAdmissions observation nontrivial half depth ordinal field).length := by
    have count : (fieldAdmissions observation nontrivial half depth ordinal field).length = remaining (raw field) := by
      rw [fieldAdmissions, List.length_ofFn]
      exact (PT.complete_steps (trace field)).trans (trace field).length_to_const
    refine ⟨count, ?_⟩
    rw [count]
    fin_cases field <;> change 0 < _+1 <;> omega
  refine ⟨each, ?_⟩
  simp only [nativeAdmissions, List.length_append, (each 0).1, (each 1).1, (each 2).1]

def fieldWords (field : Fin 3) := List.ofFn fun index :
    OriginalKPrimitiveMobiusSourceOccurrences.Index observation nontrivial half depth field =>
  ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
    (NW.admissionWord factory packet
      (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
        ((PT.words (trace field)).get index))))

def nativeWords := fieldWords observation nontrivial half depth ordinal 0 ++
  fieldWords observation nontrivial half depth ordinal 1 ++ fieldWords observation nontrivial half depth ordinal 2

theorem field_admissions_words (field : Fin 3) :
    (fieldAdmissions observation nontrivial half depth ordinal field).map (fun admitted => admitted.1.word) =
      fieldWords observation nontrivial half depth ordinal field := by
  unfold fieldAdmissions fieldWords
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact (OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative.packet_admission_word
    factory (AS.bornAfterNative native) (WN.oldStock native) (WN.oldEnvironment native)
      (born_inventory native) (OriginalKPrimitiveMobiusSourceOccurrences.actualOccurrence
        observation nontrivial half depth ordinal field index)).trans
    (congrArg (ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm)
      (OriginalKPrimitiveMobiusSourceOccurrences.actual_word observation nontrivial half depth ordinal field index))

theorem admissions_words :
    (nativeAdmissions observation nontrivial half depth ordinal).map (fun admitted => admitted.1.word) =
      nativeWords observation nontrivial half depth ordinal := by
  simp only [nativeAdmissions, nativeWords, List.map_append, field_admissions_words]

theorem words_sum (field : Fin 3) : (fieldWords observation nontrivial half depth ordinal field).sum =
    ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
      (NW.admissionWord factory packet
        (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
          (boundary observation nontrivial half depth field)))) := by
  let action :=
    (ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm).toLinearMap.comp
      ((NW.admissionWord factory packet).comp
        ((liftMap (R := ℤ)).comp (R.wordMapAt observation nontrivial half depth (ordinal+1))))
  have indexed : (List.ofFn fun index : OriginalKPrimitiveMobiusSourceOccurrences.Index
      observation nontrivial half depth field => (PT.words (trace field)).get index) = PT.words (trace field) :=
    List.ofFn_get _
  have transformed := congrArg (List.map action) indexed
  rw [List.map_ofFn] at transformed
  have listed : fieldWords observation nontrivial half depth ordinal field =
      (PT.words (trace field)).map action := transformed
  rw [listed, ← map_list_sum, PT.paid_boundary]
  rfl

def admissions : List (AR.Admission before (Engine.stockScalar frame base)) :=
  oldAdmissions observation nontrivial half depth ordinal ++ nativeAdmissions observation nontrivial half depth ordinal

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
      frame base before (nativeAdmissions observation nontrivial half depth ordinal) :=
  source_word_append
    (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1)
    (X := (AS.bornAfterNative native).2.2.1.LowVar) frame base before
    (oldAdmissions observation nontrivial half depth ordinal)
    (nativeAdmissions observation nontrivial half depth ordinal)


end OriginalKPrimitiveMobiusSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
