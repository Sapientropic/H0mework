import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.SeedReceipt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Origin

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierNativeSeed
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
open CofinalHistorySettlement
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace C
export OriginalKCombReceiptFeedback (Value Var receipt wholeDebtRWaveSourceCode wholeDebtRWaveSourceTrace)
end C
namespace Root
export OriginalKPairedWaveRootSource (currentAdmissions retainedAdmission retainedSlot currentHistory)
end Root
namespace Origin
export OriginalConstantFourierNativeOrigin (sourceRoot sourceVisit currentAdmissions admissions_source originFace)
end Origin
namespace Receipt
export OriginalConstantFourierSeedReceipt (sourceCode originalChild original_value original_child_address original_child_paid)
end Receipt
namespace A
export ActualCofinalSourceAction (wordTransport)
end A
namespace Born
export OriginalKBFiniteCalculation.BornInventory (packetAt)
end Born
namespace D
export OriginalKCombFirstFullSourceDynamics (factory)
end D
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (native beforeStock relationTransport)
end WN
namespace NW
export NativeSigma.Writeback (admissionWord)
end NW
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (wordMapAt)
end R
namespace PT
export SourceOperationPaidRelations (words complete_steps)
end PT
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
namespace PW
export OriginalKPowerWaveSourceOccurrences (actualOccurrence actual_word)
end PW
open private get_cast mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
open private relationTransport_word occurrenceIndex occurrence_read eventWord from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveRootSource
open private childAt decodeMap first_word_decode physical_word physical_native_word from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRootSource
open private physicalValue from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextSource
attribute [local instance] OriginalKPairedWaveRootSource.levelGroups
attribute [local irreducible] Origin.currentAdmissions AS.nativeAfterAdmission physicalValue

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "raw" => C.wholeDebtRWaveSourceCode observation nontrivial depth half
local notation "trace" => C.wholeDebtRWaveSourceTrace observation nontrivial depth half
local notation "admissions" => Origin.currentAdmissions observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "packet" => Born.packetAt observation nontrivial half depth
local notation "native" => WN.native observation nontrivial half depth ordinal

abbrev sourceRoot := Origin.sourceRoot observation nontrivial half depth ordinal
abbrev sourceVisit := Origin.sourceVisit observation nontrivial half depth ordinal

noncomputable def retainedSlot : Fin (admissions).length :=
  Fin.cast (congrArg List.length (Origin.admissions_source observation nontrivial half depth ordinal)).symm
    (Root.retainedSlot observation nontrivial half depth ordinal)

noncomputable def retainedAdmission : type_of% (Root.retainedAdmission observation nontrivial half depth ordinal) :=
  (admissions).get (retainedSlot observation nontrivial half depth ordinal)

private theorem retained_admission_source : retainedAdmission observation nontrivial half depth ordinal =
    Root.retainedAdmission observation nontrivial half depth ordinal :=
  get_cast admissions (Root.currentAdmissions observation nontrivial half depth ordinal)
    (Origin.admissions_source observation nontrivial half depth ordinal)
    (Root.retainedSlot observation nontrivial half depth ordinal)

noncomputable def currentHistory : type_of% (WN.beforeStock native).trace :=
  let admitted := retainedAdmission observation nontrivial half depth ordinal
  admitted.1.before ++ .relation admitted.1.word :: admitted.1.after

theorem history_source : currentHistory observation nontrivial half depth ordinal = (WN.beforeStock native).trace :=
  (retainedAdmission observation nontrivial half depth ordinal).1.trace_eq.symm

private theorem first_positive : 0 < (PT.words trace).length := by
  rw [PT.complete_steps, (trace).length_to_const]
  change 0 < _ + 1
  omega

noncomputable def firstIndex : Fin (PT.words trace).length :=
  ⟨0, first_positive observation nontrivial half depth⟩

noncomputable def originalOccurrence : WR.RelationOccurrence (WN.beforeStock native) :=
  WN.relationTransport (AS.bornAfterNative native).2.2.2.down.symm
    (PW.actualOccurrence observation nontrivial half depth ordinal
      (firstIndex observation nontrivial half depth))

private theorem original_word : (originalOccurrence observation nontrivial half depth ordinal).word =
    A.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
      (NW.admissionWord factory (packet (ordinal + 1))
        (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
          ((PT.words trace).get (firstIndex observation nontrivial half depth))))) := by
  rw [originalOccurrence, relationTransport_word, PW.actual_word]

noncomputable def wholeWaveSlot : Fin (currentHistory observation nontrivial half depth ordinal).length :=
  Fin.cast (congrArg List.length (history_source observation nontrivial half depth ordinal)).symm
    (occurrenceIndex (originalOccurrence observation nontrivial half depth ordinal))

noncomputable def wholeWaveWord : type_of% (originalOccurrence observation nontrivial half depth ordinal).word :=
  eventWord ((currentHistory observation nontrivial half depth ordinal).get
    (wholeWaveSlot observation nontrivial half depth ordinal))

private theorem whole_wave_word_source : wholeWaveWord observation nontrivial half depth ordinal =
    (originalOccurrence observation nontrivial half depth ordinal).word :=
  congrArg eventWord ((get_cast (currentHistory observation nontrivial half depth ordinal)
    (WN.beforeStock native).trace (history_source observation nontrivial half depth ordinal)
    (occurrenceIndex (originalOccurrence observation nontrivial half depth ordinal))).trans
      (occurrence_read (originalOccurrence observation nontrivial half depth ordinal)))

/-- Linear nodes consume one address bit; the sole true bit selects the original profile subtraction. -/
def seedPath : List Bool := [false,false,false,false,false,true,false,false,false,false,false,false]

private theorem child_syntax : childAt seedPath raw = Receipt.sourceCode := rfl

noncomputable def seedValue : BurnolL2 := physicalValue (AS.bornAfterNative native).1
  (decodeMap (remaining raw) seedPath (wholeWaveWord observation nontrivial half depth ordinal))

theorem seed_value_source : seedValue observation nontrivial half depth ordinal =
    (Receipt.originalChild observation nontrivial half depth).value := by
  have word := (whole_wave_word_source observation nontrivial half depth ordinal).trans
    (original_word observation nontrivial half depth ordinal)
  refine (congrArg (fun item => physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining raw) seedPath item)) word).trans ?_
  refine (physical_native_word (remaining raw) seedPath factory (packet (ordinal+1))
    (R.wordMapAt observation nontrivial half depth (ordinal+1)
      ((PT.words trace).get (firstIndex observation nontrivial half depth)))).trans ?_
  refine (physical_word observation nontrivial half depth (remaining raw) seedPath
    ((PT.words trace).get (firstIndex observation nontrivial half depth)) (ordinal+1)).trans ?_
  refine (first_word_decode seedPath trace (first_positive observation nontrivial half depth)).trans ?_
  rw [child_syntax]
  exact (Receipt.originalChild observation nontrivial half depth).trace.sound

noncomputable def seedTrace : Trace (C.receipt observation nontrivial depth half).1.environment
    Receipt.sourceCode (.const (seedValue observation nontrivial half depth ordinal)) :=
  Eq.mp (congrArg (fun point => Trace (C.receipt observation nontrivial depth half).1.environment
    Receipt.sourceCode (.const point)) (seed_value_source observation nontrivial half depth ordinal).symm)
      (Receipt.originalChild observation nontrivial half depth).trace

theorem seed_trace_source : type_of% (mp_heq
    (congrArg (fun point => Trace (C.receipt observation nontrivial depth half).1.environment
      Receipt.sourceCode (.const point)) (seed_value_source observation nontrivial half depth ordinal).symm)
      (Receipt.originalChild observation nontrivial half depth).trace) := mp_heq _ _

theorem seed_paid : (seedTrace observation nontrivial half depth ordinal).length = 0 :=
  (seedTrace observation nontrivial half depth ordinal).length_to_const

theorem seed_value : seedValue observation nontrivial half depth ordinal =
    OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed :=
  (seed_value_source observation nontrivial half depth ordinal).trans
    (Receipt.original_value observation nontrivial half depth)

end OriginalConstantFourierNativeSeed
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierNativeSeed"
