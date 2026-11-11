import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.RetainedFace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPairedWaveNativeStockConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierNativeOrigin
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution BurnolPhysicalState
namespace MS
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (frame)
end MS
namespace Transport
export OriginalConstantFourierRetainedFace.Transport (completed_frame)
end Transport
namespace Retained
export OriginalConstantFourierRetainedFace.Retained (targetFace target_payload)
end Retained

attribute [local instance] OriginalKPairedWaveRootSource.levelGroups

namespace A
export OriginalKPairedWaveAction (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader originFace)
end A
namespace N
export OriginalKPairedWaveNativeStockSource (stockProgramme settledFrame)
end N
namespace C
export OriginalWholeDebtRPairedWaveNativeStockConsumer (actualBirthTarget actualBirthEvent)
end C

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "root" => A.sourceRoot observation nontrivial half depth ordinal
local notation "visit" => A.sourceVisit observation nontrivial half depth ordinal
local notation "u7" => A.sourceU7 observation nontrivial half depth ordinal
local notation "calculus" => A.sourceCalculus observation nontrivial half depth ordinal
local notation "reader" => A.sourceReader observation nontrivial half depth ordinal
local notation "face" => A.originFace observation nontrivial half depth ordinal
local notation "cfg" => N.stockProgramme observation nontrivial half depth ordinal
local notation "event" => C.actualBirthEvent observation nontrivial half depth ordinal
local notation "currentFrame" => N.settledFrame observation nontrivial half depth ordinal
local notation "frameSource" => Transport.completed_frame (MS.frame root visit u7 calculus reader) cfg

abbrev sourceRoot := (C.actualBirthTarget observation nontrivial half depth ordinal).targetRoot
abbrev sourceVisit := (C.actualBirthTarget observation nontrivial half depth ordinal).targetVisit

noncomputable def originFace :=
  Retained.targetFace root visit u7 calculus reader face currentFrame frameSource cfg event

theorem origin_payload : type_of% (Retained.target_payload root visit u7 calculus reader face currentFrame frameSource cfg event) :=
  Retained.target_payload root visit u7 calculus reader face currentFrame frameSource cfg event

noncomputable def originPayload : type_of% (face).rootRead :=
  Eq.mp (type_eq_of_heq (origin_payload observation nontrivial half depth ordinal))
    (originFace observation nontrivial half depth ordinal).rootRead

theorem origin_source : originPayload observation nontrivial half depth ordinal = (face).rootRead :=
  eq_of_heq ((cast_heq_iff_heq _ _ _).mpr (origin_payload observation nontrivial half depth ordinal))

noncomputable def currentAdmissions :=
  (originPayload observation nontrivial half depth ordinal).source.occurrences

theorem admissions_source : currentAdmissions observation nontrivial half depth ordinal =
    OriginalKPairedWaveRootSource.currentAdmissions observation nontrivial half depth ordinal :=
  congrArg (fun payload => payload.source.occurrences) (origin_source observation nontrivial half depth ordinal)

end OriginalConstantFourierNativeOrigin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierNativeOrigin"
