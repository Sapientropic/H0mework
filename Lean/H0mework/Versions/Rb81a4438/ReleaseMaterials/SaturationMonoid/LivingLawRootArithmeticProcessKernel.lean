import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawArithmeticProcessKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootArithmeticCompletionKernel

/-!
# Root arithmetic material-revelation process

The exact completion receipt generates both its free-closure process and the
lossless local process of its derived occurrence.  Normal form authority is a
private dependent face of this process and retains the original whole-ledger
write-back and generated next current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootArithmeticProcess

open ArithmeticProcess
open RootArithmeticCompletion
open RootArithmeticIncidence

universe u

/-- Zero-field root process generated from one exact completion receipt. -/
structure RootGeneratedArithmeticProcessAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    (completion : RootArithmeticCompletionReceiptAt step direction) : Type where
  private mk ::

def sourceGeneratedRootArithmeticProcess
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    (completion : RootArithmeticCompletionReceiptAt step direction) :
    RootGeneratedArithmeticProcessAt completion :=
  ⟨⟩

namespace RootGeneratedArithmeticProcessAt

def closureProcess
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    (_process : RootGeneratedArithmeticProcessAt completion) :
    SourceGeneratedFreeClosureProcessAt completion.completionNode :=
  compileFreeClosure completion.completionNode

def derivedProcess
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    (_process : RootGeneratedArithmeticProcessAt completion) :
    SourceGeneratedArithmeticProcessAt
      completion.derivedOccurrence.occurrence :=
  ArithmeticProcess.compile completion.derivedOccurrence.occurrence

def wholeLedgerWriteBack
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    (_process : RootGeneratedArithmeticProcessAt completion) :=
  completion.wholeLedgerWriteBack

def nextCurrent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    (_process : RootGeneratedArithmeticProcessAt completion) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  completion.nextCurrent

@[simp] theorem nextCurrent_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    (process : RootGeneratedArithmeticProcessAt completion) :
    process.nextCurrent = root.generatedNextCurrentAt visit :=
  rfl

theorem unique
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    (left right : RootGeneratedArithmeticProcessAt completion) :
    left = right := by
  cases left
  cases right
  rfl

end RootGeneratedArithmeticProcessAt

/-- Private dependent normal-form face.  A naked normal-form value is only a
readout and cannot carry root authority. -/
structure RootArithmeticProcessNormalFormAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    (process : RootGeneratedArithmeticProcessAt completion) : Type where
  private mk ::

def RootGeneratedArithmeticProcessAt.normalFormFace
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    (process : RootGeneratedArithmeticProcessAt completion) :
    RootArithmeticProcessNormalFormAt process :=
  ⟨⟩

namespace RootArithmeticProcessNormalFormAt

def readout
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (_face : RootArithmeticProcessNormalFormAt process) :
    ArithmeticProcessNormalForm :=
  process.derivedProcess.normalForm

def stageHistory
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (_face : RootArithmeticProcessNormalFormAt process) :
    List ArithmeticProcessStage :=
  process.derivedProcess.history

def closureHistory
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (_face : RootArithmeticProcessNormalFormAt process) :
    List FreeClosureProcessStage :=
  process.closureProcess.history

def wholeLedgerWriteBack
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (_face : RootArithmeticProcessNormalFormAt process) :=
  process.wholeLedgerWriteBack

def nextCurrent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (_face : RootArithmeticProcessNormalFormAt process) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  process.nextCurrent

/-- Lossless factorization back to the exact derived occurrence. -/
@[simp] theorem readout_toOccurrence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (face : RootArithmeticProcessNormalFormAt process) :
    face.readout.toOccurrence =
      completion.derivedOccurrence.occurrence :=
  process.derivedProcess.normalForm_toOccurrence

theorem unique
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {step : RootArithmeticIncidenceStepAt recognition visit}
    {direction : GeneratedArithmeticClosureDirectionAt step}
    {completion : RootArithmeticCompletionReceiptAt step direction}
    {process : RootGeneratedArithmeticProcessAt completion}
    (left right : RootArithmeticProcessNormalFormAt process) :
    left = right := by
  cases left
  cases right
  rfl

end RootArithmeticProcessNormalFormAt
end RootArithmeticProcess
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
