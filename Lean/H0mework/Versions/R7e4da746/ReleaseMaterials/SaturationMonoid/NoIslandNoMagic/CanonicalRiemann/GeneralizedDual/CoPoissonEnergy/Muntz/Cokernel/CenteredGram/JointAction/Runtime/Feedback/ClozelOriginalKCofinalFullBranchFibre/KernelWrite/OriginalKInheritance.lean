import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Inheritance
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Native

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.OriginalKInheritance
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift
open ActualNativeCofaceInheritance
attribute [local irreducible] ActualNativeCofaceInheritance.ProjectionFibre
namespace C
export OriginalKCombReceiptFeedback
  (frame endpoint sourceRoot sourceVisit sourceReader Value Var)
end C
namespace O
export OriginalKCombFirstFullSource (factory data configuration)
end O
namespace FD
export OriginalKCombFirstFullSourceDynamics (factory initial firstCfg packet)
end FD
namespace D
export ActualNativeCofaceInheritance.D (packetAt)
end D
namespace AS
export ActualNativeCofaceInheritance.AS (nativeAfterAdmission bornAfterNative stockCfg)
end AS
namespace S
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (originalMaterialFace endpointCount)
end S
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative (originalState)
end SN
open NoIslandNoMagic.CanonicalRiemann
namespace WordNative
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (sourceFrame sourceBase)
end WordNative
local instance levelGroups (grade : Nat) : ∀ target,
    AddCommGroup (ActualNativeCofaceInheritance.L.Value (PairValue C.Value) grade target) :=
  ActualNativeCofaceInheritance.L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def originalFace := S.originalMaterialFace
  (C.sourceRoot observation nontrivial) (C.sourceVisit observation nontrivial depth)
  emptyEffectU7 emptyEffectU7Calculus (C.sourceReader observation nontrivial depth half)
  (S.endpointCount (C.sourceRoot observation nontrivial)
    (C.sourceVisit observation nontrivial depth) (C.sourceReader observation nontrivial depth half))

def originalMaterial := (originalFace observation nontrivial half depth).rootRead

def originalOutcome :=
  (C.endpoint observation nontrivial depth half).root.source.base.projectionLaw.outcomeAt
    (originalFace observation nontrivial half depth).projection
    ((C.endpoint observation nontrivial depth half).root.emitted
      (C.endpoint observation nontrivial depth half).visit.current)

def originalCarrier : Carrier (originalOutcome observation nontrivial half depth)
    (C.frame observation nontrivial depth half) :=
  makeCarrier (originalOutcome observation nontrivial half depth)
    (C.frame observation nontrivial depth half)
    (originalFace observation nontrivial half depth).projection (by intro current occurrence; rfl)

def fixedInitialCarrier : Carrier (originalOutcome observation nontrivial half depth)
    (FD.initial observation nontrivial half depth) :=
  configuredCarrier (originalOutcome observation nontrivial half depth)
    O.factory 0 (O.data observation nontrivial half depth) (O.configuration observation nontrivial half) rfl
    (originalCarrier observation nontrivial half depth)

def fixedCarrier : Carrier (originalOutcome observation nontrivial half depth)
    (FD.packet observation nontrivial half depth ordinal).2.1.1 :=
  ordinalCarrier (originalOutcome observation nontrivial half depth)
    (FD.factory observation nontrivial half)
    (FD.initial observation nontrivial half depth) (FD.firstCfg observation nontrivial half depth) rfl
    (fixedInitialCarrier observation nontrivial half depth) (ordinal + 1)

abbrev sourcePredecessor := D.packetAt (FD.factory observation nontrivial half)
  (FD.initial observation nontrivial half depth) (FD.firstCfg observation nontrivial half depth) rfl ordinal
abbrev sourceNative := AS.nativeAfterAdmission (FD.factory observation nontrivial half)
  (sourcePredecessor observation nontrivial half depth ordinal)
abbrev bornFrame := (AS.bornAfterNative (sourceNative observation nontrivial half depth ordinal)).2.1.1

def bornSourceCarrier : Carrier (originalOutcome observation nontrivial half depth)
    (bornFrame observation nontrivial half depth ordinal) :=
  stoppedCarrier (originalOutcome observation nontrivial half depth)
    (sourceNative observation nontrivial half depth ordinal)
    (nativeCarrier (originalOutcome observation nontrivial half depth)
      (FD.factory observation nontrivial half) (sourcePredecessor observation nontrivial half depth ordinal)
      (ordinalCarrier (originalOutcome observation nontrivial half depth)
        (FD.factory observation nontrivial half)
        (FD.initial observation nontrivial half depth) (FD.firstCfg observation nontrivial half depth) rfl
        (fixedInitialCarrier observation nontrivial half depth) ordinal))

abbrev sourceFrame := WordNative.sourceFrame (FD.factory observation nontrivial half)
  (sourceNative observation nontrivial half depth ordinal)
abbrev sourceBase := WordNative.sourceBase (FD.factory observation nontrivial half)
  (sourceNative observation nontrivial half depth ordinal)

def sourceCarrier : Carrier (originalOutcome observation nontrivial half depth)
    (sourceFrame observation nontrivial half depth ordinal) :=
  sourceSelectedCarrier (originalOutcome observation nontrivial half depth)
    (FD.factory observation nontrivial half)
    (AS.bornAfterNative (sourceNative observation nontrivial half depth ordinal))
    (bornSourceCarrier observation nontrivial half depth ordinal)

def sourceRead {current : (sourceFrame observation nontrivial half depth ordinal).V.Current}
    (occurrence : (sourceFrame observation nontrivial half depth ordinal).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  readFibre (originalOutcome observation nontrivial half depth)
    (sourceFrame observation nontrivial half depth ordinal).old
    (sourceCarrier observation nontrivial half depth ordinal) occurrence

theorem source_read {current : (sourceFrame observation nontrivial half depth ordinal).V.Current}
    (occurrence : (sourceFrame observation nontrivial half depth ordinal).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    sourceRead observation nontrivial half depth ordinal occurrence =
      originalOutcome observation nontrivial half depth :=
  read_fibre_eq _ _ _ _

def inheritedMaterial {current : (sourceFrame observation nontrivial half depth ordinal).V.Current}
    (occurrence : (sourceFrame observation nontrivial half depth ordinal).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    type_of% (originalMaterial observation nontrivial half depth) :=
  match sourceRead observation nontrivial half depth ordinal occurrence with
  | .inl actual => actual.2
  | .inr impossible => nomatch impossible

theorem inherited_material_source {current : (sourceFrame observation nontrivial half depth ordinal).V.Current}
    (occurrence : (sourceFrame observation nontrivial half depth ordinal).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    inheritedMaterial observation nontrivial half depth ordinal occurrence =
      originalMaterial observation nontrivial half depth := by
  unfold inheritedMaterial
  rw [source_read]
  rfl

def readerMaterial
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
      (sourceFrame observation nontrivial half depth ordinal).registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence
      (sourceFrame observation nontrivial half depth ordinal) (current := current)) :=
  inheritedMaterial observation nontrivial half depth ordinal
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
      (sourceFrame observation nontrivial half depth ordinal).registered
      (sourceFrame observation nontrivial half depth ordinal).packetAt supplied)

def actualKReader (rightHalf : 1 / 2 < observation.coordinate.re)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
      (sourceFrame observation nontrivial half depth ordinal).registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence
      (sourceFrame observation nontrivial half depth ordinal) (current := current)) :=
  (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit
    (readerMaterial observation nontrivial half depth ordinal supplied).1).effect.originalK.receiptAt
      (by change 1 / 2 < observation.coordinate.re; exact rightHalf))

theorem actualKReader_source (rightHalf : 1 / 2 < observation.coordinate.re)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
      (sourceFrame observation nontrivial half depth ordinal).registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence
      (sourceFrame observation nontrivial half depth ordinal) (current := current)) :
    (actualKReader observation nontrivial half depth ordinal rightHalf supplied).1 =
        installedOriginalKReceiptAt observation nontrivial rightHalf ∧
      (readerMaterial observation nontrivial half depth ordinal supplied).1 =
        (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence ∧
      (type_of% (runtimeEffectFacadeReadoutAt_factorizes observation nontrivial depth)) := by
  have material : readerMaterial observation nontrivial half depth ordinal supplied =
      originalMaterial observation nontrivial half depth := inherited_material_source _ _ _ _ _ _
  refine ⟨?_, ?_, runtimeEffectFacadeReadoutAt_factorizes observation nontrivial depth⟩
  · dsimp only [actualKReader]
    rw [material]
    rfl
  · rw [material]
    rfl

end OriginalKCofinalFullBranchFibre.KernelWrite.OriginalKInheritance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
