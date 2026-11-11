import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCountedPaPrice.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativePaInstall.Installation

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory uFeedback
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativePaInstall
open private read_price_payload read_price_payload_source from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRSourcePrice.Consumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
open OriginalRieszFinitePairing.CoPoisson.Ward
namespace NPrice
export BornRSourcePrice (PriceAnswer SourcePriceMethodReceipt actual_source_price_method actualPriceAnswer native_input_source)
end NPrice
namespace M
export BornRSealedMethodHistory (actualStock actualStock_step)
end M
namespace Counted
export BornRCountedPaPrice
 (countedStock counted_stock_next actual_source_fee actual_counted_Pa_price actual_source_counted_Pa_price_feedback)
end Counted
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "c"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m"=>generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "aJ"=>OriginalKCrossParameterRAdjointSource.SharedOutsideSource.jQuarterAmplitude c
local notation "aH"=>OriginalKDirectRCofinalOutsideVolterraSource.hQuarterAmplitude c
local notation "current"=>M.actualStock observation nontrivial half depth ordinal
local notation "Method"=>NPrice.SourcePriceMethodReceipt observation nontrivial half depth ordinal

private theorem installed_source {Parent:Sort uParent} {Index:Sort uIndex}
 {Whole:Sort uWhole} {Next:Sort uNext} {HistoryEnd:Sort uHistoryEnd} {History:Sort uHistory}
 {update cutoff:Nat}
 (method:NPrice.SourcePriceMethodReceipt (Parent:=Parent) (Index:=Index) (Whole:=Whole)
  (Next:=Next) (HistoryEnd:=HistoryEnd) (History:=History)
  observation nontrivial half depth ordinal update cutoff):
 method.native.read.source=current update :=
 (NPrice.native_input_source observation nontrivial half method.source method.native).trans method.source_input

private abbrev PricePaPayload
 (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=CompletedSourceRCalculation.Slot.branches))
 (native:Installed observation nontrivial half source) (cutoff:Nat):=
 PProd (NPrice.PriceAnswer observation nontrivial half source cutoff)
  (PProd (Material observation nontrivial half (A.nativeStock source.1 source.2.1.1))
   (PProd (Dynamics observation nontrivial half (DualSource.source cutoff native.read.source.1.1))
    (BornRNativeGammaInstall.ActionMaterial observation nontrivial half (A.nativeStock source.1 source.2.1.1))))

private def compiled_payload {Parent:Sort uParent} {Index:Sort uIndex}
 {Whole:Sort uWhole} {Next:Sort uNext} {HistoryEnd:Sort uHistoryEnd} {History:Sort uHistory}
 {update cutoff:Nat}
 (method:NPrice.SourcePriceMethodReceipt (Parent:=Parent) (Index:=Index) (Whole:=Whole)
  (Next:=Next) (HistoryEnd:=HistoryEnd) (History:=History)
  observation nontrivial half depth ordinal update cutoff):
 PricePaPayload observation nontrivial half method.source method.native cutoff:=
 read_price_payload (Payload:=PricePaPayload observation nontrivial half method.source method.native cutoff)
  method.price_method.2.1

structure InstalledPaPriceReceipt {Parent:Sort uParent} {Index:Sort uIndex}
 {Whole:Sort uWhole} {Next:Sort uNext} {HistoryEnd:Sort uHistoryEnd} {History:Sort uHistory}
 {Feedback:Sort uFeedback} (update cutoff:Nat) where
 method:NPrice.SourcePriceMethodReceipt (Parent:=Parent) (Index:=Index) (Whole:=Whole)
  (Next:=Next) (HistoryEnd:=HistoryEnd) (History:=History)
  observation nontrivial half depth ordinal update cutoff
 payload:PricePaPayload observation nontrivial half method.source method.native cutoff
 compiler_payload:payload=compiled_payload observation nontrivial half depth ordinal method
 actual_source:payload.2.1.source=current update
 complete_R:payload.2.1.fullR=current (update+1)
 whole_update:payload.2.2.1.whole=
  Counted.countedStock observation nontrivial half depth ordinal (update+1) cutoff
 Pa_update:payload.2.2.1.Pa=
  OriginalKCombCofinalPaAction.E (Counted.countedStock observation nontrivial half depth ordinal (update+1) cutoff)
 Q_update:payload.2.2.1.Q=
  OriginalKCombCofinalPaAction.Q (Counted.countedStock observation nontrivial half depth ordinal (update+1) cutoff)
 outside_update:payload.2.2.1.outside=
  P.outside (Counted.countedStock observation nontrivial half depth ordinal (update+1) cutoff)
 Tate_update:payload.2.2.1.Tate=
  burnolTateReciprocalL2 (burnolMobiusSourceL2
   (OriginalKCombCofinalPaAction.E (Counted.countedStock observation nontrivial half depth ordinal (update+1) cutoff)))
 source_fee:payload.2.2.1.fee=
  BornRCountedPaPrice.OldPrices.actualPaFee observation half
   (BornRFiniteOrderPrice.countedIncrement observation nontrivial half depth ordinal update cutoff)
 price_feedback:
  star aJ*(NPrice.actualPriceAnswer observation nontrivial half depth ordinal (update+m) cutoff).originalKDelta-
  star aH*(NPrice.actualPriceAnswer observation nontrivial half depth ordinal (update+m) cutoff).originalFKDelta=
  payload.2.2.1.fee+
   payload.1.bill+
   BornRFiniteOrderPrice.Prices.actualOutsidePrice observation half
    (BornRFiniteOrderPrice.countedIncrement observation nontrivial half depth ordinal update cutoff)
 counted_receipt:Feedback

private def assemble_installed {Parent:Sort uParent} {Index:Sort uIndex}
 {Whole:Sort uWhole} {Next:Sort uNext} {HistoryEnd:Sort uHistoryEnd} {History:Sort uHistory}
 {Feedback:Sort uFeedback} (update cutoff:Nat)
 (method:NPrice.SourcePriceMethodReceipt (Parent:=Parent) (Index:=Index) (Whole:=Whole)
  (Next:=Next) (HistoryEnd:=HistoryEnd) (History:=History)
  observation nontrivial half depth ordinal update cutoff) (feedback:Feedback):
 InstalledPaPriceReceipt (Parent:=Parent) (Index:=Index) (Whole:=Whole) (Next:=Next)
  (HistoryEnd:=HistoryEnd) (History:=History) (Feedback:=Feedback)
  observation nontrivial half depth ordinal update cutoff := by
 have source:=installed_source observation nontrivial half depth ordinal method
 let payload:=compiled_payload observation nontrivial half depth ordinal method
 have payloadSource:payload=PProd.mk method.answer
  (PProd.mk method.native.read
   (PProd.mk (counted observation nontrivial half method.native.read.source cutoff) method.gammaNative.read)):=
  read_price_payload_source method.price_method.2.1
 have actualSource:payload.2.1.source=current update:=
  (congrArg (fun value=>value.2.1.source) payloadSource).trans source
 have actualFullR:payload.2.1.fullR=current (update+1):=
  payload.2.1.fullR_source.trans
   ((congrArg (OriginalKFullSourceRAction.variableAction observation nontrivial half) actualSource).trans
    (M.actualStock_step observation nontrivial half depth ordinal update).symm)
 have input:DualSource.source cutoff method.native.read.source.1.1=
  Counted.countedStock observation nontrivial half depth ordinal update cutoff:=
  congrArg (fun value:CompletedSourceRCalculation.Value .branches=>DualSource.source cutoff value.1.1) source
 let dynamics:=payload.2.2.1
 have whole:dynamics.whole=Counted.countedStock observation nontrivial half depth ordinal (update+1) cutoff:=
  dynamics.whole_actual.trans
   ((congrArg (burnolDirectRightResolventCLM c) input).trans
    (Counted.counted_stock_next observation nontrivial half depth ordinal update cutoff).symm)
 have pa:=dynamics.Pa_actual.trans (congrArg OriginalKCombCofinalPaAction.E whole)
 have q:=dynamics.Q_actual.trans (congrArg OriginalKCombCofinalPaAction.Q whole)
 have outside:=dynamics.outside_actual.trans (congrArg P.outside whole)
 have tate:=dynamics.Tate_actual.trans
  (congrArg (fun value:BurnolPaAmbientCarrier=>burnolTateReciprocalL2 (burnolMobiusSourceL2 value)) pa)
 have fee:dynamics.fee=P.sourceFee observation nontrivial half
  (Counted.countedStock observation nontrivial half depth ordinal update cutoff):=
  dynamics.fee_source.trans (congrArg (P.sourceFee observation nontrivial half) input)
 have bill:payload.1.bill=(NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).bill:=by
  have read:=congrArg (fun value=>value.1.bill) payloadSource
  have same:method.answer.bill=(NPrice.actualPriceAnswer observation nontrivial half depth ordinal update cutoff).bill:=
   method.answer.bill_source.trans
    ((congrArg (BornRSourcePrice.generatedBill observation nontrivial half cutoff)
      (congrArg (fun value:CompletedSourceRCalculation.Value .branches=>value.1.1) method.source_input)).trans
     (BornRFiniteOrderPrice.actual_bill_source observation nontrivial half depth ordinal update cutoff).symm)
  exact read.trans same
 have price:=Counted.actual_counted_Pa_price observation nontrivial half depth ordinal update cutoff
 rw [←fee,←bill] at price
 exact {
  method:=method
  payload:=payload
  compiler_payload:=rfl
  actual_source:=actualSource
  complete_R:=actualFullR
  whole_update:=whole
  Pa_update:=pa
  Q_update:=q
  outside_update:=outside
  Tate_update:=tate
  source_fee:=fee.trans (Counted.actual_source_fee observation nontrivial half depth ordinal update cutoff)
  price_feedback:=price
  counted_receipt:=feedback }

def actual_installed_Pa_dynamics_price (update cutoff:Nat):=
 assemble_installed observation nontrivial half depth ordinal update cutoff
  (NPrice.actual_source_price_method observation nontrivial half depth ordinal update cutoff)
  (Counted.actual_source_counted_Pa_price_feedback observation nontrivial half depth ordinal update cutoff)

end CountedPaInitial.BornRNativePaInstall
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
