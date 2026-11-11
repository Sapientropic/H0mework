import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Readback

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open CenteredGram.IntegralGraphJointAction
open private source datum observedTrace compiledOccurrence compiled_state_source source_nu_projection from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Readback
local instance consumerGroups (n:Nat):∀t,AddCommGroup (Lower.Value A.W n t):=
 BornRCanonicalMethodRuntime.levelGroups n
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "slot"=>CompletedSourceRCalculation.Slot.branches
local notation "factory"=>A.fixedRFactory observation nontrivial half
local notation "initial"=>H.receiver observation nontrivial half depth ordinal
local notation "pR"=>H.methodProgramme observation nontrivial half depth ordinal


attribute [local irreducible] installedMethod

theorem actual_effect_source (update cutoff:Nat):
 M.wholeProjection ((source observation nontrivial half depth ordinal update cutoff).1+1)
  (ScalarRelationPresentation.freeEvaluation (R:=ℤ) _ (actualNu observation nontrivial half depth ordinal update cutoff))=
 (installedMethod observation nontrivial half depth ordinal update cutoff).payload.2.1.fullR-
 (installedMethod observation nontrivial half depth ordinal update cutoff).payload.2.1.source:=by
 have nuSource:=actual_nu_source observation nontrivial half depth ordinal update cutoff
 let method:=installedMethod observation nontrivial half depth ordinal update cutoff
 have projectedNu:=congrArg
  (fun value=>M.wholeProjection ((source observation nontrivial half depth ordinal update cutoff).1+1)
   (ScalarRelationPresentation.freeEvaluation (R:=ℤ) _ value)) nuSource
 have projected:=source_nu_projection observation nontrivial half (source observation nontrivial half depth ordinal update cutoff)
 have input:=method.payload.2.1.source_read
 have full:=method.payload.2.1.fullR_source
 have output:
  OriginalKFullSourceRAction.variableAction observation nontrivial half
   (A.nativeStock method.method.source.1 method.method.source.2.1.1)=method.payload.2.1.fullR:=
  (congrArg (fun value:CompletedSourceRCalculation.Value .branches=>
    OriginalKFullSourceRAction.variableAction observation nontrivial half value) input.symm).trans full.symm
 have delta:
  OriginalKFullSourceRAction.variableAction observation nontrivial half
    (A.nativeStock method.method.source.1 method.method.source.2.1.1)-
   A.nativeStock method.method.source.1 method.method.source.2.1.1=
   method.payload.2.1.fullR-method.payload.2.1.source:=
  congrArg₂ (fun left right:CompletedSourceRCalculation.Value .branches=>left-right) output input.symm
 have valueEffect:=@Eq.trans (CompletedSourceRCalculation.Value .branches) _ _ _ projectedNu projected
 have result:=@Eq.trans (CompletedSourceRCalculation.Value .branches) _ _ _ valueEffect delta
 unfold method at result
 exact result
private theorem price_of_delta (reader:BurnolL2→L[ℂ]ℂ) (outcome input actualOut actualIn:BurnolL2)
 (bill:ℂ) (outRead:outcome=actualOut) (inRead:input=actualIn)
 (paid:reader outcome-reader input=bill):bill=reader (actualOut-actualIn):=by
 rw [map_sub,←outRead,←inRead]
 exact paid.symm

set_option cleanup.letToHave false in
noncomputable def actualWordValue (update cutoff:Nat):
 Lower.Value A.W ((source observation nontrivial half depth ordinal update cutoff).1+1) slot:=
 let faces:=actualEffectFaces observation nontrivial half depth ordinal update cutoff
 faces.embedding (faces.canonical
  (A.nativeWordData observation nontrivial half
   (source observation nontrivial half depth ordinal update cutoff).1
   (source observation nontrivial half depth ordinal update cutoff).2.1.1).omega)

theorem actual_word_value (update cutoff:Nat):
 actualWordValue observation nontrivial half depth ordinal update cutoff=
 ScalarRelationPresentation.freeEvaluation (R:=ℤ) _
  (actualNu observation nontrivial half depth ordinal update cutoff):=
 TraceFaces.actual_effect (compiledOccurrence observation nontrivial half depth ordinal update cutoff)
  (observedTrace observation nontrivial half depth ordinal update cutoff)

def actualEffect (update cutoff:Nat):BurnolL2:=
 (M.wholeProjection ((source observation nontrivial half depth ordinal update cutoff).1+1)
  (actualWordValue observation nontrivial half depth ordinal update cutoff)).1.1

theorem actual_word_bill (update cutoff:Nat):
 (installedMethod observation nontrivial half depth ordinal update cutoff).payload.1.bill=
 CofinalQSource.priceCLM observation half cutoff (actualEffect observation nontrivial half depth ordinal update cutoff):=by
 let price:BurnolL2→L[ℂ]ℂ:=CofinalQSource.priceCLM observation half cutoff
 change _=price
  (M.wholeProjection ((source observation nontrivial half depth ordinal update cutoff).1+1)
   (actualWordValue observation nontrivial half depth ordinal update cutoff)).1.1
 have wordValue:=actual_word_value observation nontrivial half depth ordinal update cutoff
 have priceWord:=congrArg
  (fun value:Lower.Value A.W ((source observation nontrivial half depth ordinal update cutoff).1+1) slot=>price
   (M.wholeProjection ((source observation nontrivial half depth ordinal update cutoff).1+1)
    value).1.1) wordValue
 have full:=actual_effect_source observation nontrivial half depth ordinal update cutoff
 have output:M.packetStock (installedMethod observation nontrivial half depth ordinal update cutoff).method.source=M.actualStock observation nontrivial half depth ordinal (update+1):=
  congrArg M.packetStock (installedMethod observation nontrivial half depth ordinal update cutoff).method.source_literal
 have input:=(installedMethod observation nontrivial half depth ordinal update cutoff).method.source_input
 have result:=price_of_delta price
  (M.packetStock (installedMethod observation nontrivial half depth ordinal update cutoff).method.source).1.1 (BornRSourcePrice.inputAtPacket (installedMethod observation nontrivial half depth ordinal update cutoff).method.source).1.1
  (installedMethod observation nontrivial half depth ordinal update cutoff).payload.2.1.fullR.1.1 (installedMethod observation nontrivial half depth ordinal update cutoff).payload.2.1.source.1.1 (installedMethod observation nontrivial half depth ordinal update cutoff).payload.1.bill
  (congrArg (fun value:CompletedSourceRCalculation.Value .branches=>value.1.1) (output.trans (installedMethod observation nontrivial half depth ordinal update cutoff).complete_R.symm))
  (congrArg (fun value:CompletedSourceRCalculation.Value .branches=>value.1.1) (input.trans (installedMethod observation nontrivial half depth ordinal update cutoff).actual_source.symm))
  (installedMethod observation nontrivial half depth ordinal update cutoff).payload.1.price_read
 have billDelta:
  (installedMethod observation nontrivial half depth ordinal update cutoff).payload.1.bill=
   price
    (M.wholeProjection ((source observation nontrivial half depth ordinal update cutoff).1+1)
     (actualWordValue observation nontrivial half depth ordinal update cutoff)).1.1:=
  (result.trans (congrArg price
   (congrArg (fun value:CompletedSourceRCalculation.Value .branches=>value.1.1) full).symm)).trans
   priceWord.symm
 exact billDelta

theorem actual_word_fee (update cutoff:Nat):
 (installedMethod observation nontrivial half depth ordinal update cutoff).payload.2.2.1.fee=
 BornRCountedPaPrice.OldPrices.actualPaFee observation half
  (OriginalRieszFinitePairing.CoPoisson.Ward.DualSource.source cutoff
   (actualEffect observation nontrivial half depth ordinal update cutoff)):=by
 let paFee:BurnolL2→ℂ:=fun value=>BornRCountedPaPrice.OldPrices.actualPaFee observation half
  (OriginalRieszFinitePairing.CoPoisson.Ward.DualSource.source cutoff value)
 change (installedMethod observation nontrivial half depth ordinal update cutoff).payload.2.2.1.fee=paFee (actualEffect observation nontrivial half depth ordinal update cutoff)
 have full:=actual_effect_source observation nontrivial half depth ordinal update cutoff
 have effect:actualEffect observation nontrivial half depth ordinal update cutoff=
  (M.actualStock observation nontrivial half depth ordinal (update+1)).1.1-
  (M.actualStock observation nontrivial half depth ordinal update).1.1:=
  (congrArg (fun value=>
    (M.wholeProjection ((source observation nontrivial half depth ordinal update cutoff).1+1) value).1.1)
    (actual_word_value observation nontrivial half depth ordinal update cutoff)).trans
   ((congrArg (fun value:CompletedSourceRCalculation.Value .branches=>value.1.1) full).trans
   (congrArg₂ (fun left right:CompletedSourceRCalculation.Value .branches=>left.1.1-right.1.1)
    (installedMethod observation nontrivial half depth ordinal update cutoff).complete_R (installedMethod observation nontrivial half depth ordinal update cutoff).actual_source))
 have feeDelta:=(installedMethod observation nontrivial half depth ordinal update cutoff).source_fee
 change (installedMethod observation nontrivial half depth ordinal update cutoff).payload.2.2.1.fee=
  BornRCountedPaPrice.OldPrices.actualPaFee observation half
   (OriginalRieszFinitePairing.CoPoisson.Ward.DualSource.source cutoff
    ((M.actualStock observation nontrivial half depth ordinal (update+1)).1.1-
     (M.actualStock observation nontrivial half depth ordinal update).1.1)) at feeDelta
 have feeEffect:=congrArg
  (fun value:BurnolL2=>paFee value) effect
 unfold paFee at feeEffect ⊢
 have feeResult:=feeDelta.trans feeEffect.symm
 exact feeResult

end CountedPaInitial.BornRWordPaWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

-- Avoid re-normalizing this rooted receipt for editor suggestions at module export.
run_cmd Lean.modifyEnv fun env =>
 Lean.LibrarySuggestions.nameDenyListExt.addEntry env "BornRWordPaWriteback"
