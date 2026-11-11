import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCompleteProjection
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCountedPaPrice.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativePaInstall
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
open OriginalRieszFinitePairing.CoPoisson.Ward
namespace P
export BornRCountedPaPrice
 (pa pa_member unit correction alpha returning eta outside wholeNext paNext qNext outsideNext tateNext sourceFee
  whole_next_actual pa_next_actual q_next_actual outside_next_actual tate_next_actual source_fee_actual eta_inventory pa_response_unit_rank)
end P
namespace C
export CompletedSourceRCalculation (Value Slot)
end C
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base)
end S
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R"=>burnolDirectRightResolventCLM c

structure Dynamics (input:BurnolL2) where
 whole:BurnolL2
 Pa:BurnolPaAmbientCarrier
 Q:BurnolPaAmbientCarrier
 outside:BurnolL2
 Tate:BurnolL2
 unitPa:BurnolPaAmbientCarrier
 unitQ:BurnolPaAmbientCarrier
 invisible:BurnolL2
 reentry:ℂ
 fee:ℂ
 whole_source:whole=P.wholeNext observation nontrivial half input
 whole_actual:whole=R input
 Pa_actual:Pa=OriginalKCombCofinalPaAction.E whole
 Q_actual:Q=OriginalKCombCofinalPaAction.Q whole
 outside_actual:outside=P.outside whole
 Tate_actual:Tate=burnolTateReciprocalL2 (burnolMobiusSourceL2 Pa)
 unitPa_source:unitPa=OriginalKCombCofinalPaAction.E (P.unit observation nontrivial half:BurnolL2)
 unitQ_source:unitQ=OriginalKCombCofinalPaAction.Q (P.unit observation nontrivial half:BurnolL2)
 invisible_source:invisible=OriginalKCombCofinalPaAction.invisible input
 full_invisible:type_of% (P.eta_inventory observation half input)
 fee_source:fee=P.sourceFee observation nontrivial half input
 fee_actual:fee=BornRCountedPaPrice.OldPrices.actualPaFee observation half (whole-input)

def dynamics (input:BurnolL2):Dynamics observation nontrivial half input where
 whole:=P.wholeNext observation nontrivial half input
 Pa:=P.paNext observation nontrivial half input
 Q:=P.qNext observation nontrivial half input
 outside:=P.outsideNext observation half input
 Tate:=P.tateNext observation nontrivial half input
 unitPa:=OriginalKCombCofinalPaAction.E (P.unit observation nontrivial half:BurnolL2)
 unitQ:=OriginalKCombCofinalPaAction.Q (P.unit observation nontrivial half:BurnolL2)
 invisible:=OriginalKCombCofinalPaAction.invisible input
 reentry:=P.eta observation half input
 fee:=P.sourceFee observation nontrivial half input
 whole_source:=rfl
 whole_actual:=P.whole_next_actual observation nontrivial half input
 Pa_actual:=by rw [P.whole_next_actual];exact P.pa_next_actual observation nontrivial half input
 Q_actual:=by rw [P.whole_next_actual];exact P.q_next_actual observation nontrivial half input
 outside_actual:=by rw [P.whole_next_actual];exact P.outside_next_actual observation nontrivial half input
 Tate_actual:=by rw [P.pa_next_actual];exact P.tate_next_actual observation nontrivial half input
 unitPa_source:=rfl
 unitQ_source:=rfl
 invisible_source:=rfl
 full_invisible:=P.eta_inventory observation half input
 fee_source:=rfl
 fee_actual:=by rw [P.whole_next_actual];exact P.source_fee_actual observation nontrivial half input

structure Material (input:C.Value .branches) where
 source:C.Value .branches
 source_read:source=input
 fullR:C.Value .branches
 fullR_source:fullR=OriginalKFullSourceRAction.variableAction observation nontrivial half source
 physical:Dynamics observation nontrivial half source.1.1
 physical_R:physical.whole=fullR.1.1

def material (input:C.Value .branches):Material observation nontrivial half input where
 source:=input
 source_read:=rfl
 fullR:=OriginalKFullSourceRAction.variableAction observation nontrivial half input
 fullR_source:=rfl
 physical:=dynamics observation nontrivial half input.1.1
 physical_R:=P.whole_next_actual observation nontrivial half input.1.1

-- Every counting cutoff is a dependent mathematical read of this installed source, never a future runtime table.
def counted (input:C.Value .branches) (cutoff:Nat):
 Dynamics observation nontrivial half (DualSource.source cutoff input.1.1):=
 dynamics observation nontrivial half _

theorem counted_R (input:C.Value .branches) (cutoff:Nat):
 (counted observation nontrivial half input cutoff).whole=
 DualSource.source cutoff (material observation nontrivial half input).fullR.1.1:=by
 rw [(counted observation nontrivial half input cutoff).whole_actual,BornRFiniteOrderPrice.R_dual_source]
 rfl

section Native
variable {Sorts:Type} {U Y:Sorts→Type} [∀t,AddCommGroup (U t)] {s:Sorts}
variable (frame:M.Frame (Value:=U) (Var:=Y) (sort:=s))
variable (input:C.Value .branches)
def component:SourceNativeProjectionLaw (S.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit
 ActiveAt:=fun _ {_current} _=>PUnit
 InactiveAt:=fun _ {_current} _=>PEmpty
 classify:=fun _ {_current} _=>.inl PUnit.unit
 PayloadAt:=fun _ {_current} _ _=>Material observation nontrivial half input
 project:=fun _ {_current} _ _=>material observation nontrivial half input
end Native
end CountedPaInitial.BornRNativePaInstall
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
