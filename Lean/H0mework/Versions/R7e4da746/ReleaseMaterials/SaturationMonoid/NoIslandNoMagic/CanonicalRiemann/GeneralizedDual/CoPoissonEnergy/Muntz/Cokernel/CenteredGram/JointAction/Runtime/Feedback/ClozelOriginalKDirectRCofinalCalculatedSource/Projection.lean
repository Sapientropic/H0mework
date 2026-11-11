import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalCalculatedSource.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMobiusSourceAction.PhysicalConsumer
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKDirectRCofinalCalculatedSource"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalCalculatedSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open BurnolPhysicalState.OriginalPaPhysicalGreen
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open OriginalKDirectRCofinalMaterial
open scoped InnerProductSpace Topology
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial occurrence)
end R
namespace V
export OriginalKDirectRCofinalMobiusSourceAction
 (actualQuerySource actualQueryTate actualQueryCorrection actualQReentryPairing actualReentryVector
  actual_query_source actual_query_correction_integral actual_query_Pa_physical actual_query_source_physical actual_query_Tate_physical)
end V
namespace FR
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation (completeInput)
end FR
namespace PA
export OriginalKCombCofinalPaAction (E Q actualPa actualPa_mem invisible)
end PA
namespace Prior
export OriginalKDirectRCofinalDivision (sourceCoefficient)
export OriginalKDirectRCofinalPaUpdate (sourceWholeUnit)
end Prior
local instance projectionGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
local instance projectionComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private def castPacketEnvironment
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
 (environment : Env (PairValue (L.Value (PairValue C.Value) packet.1)) packet.2.2.1.LowVar) :
 Env (PairValue (L.Value (PairValue C.Value) packet.1)) C.Var :=
 Eq.mp (congrArg (fun vars=>Env (PairValue (L.Value (PairValue C.Value) packet.1)) vars)
  packet.2.2.2.down) environment

private theorem cast_packet_environment
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
 (environment : Env (PairValue (L.Value (PairValue C.Value) packet.1)) packet.2.2.1.LowVar)
 (actual : HEq environment (pairEnvironment packet.2.1.1.activeEnvironment 0)) :
 castPacketEnvironment packet environment=pairEnvironment packet.2.1.1.activeEnvironment 0 := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at sameVar
  cases sameVar
  simpa only [castPacketEnvironment,Eq.mp] using (eq_of_heq actual)

private def collapseInput (grade : Nat)
 (environment : Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) : BurnolL2 × BurnolL2 :=
 FR.completeInput (fun target name=>CF.collapseValue grade (environment target name)) () ()

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- This read uses the actual normal sourcePayload environment, before the source AST is evaluated. -/
def calculatedInputPair : BurnolL2 × BurnolL2 :=
 let packet:=D.packet observation nontrivial half depth ordinal
 collapseInput packet.1 (castPacketEnvironment packet
  (originalFrontier observation nontrivial half depth ordinal).sourcePayload.environment)
def calculatedInputRaw : BurnolL2 :=
 (calculatedInputPair observation nontrivial half depth ordinal).1+
 (calculatedInputPair observation nontrivial half depth ordinal).2

/-- All four original target slots are retained before their common physical read. -/
def calculatedTargetRaw : BurnolL2 :=
 let packet:=D.packet observation nontrivial half depth ordinal
 let result:=CF.collapseValue packet.1 (calculatedValue observation nontrivial half depth ordinal)
 (result.1.1+result.1.2)+(result.2.1+result.2.2)

def calculatedSourceHistory :=
 (SourceOperationPaidRelations.exposure (calculatedState observation nontrivial half depth ordinal).2).map
  (fun event=>(R.occurrence (D.packet observation nontrivial half depth ordinal).2.1.1
   (D.packet observation nontrivial half depth ordinal).2.2.1,event))

/-- The actual face is a restriction of this exact source-controlled paid history. -/
theorem calculated_face_history_from
 (paid : type_of% (actual_material_calculated_history observation nontrivial half depth ordinal)) :
 (OriginalKDirectRCofinalSourceAction.actualCofinalFace observation nontrivial half depth ordinal).root=
 calculatedSourceHistory observation nontrivial half depth ordinal := by
 have history:=congrArg
  (fun trace : type_of% (calculatedState observation nontrivial half depth ordinal).2=>
   (SourceOperationPaidRelations.exposure trace).map
    (fun event=>(R.occurrence (D.packet observation nontrivial half depth ordinal).2.1.1
     (D.packet observation nontrivial half depth ordinal).2.2.1,event))) paid
 exact (OriginalKDirectRCofinalSourceAction.actual_cofinal_preserves_history observation nontrivial half depth ordinal).trans history

theorem calculated_material_target_from
 (state : type_of% (actual_material_calculated_state observation nontrivial half depth ordinal)) :
 let packet:=D.packet observation nontrivial half depth ordinal
 (R.actualMaterial packet.2.1.1 packet.2.2.1).state.1=
 .const (calculatedValue observation nontrivial half depth ordinal) :=
 (congrArg (fun current : type_of% (calculatedState observation nontrivial half depth ordinal)=>current.1) state).trans
  (calculated_complete_target observation nontrivial half depth ordinal)

theorem calculated_normal_control : type_of% (originalNormal observation nontrivial half depth ordinal).target_factorizes :=
 (originalNormal observation nontrivial half depth ordinal).target_factorizes

theorem calculated_input_pair :
 calculatedInputPair observation nontrivial half depth ordinal=D.input observation nontrivial half depth ordinal := by
 exact congrArg (collapseInput (D.packet observation nontrivial half depth ordinal).1)
  (cast_packet_environment (D.packet observation nontrivial half depth ordinal)
   (originalFrontier observation nontrivial half depth ordinal).sourcePayload.environment
   (source_payload_literal observation nontrivial half depth ordinal).2)

theorem calculated_input_raw :
 calculatedInputRaw observation nontrivial half depth ordinal=D.raw observation nontrivial half depth ordinal :=
 congrArg (fun input : BurnolL2 × BurnolL2=>input.1+input.2)
  (calculated_input_pair observation nontrivial half depth ordinal)

theorem calculated_source_Pa :
 PA.E (calculatedInputRaw observation nontrivial half depth ordinal)=PA.actualPa observation nontrivial half depth ordinal :=
 congrArg PA.E (calculated_input_raw observation nontrivial half depth ordinal)

theorem calculated_source_nu :
 burnolMobiusSourceL2 (PA.E (calculatedInputRaw observation nontrivial half depth ordinal))=
 V.actualQuerySource observation nontrivial half depth ordinal :=
 (congrArg burnolMobiusSourceL2 (calculated_source_Pa observation nontrivial half depth ordinal)).trans
  (V.actual_query_source observation nontrivial half depth ordinal).symm

theorem calculated_source_Tate :
 burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (calculatedInputRaw observation nontrivial half depth ordinal)))=
 V.actualQueryTate observation nontrivial half depth ordinal :=
 congrArg burnolTateReciprocalL2 (calculated_source_nu observation nontrivial half depth ordinal)

theorem calculated_source_correction :
 sourceVolterraPhysical (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (calculatedInputRaw observation nontrivial half depth ordinal))))=
 V.actualQueryCorrection observation nontrivial half depth ordinal :=
 congrArg (sourceVolterraPhysical (burnolDivisionZeroCompletedMellinCoordinate observation half.down))
  (calculated_source_Tate observation nontrivial half depth ordinal)

theorem calculated_source_Q_driver :
 inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4))
  (PA.Q (calculatedInputRaw observation nontrivial half depth ordinal) : BurnolL2)=
 V.actualQReentryPairing observation nontrivial half depth ordinal :=
 congrArg (fun value : BurnolL2=>inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4))
  (PA.Q value : BurnolL2)) (calculated_input_raw observation nontrivial half depth ordinal)

theorem calculated_target_raw :
 calculatedTargetRaw observation nontrivial half depth ordinal=D.raw observation nontrivial half depth (ordinal+1) :=
 calculated_target_raw_successor observation nontrivial half depth ordinal

theorem calculated_target_Pa :
 PA.E (calculatedTargetRaw observation nontrivial half depth ordinal)=PA.actualPa observation nontrivial half depth (ordinal+1) :=
 congrArg PA.E (calculated_target_raw observation nontrivial half depth ordinal)

theorem calculated_target_nu :
 burnolMobiusSourceL2 (PA.E (calculatedTargetRaw observation nontrivial half depth ordinal))=
 V.actualQuerySource observation nontrivial half depth (ordinal+1) :=
 (congrArg burnolMobiusSourceL2 (calculated_target_Pa observation nontrivial half depth ordinal)).trans
  (V.actual_query_source observation nontrivial half depth (ordinal+1)).symm

theorem calculated_Pa_action :
 PA.E (calculatedTargetRaw observation nontrivial half depth ordinal)=
 sourceVolterraPhysical (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (calculatedInputRaw observation nontrivial half depth ordinal))))+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
 inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4))
  (PA.Q (calculatedInputRaw observation nontrivial half depth ordinal) : BurnolL2) • V.actualReentryVector observation half := by
 calc
  _ = PA.actualPa observation nontrivial half depth (ordinal+1) := calculated_target_Pa observation nontrivial half depth ordinal
  _ = _ := V.actual_query_Pa_physical observation nontrivial half depth ordinal
  _ = _ := by rw [calculated_source_correction,calculated_source_Q_driver]

theorem calculated_nu_action :
 burnolMobiusSourceL2 (PA.E (calculatedTargetRaw observation nontrivial half depth ordinal))=
 burnolTateReciprocalL2 (sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (calculatedInputRaw observation nontrivial half depth ordinal)))))+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2))+
 inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4))
  (PA.Q (calculatedInputRaw observation nontrivial half depth ordinal) : BurnolL2) • burnolMobiusSourceL2 (V.actualReentryVector observation half) := by
 calc
  _ = V.actualQuerySource observation nontrivial half depth (ordinal+1) := calculated_target_nu observation nontrivial half depth ordinal
  _ = _ := V.actual_query_source_physical observation nontrivial half depth ordinal
  _ = _ := by rw [calculated_source_Tate,calculated_source_Q_driver]

theorem calculated_Tate_action :
 burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (calculatedTargetRaw observation nontrivial half depth ordinal)))=
 sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (calculatedInputRaw observation nontrivial half depth ordinal))))+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)))+
 inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4))
  (PA.Q (calculatedInputRaw observation nontrivial half depth ordinal) : BurnolL2) • burnolTateReciprocalL2 (burnolMobiusSourceL2 (V.actualReentryVector observation half)) := by
 calc
  _ = V.actualQueryTate observation nontrivial half depth (ordinal+1) := congrArg burnolTateReciprocalL2 (calculated_target_nu observation nontrivial half depth ordinal)
  _ = _ := V.actual_query_Tate_physical observation nontrivial half depth ordinal
  _ = _ := by rw [calculated_source_Tate,calculated_source_Q_driver]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalCalculatedSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
