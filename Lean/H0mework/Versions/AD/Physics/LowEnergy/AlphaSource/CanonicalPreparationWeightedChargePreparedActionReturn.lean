import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeightedChargeCoreWard

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumWeightedChargeActionWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert GaussFockPair
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial CanonicalGradedCharge
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets PreparationVacuumNoetherChart
open PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge PreparationVacuumLowerClassical
open PreparationVacuumFullElectricWard PreparationVacuumActionFieldLift PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumNonlinearFieldCurve PreparationVacuumOriginalDensity
open PreparationVacuumFieldConstraintResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumNoetherOrdinaryWard PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalHalfAxis PreparationVacuumUncutYukawa PreparationVacuumYukawaTransport
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] noetherReader rawChargeCore weightCore normalChargeCore weightedWardCore
  sourceHamiltonian preparedDual preparedPrimal physicalTime jointResolvent

/-- The integral is the original fullGauss core action, rather than a replacement preparation. -/
theorem weightedTemporalForm_core (a : Fin 12) (l r : QuantumTest) :
    weightedTemporalForm a l r=sourcePair l (rawChargeCore a r) :=by
  rw [←temporalForm_source a 0,noetherForm_source,rawForm,sourcePair_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  rw [←pairSample_source]
  unfold rawChargeCore
  change pairSample z (l z) (rawFiber (temporalField a) 0 (0,z) (r z))=
    pairSample z (l z) (rawChargeFiber a z (r z))
  rfl

theorem temporalReader_core (a : Fin 12) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (temporalField a) p F 0=
      finiteRiesz F (fun i j=>sourcePair (frameTest F i) (rawChargeCore a (frameTest F j))) :=by
  rw [temporalReader_source]
  exact congrArg (finiteRiesz F) (funext (fun i=>funext (fun j=>weightedTemporalForm_core a _ _)))

theorem temporalReader_projected_action (a : Fin 12) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    noetherReader (temporalField a) p F 0 y=
      sourceApprox F (embed (rawChargeCore a (sourceTestApprox F y))) :=by
  rw [temporalReader_core,sourceApprox_frame,sourceTestApprox_frame]
  simp only [finiteRiesz,sum_apply,smul_apply,InnerProductSpace.rankOne_apply,
    map_sum,map_smul,inner_sum,inner_smul_right,Finset.sum_smul,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold sourcePair
  rw [frameTest_embed]
  congr 1
  ring

theorem sourceApprox_add (F : GaussUnitaryHistory.Index) (x y : H) :
    sourceApprox F (x+y)=sourceApprox F x+sourceApprox F y :=by
  simp only [sourceApprox_frame,inner_add_right,add_smul,Finset.sum_add_distrib]

theorem sourceTestApprox_add (F : GaussUnitaryHistory.Index) (x y : H) :
    sourceTestApprox F (x+y)=sourceTestApprox F x+sourceTestApprox F y :=by
  simp only [sourceTestApprox_frame,inner_add_right,add_smul,Finset.sum_add_distrib]

theorem sourceApprox_sub (F : GaussUnitaryHistory.Index) (x y : H) :
    sourceApprox F (x-y)=sourceApprox F x-sourceApprox F y :=by
  simp only [sourceApprox_frame,inner_sub_right,sub_smul,Finset.sum_sub_distrib]

/-- Actual CF compression and the original source retainer remain independent responsibilities. -/
def sourceUncutAction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H:=
  uncutOperator 0 (finiteRetainer p F) 0

theorem sourceHamiltonian_original (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceHamiltonian p F=compression p F+sourceUncutAction p F :=by
  simpa only [sourceHamiltonian,actualC,actualA,sourceUncutAction] using actualGenerator_source p F

def leftCompressionDefect (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (f : QuantumTest) : H:=
  compression p F (sourceApprox F (embed f))-sourceApprox F (embed (physicalAction p f))

def leftUncutDefect (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (f : QuantumTest) : H:=
  sourceUncutAction p F (sourceApprox F (embed f))-sourceApprox F (embed (GaussYukawaOperator.originalAction f))

def rightCompressionDefect (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) : QuantumTest:=
  sourceTestApprox F (compression p F y)-physicalAction p (sourceTestApprox F y)

def rightUncutDefect (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) : QuantumTest:=
  sourceTestApprox F (sourceUncutAction p F y)-GaussYukawaOperator.originalAction (sourceTestApprox F y)

theorem rightAction_source (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    sourceTestApprox F (sourceHamiltonian p F y)=fullSourceAction p (sourceTestApprox F y)+
      rightCompressionDefect p F y+rightUncutDefect p F y :=by
  rw [sourceHamiltonian_original,add_apply,sourceTestApprox_add]
  simp only [rightCompressionDefect,rightUncutDefect,fullSourceAction,LinearMap.add_apply]
  abel

theorem leftAction_source (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (f : QuantumTest) :
    sourceHamiltonian p F (sourceApprox F (embed f))=
      sourceApprox F (embed (fullSourceAction p f))+leftCompressionDefect p F f+leftUncutDefect p F f :=by
  rw [sourceHamiltonian_original,add_apply]
  simp only [leftCompressionDefect,leftUncutDefect,fullSourceAction,LinearMap.add_apply,map_add,sourceApprox_add]
  abel

/-- The complete prepared insertion consumes the actual weighted source action Ward. -/
theorem temporalInsertion_action_return (q : PhysicalResponsePoint) (a : Fin 12) (y : H) :
    noetherTimeInsertion q (temporalField a) y=
      sourceApprox q.F (embed (weightedWardCore q.p q.k a (sourceTestApprox q.F y)))+
        leftCompressionDefect (q.p+q.k) q.F (rawChargeCore a (sourceTestApprox q.F y))+
        leftUncutDefect (q.p+q.k) q.F (rawChargeCore a (sourceTestApprox q.F y))-
        sourceApprox q.F (embed (rawChargeCore a
          (rightCompressionDefect q.p q.F y+rightUncutDefect q.p q.F y))) :=by
  simp only [noetherTimeInsertion,sub_apply,mul_apply_eq_comp,temporalReader_projected_action]
  rw [leftAction_source,rightAction_source]
  simp only [map_add,sourceApprox_add]
  have action:=rawCharge_original_action_ward q.p q.k a (sourceTestApprox q.F y)
  have projected:=congrArg (fun f : QuantumTest=>sourceApprox q.F (embed f)) action
  simp only [map_sub,sourceApprox_sub] at projected
  rw [←projected]
  abel

def preparedWardChannels (q : PhysicalResponsePoint) (a : Fin 12) (t : ℝ) : H:=
  sourceApprox q.F (embed (weightedWardCore q.p q.k a (sourceTestApprox q.F (preparedPrimal q 0 t))))+
    leftCompressionDefect (q.p+q.k) q.F (rawChargeCore a (sourceTestApprox q.F (preparedPrimal q 0 t)))+
    leftUncutDefect (q.p+q.k) q.F (rawChargeCore a (sourceTestApprox q.F (preparedPrimal q 0 t)))-
    sourceApprox q.F (embed (rawChargeCore a
      (rightCompressionDefect q.p q.F (preparedPrimal q 0 t)+rightUncutDefect q.p q.F (preparedPrimal q 0 t))))

theorem preparedCurrent_action_time (q : PhysicalResponsePoint) (a : Fin 12) (t : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r=>noetherPreparedCurrent q (temporalField a) 0 r)
      (Complex.I*preparedDual q 0 t (preparedWardChannels q a t)) t :=by
  have source:=noetherPreparedCurrent_time q (temporalField a) t hz hw
  apply source.congr_deriv
  rw [noetherTimeCurrent,temporalInsertion_action_return]
  rfl

theorem preparedCurrent_action_initial (q : PhysicalResponsePoint) (a : Fin 12) :
    noetherTimeCurrent q (temporalField a) 0=Complex.I*inner ℂ (responseLeft q)
      (jointResolvent (q.p+q.k) q.F q.z 0 (preparedWardChannels q a 0)) :=by
  rw [noetherTimeCurrent,temporalInsertion_action_return]
  simp only [preparedDual,independentDual,neg_zero,physicalTime_initial,
    ContinuousLinearMap.comp_apply,one_apply_eq_self,innerSL_apply_apply]
  rfl

end LowEnergy.PreparationVacuumWeightedChargeActionWard
