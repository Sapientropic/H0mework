import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedActionWard
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.PhysicalModeEMCurrent
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticCurrentResidue

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalLockedGaussBalance
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity PreparationVacuumFieldConstraintResponse
open YangMills.FullPairing
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open PreparationVacuumWeightedChargeActionWard PreparationVacuumSourceActionJets
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFullFieldRiesz PreparationVacuumPhysicalElectromagneticDirection
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumObservedStaticResidue PreparationVacuumPhysicalModeChargeRead
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumMovingPoleGaussReturn
open FullQuantum.StateGreen PreparationVacuumActualFieldQuantization
open Stage10.CanonicalMatter DiracExteriorMatterAction DiracCliffordRepresentation
open PreparationVacuumPhysicalElectromagneticDirection
open LowEnergy.GaussComposite.PhysicalModeCharge LowEnergy.GaussComposite.PhysicalModeEMCurrent
open Filter MeasureTheory
open scoped BigOperators Topology InnerProductSpace Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] frameVector frameTest sourceLockedReader sourceLockedForm
  sourceLockedRawChargeCore sourceLockedRawChargeFiber sourceLockedPairCore sourceLockedChargeCore
  noetherReader noetherTimeInsertion sourceHamiltonian sourcePoleRead

/-- This Mother action is the actual primal block of the same full Gauss charge matrix. -/
def sourceLockedNormalizedMother : Mother:=Quantum.operatorMatrix.symm
  (fun i j=>sourceLockedChargeMatrix (Sum.inl i) (Sum.inl j))

theorem sourceLockedNormalizedMother_generated :
    sourceLockedNormalizedMother=Complex.I • sourceLockedAction 2 := by
  apply Quantum.operatorMatrix.injective
  rw [sourceLockedNormalizedMother,Quantum.operatorMatrix.apply_symm_apply,map_smul]
  ext i j
  simp [sourceLockedChargeMatrix,realFourierMatrix,affineMatrix]

/-- The source mode current and full Gauss charge share this generated action on the complete Mother carrier. -/
theorem sourceLockedModeCurrent_generated (mu : Fin 4) :
    sourceModeCurrent (fun j=>(sourceLockedField mu 2 j:ℂ)) mu=
      (diracMatrixMatterAction (diracGamma mu)).comp sourceLockedNormalizedMother := by
  rw [sourceLockedNormalizedMother_generated]
  unfold sourceModeCurrent
  rw [sourceLockedModeMother,LinearMap.comp_smul]

private theorem sourceLockedForm_core (l r : QuantumTest) :
    sourceLockedForm 0 2 l r=sourcePair l (sourceLockedRawChargeCore r) := by
  rw [←sourceLockedForm_generated 0 2 0,rawForm,sourcePair_integral]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  rw [←pairSample_source]
  unfold sourceLockedRawChargeCore
  change pairSample z (l z) (rawFiber (sourceLockedField 0 2) 0 (0,z) (r z))=
    pairSample z (l z) (sourceLockedRawChargeFiber z (r z))
  unfold sourceLockedRawChargeFiber
  rfl

theorem sourceLockedReader_core (F : GaussUnitaryHistory.Index) :
    sourceLockedReader 0 2 F=finiteRiesz F (fun i j=>
      sourcePair (frameTest F i) (sourceLockedRawChargeCore (frameTest F j))) := by
  unfold sourceLockedReader
  simp_rw [sourceLockedForm_core]

/-- The raw mode reader returns through the same original Gauss core and full source charge. -/
theorem sourceLockedReader_projected_action (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    noetherReader (sourceLockedField 0 2) p F 0 y=
      sourceApprox F (embed (sourceLockedRawChargeCore (sourceTestApprox F y))) := by
  rw [noetherReader_source,sourceLockedReader_generated,sourceLockedReader_core,
    sourceApprox_frame,sourceTestApprox_frame]
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

/-- Both complete source Hamiltonians consume the generated charge Ward, including actual compression and uncut defects. -/
theorem sourceLockedInsertion_generated (q : PhysicalResponsePoint) (y : H) :
    noetherTimeInsertion q (sourceLockedField 0 2) y=
      sourceApprox q.F (embed (sourceLockedWeightedWard q.p q.k (sourceTestApprox q.F y)))+
      leftCompressionDefect (q.p+q.k) q.F (sourceLockedRawChargeCore (sourceTestApprox q.F y))+
      leftUncutDefect (q.p+q.k) q.F (sourceLockedRawChargeCore (sourceTestApprox q.F y))-
      sourceApprox q.F (embed (sourceLockedRawChargeCore
        (rightCompressionDefect q.p q.F y+rightUncutDefect q.p q.F y))) := by
  simp only [noetherTimeInsertion,sub_apply,mul_apply_eq_comp,sourceLockedReader_projected_action]
  rw [leftAction_source,rightAction_source]
  simp only [map_add]
  have source:=sourceLockedRawActionWard_generated q.p q.k (sourceTestApprox q.F y)
  have projected:=congrArg (fun f : QuantumTest=>sourceApprox q.F (embed f)) source
  simp only [map_sub] at projected
  rw [←projected]
  abel

def sourceLockedPreparedWard (q : PhysicalResponsePoint) (t : ℝ) : H:=
  sourceApprox q.F (embed (sourceLockedWeightedWard q.p q.k (sourceTestApprox q.F (preparedPrimal q 0 t))))+
    leftCompressionDefect (q.p+q.k) q.F (sourceLockedRawChargeCore (sourceTestApprox q.F (preparedPrimal q 0 t)))+
    leftUncutDefect (q.p+q.k) q.F (sourceLockedRawChargeCore (sourceTestApprox q.F (preparedPrimal q 0 t)))-
    sourceApprox q.F (embed (sourceLockedRawChargeCore
      (rightCompressionDefect q.p q.F (preparedPrimal q 0 t)+rightUncutDefect q.p q.F (preparedPrimal q 0 t))))

theorem sourceLockedPreparedCurrent_time (q : PhysicalResponsePoint) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    HasDerivAt (fun age=>noetherPreparedCurrent q (sourceLockedField 0 2) 0 age)
      (Complex.I*preparedDual q 0 t (sourceLockedPreparedWard q t)) t := by
  apply (noetherPreparedCurrent_time q (sourceLockedField 0 2) t nonrealL nonrealR).congr_deriv
  rw [noetherTimeCurrent,sourceLockedInsertion_generated]
  rfl

theorem sourceLockedPreparedCurrent_initial (q : PhysicalResponsePoint) :
    noetherTimeCurrent q (sourceLockedField 0 2) 0=Complex.I*inner ℂ (responseLeft q)
      (jointResolvent (q.p+q.k) q.F q.z 0 (sourceLockedPreparedWard q 0)) := by
  rw [noetherTimeCurrent,sourceLockedInsertion_generated]
  simp only [preparedDual,independentDual,neg_zero,physicalTime_initial,
    ContinuousLinearMap.comp_apply,one_apply_eq_self,innerSL_apply_apply]
  rfl

/-- The actual nested static retainer channel consumes the same complete Hamiltonian return without zero-torque premises. -/
theorem sourceLockedStaticRetainer_return (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (i : Fin 289) (y : H) :
    noetherTimeInsertion (sourcePhysicalMaterialPoint q 0 0) (sourceLockedField 0 2)
      (sourceStaticBase q n i y)=
      sourceApprox q.F (embed (sourceLockedWeightedWard 0 0 (sourceTestApprox q.F (sourceStaticBase q n i y))))+
      leftCompressionDefect 0 q.F (sourceLockedRawChargeCore (sourceTestApprox q.F (sourceStaticBase q n i y)))+
      leftUncutDefect 0 q.F (sourceLockedRawChargeCore (sourceTestApprox q.F (sourceStaticBase q n i y)))-
      sourceApprox q.F (embed (sourceLockedRawChargeCore
        (rightCompressionDefect 0 q.F (sourceStaticBase q n i y)+rightUncutDefect 0 q.F (sourceStaticBase q n i y)))) := by
  simpa only [sourcePhysicalMaterialPoint,sourceMaterialTransfer,sub_self,add_zero] using
    sourceLockedInsertion_generated (sourcePhysicalMaterialPoint q 0 0) (sourceStaticBase q n i y)

/-- The complete prepared balance uses the already generated source charged-column four-current identity. -/
theorem sourceLockedChargedPrepared_consumer (point : ProofFreeRicherAnholonomicSource.BasePoint)
    (side : Fin 2) (q : PhysicalResponsePoint) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (∀ mu,sourceModeCurrent (fun j=>(sourceLockedField mu 2 j:ℂ)) mu=
      (diracMatrixMatterAction (diracGamma mu)).comp sourceLockedNormalizedMother) ∧
    (∀ mu left,modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu left (side,1)=
      canonicalCurrentTensor point mu left (side,1)) ∧
    (∀ mu left,modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu left (side,3)=
      -canonicalCurrentTensor point mu left (side,3)) ∧
    HasDerivAt (fun age=>noetherPreparedCurrent q (sourceLockedField 0 2) 0 age)
      (Complex.I*preparedDual q 0 t (sourceLockedPreparedWard q t)) t :=
  ⟨sourceLockedModeCurrent_generated,fun mu left=>modeTensor_minus_column point mu left side,
    fun mu left=>modeTensor_plus_column point mu left side,
    sourceLockedPreparedCurrent_time q t nonrealL nonrealR⟩

end LowEnergy.PreparationVacuumPhysicalLockedGaussBalance
