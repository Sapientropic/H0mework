import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceColorMatrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalColorCharge
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _

def sourceColorSample (mu : Fin 4) (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  pairSample z (a z) (sourceColorFiber mu z (b z))

def sourceColorForm (mu : Fin 4) (a b : QuantumTest) : ℂ :=
  ∫z,sourceColorSample mu a b z ∂GaussHistoryHilbert.configurationMeasure

private theorem pair_real_half (z : SourceCoordinateSlice) (u v w : FockFiber) :
    pairSample z u ((1/2 : ℝ) • (v-w))=
      (1/2 : ℝ) • (pairSample z u v-pairSample z u w) := by
  simp only [pairSample,WithLp.ofLp_smul,WithLp.ofLp_sub,Pi.sub_apply,Pi.smul_apply,Complex.real_smul]
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [Finset.mul_sum,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro w _ <;> ring

private theorem raw_integrable (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (fun z=>rawSample reader p a b (0,z)) GaussHistoryHilbert.configurationMeasure := by
  apply parameter_slice_integrable _ (tsupport a) a.hasCompactSupport 0
    (fun z=>rawSample_near_smooth reader p a b 0 z (by simpa only [norm_zero] using ambientRadius_positive a))
    (rawSample_zero reader p a b)

theorem sourceColorSample_generated (mu : Fin 4) (p : PhysicalMomentum) (a b : QuantumTest)
    (z : SourceCoordinateSlice) :
    (1/2 : ℝ) • (rawSample (gaugeField mu 6) p a b (0,z)-
      rawSample (gaugeField mu 7) p a b (0,z))=sourceColorSample mu a b z := by
  by_cases inside : z∈tsupport a
  · have h:=sourceColorFiber_generated mu p ⟨z,a.tsupport_subset inside⟩
    unfold rawSample sourceColorSample
    rw [rawFiber_zero,rawFiber_zero]
    rw [←h]
    change _=pairSample z (a z) ((1/2 : ℝ) • (rawStateFiber (gaugeField mu 6) p (sourceState z) (b z)-
      rawStateFiber (gaugeField mu 7) p (sourceState z) (b z)))
    exact (pair_real_half z _ _ _).symm
  · rw [rawSample_zero _ _ _ _ _ _ inside,rawSample_zero _ _ _ _ _ _ inside]
    simp only [sub_self,smul_zero,sourceColorSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

theorem sourceColorForm_generated (mu : Fin 4) (p : PhysicalMomentum) (a b : QuantumTest) :
    (1/2 : ℝ) • (rawForm (gaugeField mu 6) p a b 0-
      rawForm (gaugeField mu 7) p a b 0)=sourceColorForm mu a b := by
  unfold rawForm sourceColorForm
  rw [←integral_sub (raw_integrable _ _ _ _) (raw_integrable _ _ _ _),←integral_smul]
  exact integral_congr_ae (Eventually.of_forall (sourceColorSample_generated mu p a b))

def sourceColorReader (mu : Fin 4) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H :=
  finiteRiesz F (fun i j=>sourceColorForm mu (frameTest F i) (frameTest F j))

private theorem coefficient_rank {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module ℝ M] [IsScalarTower ℝ ℂ M] (e f : ℂ) (x : M) :
    (1/2 : ℝ) • (e • x)-(1/2 : ℝ) • (f • x)=((1/2 : ℝ) • (e-f)) • x := by
  simp only [smul_sub,sub_smul,smul_assoc]

attribute [local irreducible] frameVector frameTest rawForm sourceColorForm sourceColorReader
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem sourceColorReader_generated (mu : Fin 4) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (1/2 : ℝ) • (rawReader (gaugeField mu 6) p F 0-
      rawReader (gaugeField mu 7) p F 0)=sourceColorReader mu F := by
  unfold rawReader sourceColorReader finiteRiesz
  simp only [smul_sub,Finset.smul_sum]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact (coefficient_rank _ _ _).trans (congrArg
    (fun e : ℂ=>e • InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
    (sourceColorForm_generated mu p (frameTest F i) (frameTest F j)))

/-- The density weight stays in the source operator before taking the prepared-state read. -/
def sourceColorKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (t : ℝ) : H→L[ℂ] H :=
  SourceFiniteUnitary.time (actualC pL q.F) (-t)*CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z*
    sourceColorReader mu q.F*CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w*
      SourceFiniteUnitary.time (actualC pR q.F) t

theorem sourceColorKernel_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (t : ℝ) :
    (1/2 : ℝ) • (sourceGaugeZeroHistoryKernel q pL pR mu 6 t-
      sourceGaugeZeroHistoryKernel q pL pR mu 7 t)=sourceColorKernel q pL pR mu t := by
  unfold sourceGaugeZeroHistoryKernel sourceColorKernel
  rw [←sourceColorReader_generated mu pR q.F]
  simp only [mul_sub,sub_mul,smul_sub,smul_mul_assoc,mul_smul_comm]

end LowEnergy.PreparationVacuumPhysicalColorCharge
