import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCurvatureReaders

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTemporalCharge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential
open GaussQuantumMultiplier GaussNativeMatter
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceFieldFamily PreparationVacuumLowerClassical PreparationVacuumNonlinearFieldCurve
open PreparationVacuumActionDecomposition PreparationVacuumFieldConstraintResponse
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse
open CanonicalGradedSpatialSource CanonicalGradedCurrent CanonicalGradedCharge
open CanonicalPhysicalYResolvent GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)
open Set Filter
open scoped Matrix Matrix.Norms.L2Operator ContDiff BigOperators Topology InnerProductSpace
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

-- This is the literal retained temporal/spin connection, read on the same state curve.
def retainedState (s : ActionState) : SourceMatrix :=
  ((-Complex.I) • Ring.inverse (CoframeResponse.principalMatrix s.1))*coefficientMatrix 0 s.1*s.2.1 0+
    ∑ j : Fin 3,((-Complex.I) • Ring.inverse (CoframeResponse.principalMatrix s.1))*
      coefficientMatrix j.succ s.1*spinConnection j.succ

theorem retainedState_source (z : SourceCoordinateSlice) :
    retainedState (sourceState z)=retainedConnection z := rfl

theorem retainedState_temporal (a : Fin 12) (s : ActionState) (valid : s∈validStates) (r : ℝ) :
    retainedState (temporalCurve a s r)=retainedState s-r • (Complex.I • nativePrimal (originalUnit a)) := by
  have unit:=principalMatrix_regular s.1 valid.2
  unfold retainedState
  simp only [temporalCurve_coframe,temporalCurve_connection,if_true,mul_add,mul_smul_comm]
  rw [←principalMatrix_coefficient,smul_mul_assoc,Ring.inverse_mul_cancel _ unit]
  simp only [smul_mul_assoc,one_mul]
  simp only [neg_smul,smul_neg,sub_eq_add_neg]
  abel

theorem temporal_complete_coefficient (a : Fin 12) (s : ActionState) (valid : s∈validStates)
    (r : ℝ) (i : Fin 4) :
    stateHamiltonian (temporalCurve a s r) i-(if i=0 then retainedState (temporalCurve a s r) else 0)=
      stateHamiltonian s i-(if i=0 then retainedState s else 0) := by
  rw [temporal_hamiltonian a s valid,retainedState_temporal a s valid]
  by_cases hi : i=0
  · simp only [hi,temporalCoefficient,if_true]
    abel
  · simp [temporalCoefficient,hi]

theorem temporal_complete_source (a : Fin 12) (z : physicalChart) (r : ℝ) (p : PhysicalMomentum) :
    affineMatrix (fun i=>stateHamiltonian (temporalCurve a (sourceState z.val) r) i-
        if i=0 then retainedState (temporalCurve a (sourceState z.val) r) else 0) p=
      affineMatrix (fun i=>stateHamiltonian (sourceState z.val) i-
        if i=0 then retainedConnection z.val else 0) p := by
  apply congrArg (fun A : Fin 4 → SourceMatrix=>affineMatrix A p)
  funext i
  exact (temporal_complete_coefficient a _ (sourceState_valid z) r i).trans
    (by rw [retainedState_source])

private theorem triple_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B C : E →L[ℂ] E) (a b c : ℝ) (ha : ‖A‖ ≤ a) (hb : ‖B‖ ≤ b) (hc : ‖C‖ ≤ c)
    (hpa : 0 ≤ a) (hpb : 0 ≤ b) : ‖A*B*C‖ ≤ a*b*c :=
  (norm_mul_le (A*B) C).trans (mul_le_mul
    ((norm_mul_le A B).trans (mul_le_mul ha hb (norm_nonneg _) hpa)) hc
    (norm_nonneg _) (mul_nonneg hpa hpb))

def vertexPrice (a : Fin 12) (cut : ℕ) (z w : ℂ) : ℝ :=
  normBound cut z*chargePrice a*normBound cut w

theorem vertexPrice_nonnegative (a : Fin 12) (cut : ℕ) (z w : ℂ) : 0 ≤ vertexPrice a cut z w :=
  mul_nonneg (mul_nonneg (normBound_nonneg cut z) (chargePrice_nonnegative a)) (normBound_nonneg cut w)

theorem original_finite_vertex_price (a : Fin 12) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (F : Index) :
    ‖CanonicalPhysicalWard.finiteVertex p k (originalUnit a) cut z w F‖ ≤ vertexPrice a cut z w :=
  triple_norm (finiteFull (p+k) F cut z) (globalReader a) (finiteFull p F cut w)
    _ _ _ (finiteFull_bound _ _ _ _ hz) (globalReader_norm a) (finiteFull_bound _ _ _ _ hw)
    (normBound_nonneg _ _) (chargePrice_nonnegative a)

theorem original_full_vertex_price (a : Fin 12) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    ‖CanonicalPhysicalWard.vertex p k (originalUnit a) cut z w hz hw‖ ≤ vertexPrice a cut z w := by
  apply ContinuousLinearMap.opNorm_le_bound _ (vertexPrice_nonnegative a cut z w)
  intro x
  apply SourceBoundaryGram.lift_bound_explicit sourceFilter
    (CanonicalPhysicalWard.vertexFamily p k (originalUnit a) cut z w hz hw) _
    (vertexPrice_nonnegative a cut z w)
  intro F y
  exact ((CanonicalPhysicalWard.finiteVertex p k (originalUnit a) cut z w F).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (original_finite_vertex_price a p k cut z w hz hw F) (norm_nonneg y))

private theorem family_pair_limit (A : SourceFamilyOperator.Operator Index H) (x y : H) :
    Tendsto (fun F : Index=>inner ℂ x (A.component F y)) sourceFilter
      (𝓝 (inner ℂ (inclusion x) (SourceFamilyOperator.lift sourceFilter A (inclusion y)))) := by
  change Tendsto _ _ (𝓝 (inner ℂ (SourceFamilyHilbert.constant sourceFilter x : HistorySpace)
    (SourceFamilyOperator.lift sourceFilter A (SourceFamilyHilbert.constant sourceFilter y : HistorySpace))))
  rw [SourceFamilyOperator.lift_coe,SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter x)
    (SourceFamilyOperator.act sourceFilter A (SourceFamilyHilbert.constant sourceFilter y))

theorem original_vertex_samefilter (a : Fin 12) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (x y : H) :
    Tendsto (fun F : Index=>inner ℂ x
      (CanonicalPhysicalWard.finiteVertex p k (originalUnit a) cut z w F y)) sourceFilter
      (𝓝 (inner ℂ (inclusion x) (CanonicalPhysicalWard.vertex p k (originalUnit a) cut z w hz hw (inclusion y)))) :=
  family_pair_limit (CanonicalPhysicalWard.vertexFamily p k (originalUnit a) cut z w hz hw) x y

theorem original_temporal_ward (a : Fin 12) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (F : Index) :
    CanonicalPhysicalWard.finiteResponse p k (originalUnit a) cut z w F=
      globalReader a*finiteFull p F cut w-finiteFull (p+k) F cut z*globalReader a+
        (z-w) • CanonicalPhysicalWard.finiteVertex p k (originalUnit a) cut z w F :=
  CanonicalPhysicalWard.finite_ward p k (originalUnit a) cut z w hz hw F

def preparedVertex (a : Fin 12) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (epsilon : ℝ) (precision : 0<epsilon)
    (left right : Bool) (lc ls rc rs : Fin 2) : ℂ :=
  SourceGraph.response (CanonicalPhysicalWard.vertex p k (originalUnit a) cut z w hz hw)
    left right lc ls rc rs (sourceProfile epsilon precision) (sourceProfile epsilon precision)

theorem same_prepared_vertex_limit (a : Fin 12) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (epsilon : ℝ) (precision : 0<epsilon)
    (left right : Bool) (lc ls rc rs : Fin 2) :
    Tendsto (fun F : Index=>inner ℂ (completedLeg left lc ls (sourceProfile epsilon precision))
      (CanonicalPhysicalWard.finiteVertex p k (originalUnit a) cut z w F
        (completedLeg right rc rs (sourceProfile epsilon precision)))) sourceFilter
      (𝓝 (preparedVertex a p k cut z w hz hw epsilon precision left right lc ls rc rs)) :=
  original_vertex_samefilter a p k cut z w hz hw _ _

-- The temporal columns of the existing full36 reader, with no selection of an EM generator.
def curvatureTemporalReader (q : Fin 4 → ℂ) (row : Fin 36) : H →L[ℂ] H :=
  ∑ a : Fin 12,originalReader36 q row (gaugeSlot 0 a) • globalReader a

def curvatureTemporalPrice (q : Fin 4 → ℂ) (row : Fin 36) : ℝ :=
  ∑ a : Fin 12,‖originalReader36 q row (gaugeSlot 0 a)‖*chargePrice a

theorem curvatureTemporalPrice_nonnegative (q : Fin 4 → ℂ) (row : Fin 36) :
    0 ≤ curvatureTemporalPrice q row :=
  Finset.sum_nonneg (fun a _=>mul_nonneg (norm_nonneg _) (chargePrice_nonnegative a))

theorem curvatureTemporalReader_norm (q : Fin 4 → ℂ) (row : Fin 36) :
    ‖curvatureTemporalReader q row‖ ≤ curvatureTemporalPrice q row := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (globalReader_norm a) (norm_nonneg _)

theorem curvatureTemporal_source_core (q : Fin 4 → ℂ) (row : Fin 36) (p : PhysicalMomentum)
    (test : QuantumTest) :
    curvatureTemporalReader q row (embed test)=∑ a : Fin 12,
      originalReader36 q row (gaugeSlot 0 a) • embed (familyCore (temporalField a) p test) := by
  simp only [curvatureTemporalReader,sum_apply,smul_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [globalReader_source a p test]

def curvatureTemporalFamily (q : Fin 4 → ℂ) (row : Fin 36) (p k : PhysicalMomentum)
    (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) : SourceFamilyOperator.Operator Index H :=
  SourceFamilyOperator.comp (SourceFamilyOperator.comp (CanonicalPhysicalYResolvent.fullFamily (p+k) cut z hz)
    (SourceFamilyOperator.constant (curvatureTemporalReader q row))) (CanonicalPhysicalYResolvent.fullFamily p cut w hw)

theorem curvatureTemporal_finite_price (q : Fin 4 → ℂ) (row : Fin 36) (p k : PhysicalMomentum)
    (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (F : Index) :
    ‖(curvatureTemporalFamily q row p k cut z w hz hw).component F‖ ≤
      normBound cut z*curvatureTemporalPrice q row*normBound cut w :=
  triple_norm (finiteFull (p+k) F cut z) (curvatureTemporalReader q row) (finiteFull p F cut w)
    _ _ _ (finiteFull_bound _ _ _ _ hz) (curvatureTemporalReader_norm q row)
    (finiteFull_bound _ _ _ _ hw) (normBound_nonneg _ _) (curvatureTemporalPrice_nonnegative q row)

theorem same_prepared_curvature_limit (q : Fin 4 → ℂ) (row : Fin 36) (p k : PhysicalMomentum)
    (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (epsilon : ℝ) (precision : 0<epsilon)
    (left right : Bool) (lc ls rc rs : Fin 2) :
    Tendsto (fun F : Index=>inner ℂ (completedLeg left lc ls (sourceProfile epsilon precision))
      ((curvatureTemporalFamily q row p k cut z w hz hw).component F
        (completedLeg right rc rs (sourceProfile epsilon precision)))) sourceFilter
      (𝓝 (SourceGraph.response (SourceFamilyOperator.lift sourceFilter (curvatureTemporalFamily q row p k cut z w hz hw))
        left right lc ls rc rs (sourceProfile epsilon precision) (sourceProfile epsilon precision))) :=
  family_pair_limit (curvatureTemporalFamily q row p k cut z w hz hw) _ _

end LowEnergy.PreparationVacuumTemporalCharge
