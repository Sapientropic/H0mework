import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPreparedWard
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationPreparedCurrentRead

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectricConstraint
open SourceQuantumScalarChart GaussCoreHilbert GaussCoreDifferential GaussFockPair
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial CanonicalGradedCharge CanonicalPhysicalYResolvent
open PreparationVacuumTemporalCharge PreparationVacuumLowerClassical PreparationVacuumFieldConstraintResponse
open PreparationVacuumPreparedCurrent PreparationVacuumSourcePreparedResponse
open PreparationVacuumFullElectricWard GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion)
open Filter Set
open scoped Topology InnerProductSpace
attribute [local irreducible] finiteFull sourceProfile

theorem quartic_constraint_balance (k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    momentumAction k (orbitAction a f)+CanonicalPhysicalWardCore.currentAction k a f+pairCurrent k a f=0 := by
  rw [original_gauss_constraint,LinearMap.neg_apply,map_neg,full_current]
  abel

theorem complete_source_constraint (p k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    (physicalAction (p+k)+GaussYukawaOperator.originalAction) (orbitAction a f)-
      orbitAction a ((physicalAction p+GaussYukawaOperator.originalAction) f)+wardCore k a f=0 := by
  rw [original_gauss_constraint]
  simp only [LinearMap.neg_apply,map_neg]
  have h:=original_full_ward p k a f
  rw [←h]
  abel

theorem actual_resolved_joint_domain (a : Fin 12) (p : PhysicalMomentum) (F : Index)
    (cut : ℕ) (z : ℂ) (x : H) :
    (finiteFull p F cut z x,jointReader a (finiteFull p F cut z x))∈closure (jointCoreGraph a) := by
  rw [original_joint_graph_closed]
  rfl

theorem actual_adjoint_resolved_joint_domain (a : Fin 12) (p : PhysicalMomentum) (F : Index)
    (cut : ℕ) (z : ℂ) (x : H) :
    ((finiteFull p F cut z).adjoint x,jointReader a ((finiteFull p F cut z).adjoint x))∈closure (jointCoreGraph a) := by
  rw [original_joint_graph_closed]
  rfl

private theorem map_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (c : ℝ) (h : ‖A‖≤c) (x : E) : ‖A x‖≤c*‖x‖ :=
  (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem source_core_joint_price (a : Fin 12) (F : Index) (x : H) :
    ‖embed (orbitAction (originalUnit a) (sourceTestApprox F x))‖≤chargePrice a*‖x‖ := by
  change ‖embed (scalarOrbitAction (originalUnit a) (sourceTestApprox F x)+
    electricOrbitAction (originalUnit a) (sourceTestApprox F x))‖≤_
  rw [←jointReader_core,sourceTestApprox_embed]
  exact (map_price _ _ (jointReader_price a) _).trans
    (mul_le_mul_of_nonneg_left (sourceApprox_contractive F x) (chargePrice_nonnegative a))

theorem propagated_joint_price (a : Fin 12) (p : PhysicalMomentum) (F : Index) (cut : ℕ)
    (z : ℂ) (hz : z.im≠0) (x : H) :
    ‖embed (orbitAction (originalUnit a) (sourceTestApprox F (finiteFull p F cut z x)))‖≤
      chargePrice a*normBound cut z*‖x‖ := by
  apply (source_core_joint_price a F _).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (map_price _ _ (finiteFull_bound p F cut z hz) x) (chargePrice_nonnegative a)

theorem propagated_adjoint_joint_price (a : Fin 12) (p : PhysicalMomentum) (F : Index) (cut : ℕ)
    (z : ℂ) (hz : z.im≠0) (x : H) :
    ‖embed (orbitAdjoint (originalUnit a) (sourceTestApprox F ((finiteFull p F cut z).adjoint x)))‖≤
      chargePrice a*normBound cut z*‖x‖ := by
  rw [original_weighted_ordering]
  apply (source_core_joint_price a F _).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (chargePrice_nonnegative a)
  exact map_price _ _ ((ContinuousLinearMap.adjoint.norm_map _).le.trans (finiteFull_bound p F cut z hz)) x

/-- Exact cancellation for the actual F-dependent propagated source tests. -/
theorem propagated_core_constraint (a : Fin 12) (p k : PhysicalMomentum) (F : Index) (cut : ℕ)
    (z w : ℂ) (x y : H) :
    sourcePair (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x))
      (orbitAction (originalUnit a) (sourceTestApprox F (finiteFull p F cut w y)))+
    sourcePair (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x))
      (chargeAction (originalUnit a) (sourceTestApprox F (finiteFull p F cut w y)))=0 := by
  rw [original_gauss_constraint]
  simp only [LinearMap.neg_apply,sourcePair,map_neg,inner_neg_right,neg_add_cancel]

def jointVertex (a : Fin 12) (p k : PhysicalMomentum) (F : Index) (cut : ℕ) (z w : ℂ) : H →L[ℂ] H :=
  finiteFull (p+k) F cut z*jointReader a*finiteFull p F cut w

theorem jointVertex_source (a : Fin 12) (p k : PhysicalMomentum) (F : Index) (cut : ℕ) (z w : ℂ) :
    jointVertex a p k F cut z w= -CanonicalPhysicalWard.finiteVertex p k (originalUnit a) cut z w F := by
  apply ContinuousLinearMap.ext
  intro x
  change finiteFull (p+k) F cut z (-(globalReader a (finiteFull p F cut w x)))=
    -(finiteFull (p+k) F cut z (globalReader a (finiteFull p F cut w x)))
  exact map_neg _ _

theorem jointVertex_price (a : Fin 12) (p k : PhysicalMomentum) (F : Index) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) : ‖jointVertex a p k F cut z w‖≤vertexPrice a cut z w := by
  rw [jointVertex_source,norm_neg]
  exact original_finite_vertex_price a p k cut z w hz hw F

theorem actual_full_constraint_cancellation (a : Fin 12) (p k : PhysicalMomentum) (F : Index)
    (cut : ℕ) (z w : ℂ) :
    finiteFull (p+k) F cut z*(jointReader a+globalReader a)*finiteFull p F cut w=0 := by
  simp only [jointReader,neg_add_cancel,mul_zero,zero_mul]

def orbitFeedback (a : Fin 12) (p k : PhysicalMomentum) (F : Index) (cut : ℕ) (z w : ℂ) : H →L[ℂ] H :=
  finiteFull (p+k) F cut z*
    ((compression (p+k) F+FullYSourceCutoffVolterra.cutoff cut)*jointReader a-
      jointReader a*(compression p F+FullYSourceCutoffVolterra.cutoff cut))*finiteFull p F cut w

theorem orbitFeedback_source (a : Fin 12) (p k : PhysicalMomentum) (F : Index) (cut : ℕ) (z w : ℂ) :
    orbitFeedback a p k F cut z w= -CanonicalPhysicalWard.finiteResponse p k (originalUnit a) cut z w F := by
  apply ContinuousLinearMap.ext
  intro x
  change finiteFull (p+k) F cut z
    ((compression (p+k) F+FullYSourceCutoffVolterra.cutoff cut) (-(globalReader a (finiteFull p F cut w x)))-
      -(globalReader a ((compression p F+FullYSourceCutoffVolterra.cutoff cut) (finiteFull p F cut w x))))=
    -(finiteFull (p+k) F cut z
      ((compression (p+k) F+FullYSourceCutoffVolterra.cutoff cut) (globalReader a (finiteFull p F cut w x))-
        globalReader a ((compression p F+FullYSourceCutoffVolterra.cutoff cut) (finiteFull p F cut w x))))
  simp only [map_neg,map_sub]
  abel

theorem source_feedback_balance (a : Fin 12) (p k : PhysicalMomentum) (F : Index)
    (cut : ℕ) (z w : ℂ) (x y : H) :
    inner ℂ x (orbitFeedback a p k F cut z w y)+
      resolvedChannels p k (originalUnit a) cut z w F x y=0 := by
  rw [orbitFeedback_source,resolvedChannels_original_response]
  simp only [neg_apply,inner_neg_right,neg_add_cancel]

theorem same_prepared_joint_limit (epsilon : ℝ) (precision : 0<epsilon) (a : Fin 12)
    (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (lc ls rc rs : Fin 2) :
    Tendsto (fun F : Index=>inner ℂ (completedLeg left lc ls (sourceProfile epsilon precision))
      (jointVertex a p k F cut z w (completedLeg right rc rs (sourceProfile epsilon precision))))
      sourceFilter (𝓝 (-preparedVertex a p k cut z w hz hw epsilon precision left right lc ls rc rs)) := by
  simp only [jointVertex_source,neg_apply,inner_neg_right]
  exact (same_prepared_vertex_limit a p k cut z w hz hw epsilon precision left right lc ls rc rs).neg

end LowEnergy.PreparationVacuumElectricConstraint
