import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationElectricCoreWard

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullElectricWard
open SourceQuantumScalarChart GaussCoreHilbert GaussCoreDifferential GaussFockPair
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial CanonicalGradedCharge
open CanonicalPhysicalWardCore CanonicalPhysicalYResolvent
open PreparationVacuumTemporalCharge PreparationVacuumLowerClassical
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumSourcePreparedResponse GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion)
open Filter
open scoped Topology InnerProductSpace BigOperators
attribute [local irreducible] finiteFull sourceProfile

def coreChannels (k : PhysicalMomentum) (a : NativeLie) (l r : QuantumTest) : ℂ :=
  sourcePair l (configurationTorque a r)+sourcePair l (CanonicalPhysicalWardCore.currentAction k a r)+
    sourcePair l (pairCurrent k a r)+sourcePair l (yukawaTorque a r)

theorem coreChannels_source (k : PhysicalMomentum) (a : NativeLie) (l r : QuantumTest) :
    coreChannels k a l r=sourcePair l (wardCore k a r) := by
  simp only [wardCore,LinearMap.add_apply,sourcePair,map_add,inner_add_right,coreChannels]

def transportRemainder (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (F : Index)
    (l r : QuantumTest) (L R : H) : ℂ :=
  inner ℂ L (wardDefect p k a cut F r)+
    inner ℂ (L-embed l) (embed (wardCore k a r))+
    inner ℂ L (CanonicalPhysicalWard.finiteInsertion p k a cut F (R-embed r))

theorem insertion_actual_channels (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (F : Index)
    (l r : QuantumTest) (L R : H) :
    inner ℂ L (CanonicalPhysicalWard.finiteInsertion p k a cut F R)=
      coreChannels k a l r+transportRemainder p k a cut F l r L R := by
  rw [coreChannels_source]
  unfold transportRemainder
  simp only [map_sub,inner_sub_left,inner_sub_right,finite_full_core,inner_add_right]
  change _=inner ℂ (embed l) (embed (wardCore k a r))+_
  abel

def leftResolved (p k : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (x : H) : H :=
  (finiteFull (p+k) F cut z).adjoint x

def rightResolved (p : PhysicalMomentum) (F : Index) (cut : ℕ) (w : ℂ) (y : H) : H :=
  finiteFull p F cut w y

/-- All source channels plus the actual compression, cutoff and propagated-core errors. -/
def resolvedChannels (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (F : Index) (x y : H) : ℂ :=
  let L:=leftResolved p k F cut z x
  let R:=rightResolved p F cut w y
  coreChannels k a (sourceTestApprox F L) (sourceTestApprox F R)+
    transportRemainder p k a cut F (sourceTestApprox F L) (sourceTestApprox F R) L R

theorem resolvedChannels_original_response (p k : PhysicalMomentum) (a : NativeLie)
    (cut : ℕ) (z w : ℂ) (F : Index) (x y : H) :
    resolvedChannels p k a cut z w F x y=
      inner ℂ x (CanonicalPhysicalWard.finiteResponse p k a cut z w F y) := by
  unfold resolvedChannels
  rw [←insertion_actual_channels]
  unfold CanonicalPhysicalWard.finiteResponse leftResolved rightResolved
  simp only [mul_apply_eq_comp]
  exact (finiteFull (p+k) F cut z).adjoint_inner_left _ _

private theorem ward_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q R S V : E →L[ℂ] E) (c : ℂ) (q r s v : ℝ)
    (hQ : ‖Q‖ ≤ q) (hR : ‖R‖ ≤ r) (hS : ‖S‖ ≤ s) (hV : ‖V‖ ≤ v) :
    ‖Q*R-S*Q+c • V‖ ≤ q*r+s*q+‖c‖*v := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sub_le _ _).trans
    exact add_le_add ((norm_mul_le _ _).trans
      (mul_le_mul hQ hR (norm_nonneg _) ((norm_nonneg _).trans hQ)))
      ((norm_mul_le _ _).trans (mul_le_mul hS hQ (norm_nonneg _) ((norm_nonneg _).trans hS)))
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hV (norm_nonneg _)

def responsePrice (a : Fin 12) (cut : ℕ) (z w : ℂ) : ℝ :=
  chargePrice a*normBound cut w+normBound cut z*chargePrice a+‖z-w‖*vertexPrice a cut z w

theorem original_response_price (a : Fin 12) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (F : Index) :
    ‖CanonicalPhysicalWard.finiteResponse p k (originalUnit a) cut z w F‖≤responsePrice a cut z w := by
  rw [original_temporal_ward a p k cut z w hz hw F]
  exact ward_norm _ _ _ _ _ _ _ _ _ (globalReader_norm a)
    (finiteFull_bound p F cut w hw) (finiteFull_bound (p+k) F cut z hz)
    (original_finite_vertex_price a p k cut z w hz hw F)

theorem resolvedChannels_price (a : Fin 12) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (F : Index) (x y : H) :
    ‖resolvedChannels p k (originalUnit a) cut z w F x y‖≤‖x‖*responsePrice a cut z w*‖y‖ := by
  rw [resolvedChannels_original_response]
  calc
    _≤‖x‖*‖CanonicalPhysicalWard.finiteResponse p k (originalUnit a) cut z w F y‖:=norm_inner_le_norm _ _
    _≤‖x‖*(responsePrice a cut z w*‖y‖):=mul_le_mul_of_nonneg_left
      (((CanonicalPhysicalWard.finiteResponse p k (originalUnit a) cut z w F).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right (original_response_price a p k cut z w hz hw F) (norm_nonneg _))) (norm_nonneg _)
    _=‖x‖*responsePrice a cut z w*‖y‖:=(mul_assoc _ _ _).symm

private theorem family_pair_limit (A : SourceFamilyOperator.Operator Index H) (x y : H) :
    Tendsto (fun F : Index=>inner ℂ x (A.component F y)) sourceFilter
      (𝓝 (inner ℂ (inclusion x) (SourceFamilyOperator.lift sourceFilter A (inclusion y)))) := by
  change Tendsto _ _ (𝓝 (inner ℂ (SourceFamilyHilbert.constant sourceFilter x : HistorySpace)
    (SourceFamilyOperator.lift sourceFilter A (SourceFamilyHilbert.constant sourceFilter y : HistorySpace))))
  rw [SourceFamilyOperator.lift_coe,SourceFamilyHilbert.inner_coe]
  exact SourceFamilyHilbert.pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter x)
    (SourceFamilyOperator.act sourceFilter A (SourceFamilyHilbert.constant sourceFilter y))

theorem resolvedChannels_samefilter (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (x y : H) :
    Tendsto (fun F : Index=>resolvedChannels p k a cut z w F x y) sourceFilter
      (𝓝 (inner ℂ (inclusion x) (CanonicalPhysicalWard.response p k a cut z w hz hw (inclusion y)))) := by
  simp only [resolvedChannels_original_response]
  exact family_pair_limit (CanonicalPhysicalWard.responseFamily p k a cut z w hz hw) x y

def preparedChannels (epsilon : ℝ) (precision : 0<epsilon) (a : Fin 12) (p k : PhysicalMomentum)
    (cut : ℕ) (z w : ℂ) (F : Index) (left right : Bool) (lc ls rc rs : Fin 2) : ℂ :=
  resolvedChannels p k (originalUnit a) cut z w F
    (completedLeg left lc ls (sourceProfile epsilon precision))
    (completedLeg right rc rs (sourceProfile epsilon precision))

theorem preparedChannels_same_state (epsilon : ℝ) (precision : 0<epsilon) (a : Fin 12)
    (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (lc ls rc rs : Fin 2) :
    Tendsto (fun F=>preparedChannels epsilon precision a p k cut z w F left right lc ls rc rs)
      sourceFilter (𝓝 (SourceGraph.response (CanonicalPhysicalWard.response p k (originalUnit a) cut z w hz hw)
        left right lc ls rc rs (sourceProfile epsilon precision) (sourceProfile epsilon precision))) :=
  resolvedChannels_samefilter p k (originalUnit a) cut z w hz hw _ _

def curvatureChannels (epsilon : ℝ) (precision : 0<epsilon) (q : Fin 4 → ℂ) (row : Fin 36)
    (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ) (F : Index)
    (left right : Bool) (lc ls rc rs : Fin 2) : ℂ :=
  ∑ a : Fin 12,originalReader36 q row (gaugeSlot 0 a)*
    preparedChannels epsilon precision a p k cut z w F left right lc ls rc rs

theorem curvatureChannels_same_state (epsilon : ℝ) (precision : 0<epsilon) (q : Fin 4 → ℂ) (row : Fin 36)
    (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (lc ls rc rs : Fin 2) :
    Tendsto (fun F=>curvatureChannels epsilon precision q row p k cut z w F left right lc ls rc rs) sourceFilter
      (𝓝 (∑ a : Fin 12,originalReader36 q row (gaugeSlot 0 a)*
        SourceGraph.response (CanonicalPhysicalWard.response p k (originalUnit a) cut z w hz hw)
          left right lc ls rc rs (sourceProfile epsilon precision) (sourceProfile epsilon precision))) := by
  exact tendsto_finsetSum _ (fun a _=>(tendsto_const_nhds.mul
    (preparedChannels_same_state epsilon precision a p k cut z w hz hw left right lc ls rc rs)))

end LowEnergy.PreparationVacuumFullElectricWard
