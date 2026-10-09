import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCausalRegular

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumCausalPoleResponse
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalZeroRead
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalPoleLegDynamics
open SourcePropagationNativeActionHessian Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourcePoleCurrentHalf sourcePoleCurrentWindow sourceGreen sourceField

/-- One shared Laplace parameter for the source current, original field and all constraint rows. -/
def CausalFrequency (k : PhysicalMomentum) : Set ℂ:=
  {lambda | 0<lambda.re ∧ fixedMomentum k lambda∈regularSource}

def causalPoint (k : PhysicalMomentum) (frequency : CausalFrequency k) : regularSource:=
  ⟨fixedMomentum k frequency.val,frequency.property.2⟩

def causalHalfCurrent (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) : Fin 289→ℂ:=sourcePoleCurrentHalf q (p-k) p l r frequency.val

def causalWindowCurrent (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) (T : ℝ) : Fin 289→ℂ:=sourcePoleCurrentWindow q (p-k) p l r frequency.val T

def causalHalfCosource (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) : Fin 289→ℂ:=
  originalReadback (fixedMomentum k frequency.val)*ᵥcausalHalfCurrent q p k l r frequency

def causalHalfField (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) : Fin 289→ℂ:=
  sourceField (causalPoint k frequency) (causalHalfCurrent q p k l r frequency)

def causalWindowField (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) (T : ℝ) : Fin 289→ℂ:=
  sourceField (causalPoint k frequency) (causalWindowCurrent q p k l r frequency T)

theorem causalCurrent_halfAxis (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) :
    Tendsto (causalWindowCurrent q p k l r frequency) atTop (𝓝 (causalHalfCurrent q p k l r frequency)):=
  tendsto_pi_nhds.mpr (fun i=>sourcePoleCurrentWindow_halfAxis q (p-k) p l r frequency.val frequency.property.1 i)

/-- The half cosource is the limit of the original time source with both genuine endpoint terms. -/
theorem causalCosource_halfAxis (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) :
    Tendsto (fun T=>sourceActualCurrentCosource q (p-k) p l r (physicalSpatial k) frequency.val T) atTop
      (𝓝 (causalHalfCosource q p k l r frequency)):=
  tendsto_pi_nhds.mpr (fun i=>sourceActualCurrentCosource_halfAxis q (p-k) p l r (physicalSpatial k)
    frequency.val frequency.property.1 i)

theorem causalHalfField_whole (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) :
    nativeFourierHessian nativeHessian (fixedMomentum k frequency.val)*ᵥcausalHalfField q p k l r frequency=
      causalHalfCurrent q p k l r frequency-originalRowLift (fixedMomentum k frequency.val)*ᵥ
        (nullProjection*ᵥcausalHalfCosource q p k l r frequency):=by
  rw [causalHalfField,nativeActionFourierHessian_original]
  exact original_forced_field (causalPoint k frequency) _

theorem causalWindowField_whole (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) (T : ℝ) :
    nativeFourierHessian nativeHessian (fixedMomentum k frequency.val)*ᵥcausalWindowField q p k l r frequency T=
      causalWindowCurrent q p k l r frequency T-originalRowLift (fixedMomentum k frequency.val)*ᵥ
        (nullProjection*ᵥsourceActualCurrentCosource q (p-k) p l r (physicalSpatial k) frequency.val T):=by
  rw [causalWindowField,nativeActionFourierHessian_original]
  have returned:=original_forced_field (causalPoint k frequency) (causalWindowCurrent q p k l r frequency T)
  simpa only [sourceCompatibility,causalWindowCurrent,causalPoint,fixedMomentum,sourceActualCurrentWindow_ward] using returned

private theorem field_continuous (point : regularSource) : Continuous (sourceField point):=by
  unfold sourceField
  exact continuous_const.matrix_mulVec continuous_id

theorem causalField_halfAxis (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) :
    Tendsto (causalWindowField q p k l r frequency) atTop (𝓝 (causalHalfField q p k l r frequency)):=
  (field_continuous (causalPoint k frequency)).tendsto _ |>.comp (causalCurrent_halfAxis q p k l r frequency)

/-- Original current tail price transported through every row of the uncleared source Green. -/
def causalFieldTail (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) (T : ℝ) (row : Fin 289) : ℝ:=
  ∑i : Fin 289,‖sourceGreen (causalPoint k frequency) row i‖*
    sourcePoleCurrentTail q (p-k) p l r frequency.val T i

theorem causalField_tail_price (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) (T : ℝ) (future : 0≤T) (row : Fin 289) :
    ‖(causalHalfField q p k l r frequency-causalWindowField q p k l r frequency T) row‖≤
      causalFieldTail q p k l r frequency T row:=by
  have difference : causalHalfField q p k l r frequency-causalWindowField q p k l r frequency T=
      sourceGreen (causalPoint k frequency)*ᵥ(causalHalfCurrent q p k l r frequency-causalWindowCurrent q p k l r frequency T):=by
    unfold causalHalfField causalWindowField sourceField
    rw [Matrix.mulVec_sub]
  rw [difference,Matrix.mulVec,dotProduct]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (sourcePoleCurrentHalf_tail_price q (p-k) p l r frequency.val frequency.property.1 T future i) (norm_nonneg _)

theorem causalFieldTail_tendsto (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) (row : Fin 289) :
    Tendsto (fun T=>causalFieldTail q p k l r frequency T row) atTop (𝓝 0):=by
  have exponent : Tendsto (fun T : ℝ=> -(frequency.val.re/2)*T) atTop atBot:=
    tendsto_id.const_mul_atTop_of_neg (by linarith [frequency.property.1])
  have decay:=Real.tendsto_exp_atBot.comp exponent
  have terms (i : Fin 289) : Tendsto (fun T=>‖sourceGreen (causalPoint k frequency) row i‖*
      sourcePoleCurrentTail q (p-k) p l r frequency.val T i) atTop (𝓝 0):=by
    have result:=(tendsto_const_nhds (x:=‖sourceGreen (causalPoint k frequency) row i‖)).mul
      ((tendsto_const_nhds (x:=(2/frequency.val.re)*sourcePoleCurrentDecay q (p-k) p l r frequency.val i)).mul decay)
    simpa only [sourcePoleCurrentTail,mul_zero,Function.comp_def] using result
  unfold causalFieldTail
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _=>terms i)

/-- Damping does not replace the actual material clock or erase the quantum correction and initial vector. -/
theorem causalHalfCurrent_initial (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) :
    (frequency.val-sourcePhysicalClock (p-k) p l r) • causalHalfCurrent q p k l r frequency=
      sourcePoleEulerInitial q (p-k) p l r+
        (frequency.val-sourcePhysicalClock (p-k) p l r) • sourcePoleCorrectionHalf q (p-k) p l r frequency.val:=
  sourcePoleCurrentHalf_initial q (p-k) p l r frequency.val frequency.property.1

attribute [local irreducible] nativeHessian nativeFourierHessian originalRowLift
  causalHalfField causalHalfCurrent causalHalfCosource

set_option backward.isDefEq.respectTransparency false in
theorem sourceSheet_causal_half_response (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) :
    ∀ᶠ (e : scaleDomain) in scaleApproach,∀ᶠ eta in 𝓝[>] (0:ℝ),
      ∃frequency : CausalFrequency (e.val^2 • n),frequency.val=causalLambda eta (sourceFrequency e.val (sourceSheet branch n unit e.val)) ∧
        Tendsto (causalWindowField q (0:PhysicalMomentum) (e.val^2 • n) l r frequency) atTop
          (𝓝 (causalHalfField q (0:PhysicalMomentum) (e.val^2 • n) l r frequency)):=by
  filter_upwards [sourceSheet_causal_regular branch n unit] with e legal
  filter_upwards [legal,self_mem_nhdsWithin] with eta regular positive
  let frequency : CausalFrequency (e.val^2 • n):=⟨causalLambda eta (sourceFrequency e.val (sourceSheet branch n unit e.val)),
    by rw [causalLambda_re];exact positive,regular⟩
  exact ⟨frequency,rfl,causalField_halfAxis q 0 (e.val^2 • n) l r frequency⟩

end LowEnergy.PreparationVacuumCausalPoleResponse
