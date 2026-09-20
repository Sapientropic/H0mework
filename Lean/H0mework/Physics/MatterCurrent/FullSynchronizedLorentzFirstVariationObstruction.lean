import H0mework.Physics.Lorentz.LorentzTemporalGaussFirstVariation
import H0mework.Physics.MatterCurrent.FullSynchronizedLorentzResponse

/-!
# C3h204: latest-current Lorentz first-variation channels

C3h203 generated a complete synchronized Lorentz action dual and a faithful
BF-momentum first-jet actual from the latest C3h200n current.  This module
judges that new actual at the same canonical contact without assuming
tangency.

It constructs four component-indexed channels:

```text
actual gravity-BF derivative
actual matter-spin derivative
actual mixed BF-momentum derivative
producer coframe/stress torque.
```

The first three sum to the genuine `HasDerivAt` coefficient of the C3h203
actual's temporal-Gauss residual.  The fourth has its own genuine derivative
provenance from the corrected producer-density path and vanishes by the
coframe equation that generated the response.  It is producer consistency,
not an independent Ward constraint.

The channels deliberately remain separated.  The repository does not yet
identify the producer coframe density with the judged actual's origin density,
nor does it supply the required multiplier Lorentz transformation law.
Consequently this module does **not** add the four values and call the result
a full local-Lorentz Noether obstruction.  No obstruction value, support
branch, repair coefficient, endpoint shell, stationarity receipt, or equation
certificate enters a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzFirstVariationObstruction

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedLorentzResponse
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionVariation
open StageNineLorentzTemporalGaussFirstVariation
open StageNineLorentzTemporalGaussResidualTangency
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzResponse
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private abbrev CurrentState : StageNineCauchyState :=
  PreContorsionFullLorentzTriangularCurrent

private abbrev JudgedActual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentFullSynchronizedLorentzActual

/-! ## Four responsibility-preserving channels -/

/-- Data carrier for the three same-actual Gauss sectors and the separately
provenanced producer coframe sector.  It stores values, not a vanishing
certificate or a preferred totalization. -/
structure FullSynchronizedLorentzFirstVariationChannels where
  gravityBF : LorentzTemporalGaussResidualCarrier
  matterSpin : LorentzTemporalGaussResidualCarrier
  mixedBF : LorentzTemporalGaussResidualCarrier
  producerCoframe : LorentzTemporalGaussResidualCarrier

def positiveP506MatterCurrentFullSynchronizedLorentzGravityBFTangencyTerm
    (component : LorentzTemporalBivectorDirection) : ℝ :=
  lorentzTemporalGaussGravityBFTangencyTerm JudgedActual component

def positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm
    (component : LorentzTemporalBivectorDirection) : ℝ :=
  lorentzTemporalGaussMatterSpinTangencyTerm positiveSmoothUnifiedSource
    JudgedActual component

def positiveP506MatterCurrentFullSynchronizedLorentzMixedBFTangencyTerm
    (component : LorentzTemporalBivectorDirection) : ℝ :=
  lorentzTemporalGaussMixedBFTangencyTerm JudgedActual component

/-- The fourth channel remains explicitly attached to the producer graph.
It is not silently re-labelled as an actual-origin coframe Ward term. -/
def positiveP506MatterCurrentFullSynchronizedLorentzProducerCoframeTorque
    (component : LorentzTemporalBivectorDirection) : ℝ :=
  currentFullSynchronizedProducerLorentzCoframeTorque
    positiveSmoothUnifiedSource CurrentState 0 component

def positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels :
    FullSynchronizedLorentzFirstVariationChannels where
  gravityBF :=
    positiveP506MatterCurrentFullSynchronizedLorentzGravityBFTangencyTerm
  matterSpin :=
    positiveP506MatterCurrentFullSynchronizedLorentzMatterSpinTangencyTerm
  mixedBF :=
    positiveP506MatterCurrentFullSynchronizedLorentzMixedBFTangencyTerm
  producerCoframe :=
    positiveP506MatterCurrentFullSynchronizedLorentzProducerCoframeTorque

/-! ## Genuine same-actual temporal-Gauss obstruction -/

/-- Component-indexed temporal-Gauss tangency obstruction of the C3h203
actual.  No value or zero certificate is stored. -/
def positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction :
    LorentzTemporalGaussResidualCarrier :=
  lorentzTemporalGaussTangencyObstruction positiveSmoothUnifiedSource
    JudgedActual

/-- Exact three-sector decomposition on the same judged actual. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction_eq_sectors
    (component : LorentzTemporalBivectorDirection) :
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
        component =
      positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.gravityBF
          component +
        positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.matterSpin
          component +
        positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.mixedBF
          component := by
  exact lorentzTemporalGaussTangencyObstruction_eq_sectors
    positiveSmoothUnifiedSource JudgedActual
    positiveP506MatterCurrentFullSynchronizedLorentzActual_smooth
    positiveP506MatterCurrentFullSynchronizedLorentzActual_nondegenerate
    component

/-- The obstruction is the genuine derivative coefficient of the same
actual's temporal-Gauss residual trace. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_lorentzTemporalGaussResidual_timeTrace_hasDerivAt_obstruction
    (component : LorentzTemporalBivectorDirection) :
    HasDerivAt
      (lorentzTemporalGaussResidualTimeTrace positiveSmoothUnifiedSource
        JudgedActual 0 component)
      (positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
        component)
      0 := by
  exact lorentzTemporalGaussResidualTimeTrace_hasDerivAt_obstruction
    positiveSmoothUnifiedSource JudgedActual
    positiveP506MatterCurrentFullSynchronizedLorentzActual_smooth
    positiveP506MatterCurrentFullSynchronizedLorentzActual_nondegenerate
    component

/-! ## Separately provenanced producer coframe channel -/

/-- Genuine derivative provenance of the producer coframe/stress torque. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzProducerCoframeDensityPath_hasDerivAt_torque
    (component : LorentzTemporalBivectorDirection) :
    HasDerivAt
      (positiveP506MatterCurrentFullSynchronizedLorentzCoframeDensityPath
        (lorentzLeftCoframeTangent component
          ((currentCanonicalFullActionActual positiveSmoothUnifiedSource
            CurrentState 0).coframe 0)))
      (positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.producerCoframe
        component)
      0 := by
  exact
    currentFullSynchronizedProducerCoframeDensityPath_hasDerivAt
      positiveSmoothUnifiedSource CurrentState 0
      preContorsionFullLorentzTriangularCurrent_coframe_origin
      (lorentzLeftCoframeTangent component
        ((currentCanonicalFullActionActual positiveSmoothUnifiedSource
          CurrentState 0).coframe 0))

/-- The producer coframe channel vanishes by the same action equation that
generated the response.  This does not set the actual Gauss obstruction to
zero. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzProducerCoframeTorque_eq_zero
    (component : LorentzTemporalBivectorDirection) :
    positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.producerCoframe
        component =
      0 := by
  exact currentFullSynchronizedProducerLorentzCoframeTorque_eq_zero
    positiveSmoothUnifiedSource CurrentState 0 component

/-! ## Zero fiber and support responsibility -/

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction_eq_zero_iff :
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction =
          0 ↔
      ∀ component,
        positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
            component =
          0 := by
  constructor
  · intro obstructionZero component
    exact congrFun obstructionZero component
  · intro pointwiseZero
    funext component
    exact pointwiseZero component

/-- Finite coordinate support of the generated actual obstruction.  It
records responsibility but does not select a repair branch. -/
def positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstructionSupport :
    Finset (Fin 6) :=
  Finset.univ.filter fun internalPair =>
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
      (EuclideanSpace.single internalPair 1) ≠ 0

@[simp] theorem
    mem_positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstructionSupport_iff
    (internalPair : Fin 6) :
    internalPair ∈
        positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstructionSupport ↔
        positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
          (EuclideanSpace.single internalPair 1) ≠
        0 := by
  rw [positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstructionSupport,
    Finset.mem_filter]
  simp

/-! ## No-premise exact-source checkpoint -/

/-- C3h204 binds the new actual derivative and separated producer coframe
channel to exact P506/L0 provenance.  No vanishing of the actual obstruction
and no four-sector Ward totalization is claimed. -/
structure
    PositiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannelsLaw :
    Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  endpointEleven :
    positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos =
      11
  judgedActualGenerated :
    JudgedActual =
      currentFullSynchronizedLorentzActualFirstJetLift
        positiveSmoothUnifiedSource CurrentState 0
  actualSmooth : JudgedActual.Smooth
  actualNondegenerate : JudgedActual.Nondegenerate
  actualGaussSectorTrace : ∀ component,
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
        component =
      positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.gravityBF
          component +
        positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.matterSpin
          component +
        positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.mixedBF
          component
  actualGaussFirstVariation : ∀ component,
    HasDerivAt
      (lorentzTemporalGaussResidualTimeTrace positiveSmoothUnifiedSource
        JudgedActual 0 component)
      (positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
        component)
      0
  producerCoframeDerivative : ∀ component,
    HasDerivAt
      (positiveP506MatterCurrentFullSynchronizedLorentzCoframeDensityPath
        (lorentzLeftCoframeTangent component
          ((currentCanonicalFullActionActual positiveSmoothUnifiedSource
            CurrentState 0).coframe 0)))
      (positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.producerCoframe
        component)
      0
  producerCoframeConsistency : ∀ component,
    positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels.producerCoframe
        component =
      0
  actualGaussFaithfulZeroFiber :
    positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction =
          0 ↔
      ∀ component,
        positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction
            component =
          0

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannels_realizes_C3h204 :
    PositiveP506MatterCurrentFullSynchronizedLorentzFirstVariationChannelsLaw := by
  exact
    { exactP506L0Lineage :=
        positiveP506MatterCurrentFullSynchronizedLorentzResponse_realizes_C3h203
          |>.exactP506L0Lineage
      endpointEleven :=
        positiveP506MatterCurrentFullSynchronizedLorentzResponse_realizes_C3h203
          |>.endpointEleven
      judgedActualGenerated := rfl
      actualSmooth :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_smooth
      actualNondegenerate :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_nondegenerate
      actualGaussSectorTrace :=
        positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction_eq_sectors
      actualGaussFirstVariation :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_lorentzTemporalGaussResidual_timeTrace_hasDerivAt_obstruction
      producerCoframeDerivative :=
        positiveP506MatterCurrentFullSynchronizedLorentzProducerCoframeDensityPath_hasDerivAt_torque
      producerCoframeConsistency :=
        positiveP506MatterCurrentFullSynchronizedLorentzProducerCoframeTorque_eq_zero
      actualGaussFaithfulZeroFiber :=
        positiveP506MatterCurrentFullSynchronizedLorentzGaussTangencyObstruction_eq_zero_iff }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzFirstVariationObstruction
