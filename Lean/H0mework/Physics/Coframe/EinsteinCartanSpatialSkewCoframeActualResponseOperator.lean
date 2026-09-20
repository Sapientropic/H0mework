import H0mework.Physics.Coframe.EinsteinCartanSkewCoframeActualResponseOperator

/-!
# S9-C3h200i: spatial restriction of the actual skew-coframe principal

The dependency-light C3h108a operator reads the complete 24-coordinate
Lorentz BF-divergence response from an actual affine skew-coframe germ.  This
module fixes only the temporal row of that *input jet* to zero and projects
the actual output to its three spatial rows.  The resulting 18-to-18
principal is still an actual-action readout: the closed coordinate table is
proved equal to the restriction of `skewCoframeActualBFDivergenceCoordinates`.

The displayed inverse is derived after that actual binding.  It proves that
the three spatial output rows uniquely determine the spatial skew-coframe
jet.  The omitted temporal output row is not discarded or freely supplied:
its six coordinates are a fixed prediction of those same spatial outputs.
No source target, residual, range witness, branch, or stationarity receipt is
an input to this construction.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineEinsteinCartanSpatialSkewCoframeActualResponseOperator

open ProofFreeRicherAnholonomicSource
open StageNineEinsteinCartanSkewCoframeActualResponseOperator
open StageNineBlockwiseConstitutive
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Embed the eighteen spatial skew-coframe jet coordinates into the full
24-coordinate carrier.  The temporal derivative row is definitionally zero.
-/
def spatialSkewCoframeJetLift
    (jet : LorentzSpatialBivectorDirection) : LorentzBivectorOneForm :=
  ![0, jet 0, jet 1, jet 2]

@[simp] theorem spatialSkewCoframeJetLift_time
    (jet : LorentzSpatialBivectorDirection) :
    spatialSkewCoframeJetLift jet canonicalLorentzianTimeDirection = 0 := by
  rfl

@[simp] theorem spatialSkewCoframeJetLift_spatial
    (jet : LorentzSpatialBivectorDirection) (spatial : Fin 3) :
    spatialSkewCoframeJetLift jet spatial.succ = jet spatial := by
  fin_cases spatial <;> rfl

/-! ## Base-relative actual binding -/

/-- Install a spatial skew-coframe profile on an already generated actual.
Only the coframe and its derived simple `B` field are replaced. -/
def spatialSkewCoframeActualOn
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection) :
    StageNineHolonomicConfiguration :=
  let coframe := skewCoframeField (spatialSkewCoframeJetLift jet)
  { base with
    coframe := coframe
    gravityAuxiliary := fun point => physicalIIPlusBivector (coframe point) }

/-- The seven primitive fields not rebuilt from the coframe are retained
verbatim from the action-generated base actual. -/
def SpatialSkewCoframeActualOnRetainedFields
    (base actual : StageNineHolonomicConfiguration) : Prop :=
  actual.gravityConnection = base.gravityConnection ∧
    actual.gravitySimplicityMultiplier = base.gravitySimplicityMultiplier ∧
    actual.gaugeConnection = base.gaugeConnection ∧
    actual.gaugeAuxiliary = base.gaugeAuxiliary ∧
    actual.scalar = base.scalar ∧
    actual.matter = base.matter ∧
    actual.conjugateMatter = base.conjugateMatter

theorem spatialSkewCoframeActualOn_retains_fields
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection) :
    SpatialSkewCoframeActualOnRetainedFields base
      (spatialSkewCoframeActualOn base jet) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem spatialSkewCoframeActualOn_coframe_origin
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection) :
    (spatialSkewCoframeActualOn base jet).coframe 0 = 1 := by
  exact affineCoframeFieldOfJet_origin _

theorem spatialSkewCoframeActualOn_gravityAuxiliary_generated
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection) :
    (spatialSkewCoframeActualOn base jet).gravityAuxiliary =
      fun point => physicalIIPlusBivector
        ((spatialSkewCoframeActualOn base jet).coframe point) := by
  rfl

theorem spatialSkewCoframeActualOn_smooth
    (base : StageNineHolonomicConfiguration)
    (baseSmooth : base.Smooth)
    (jet : LorentzSpatialBivectorDirection) :
    (spatialSkewCoframeActualOn base jet).Smooth := by
  rcases baseSmooth with
    ⟨_baseCoframeSmooth, gravityConnectionSmooth,
      _baseGravityAuxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth,
      matterSmooth, conjugateMatterSmooth⟩
  let fullJet := skewCoframeJet (spatialSkewCoframeJetLift jet)
  have coframeSmooth :
      ContDiff ℝ ∞ (affineCoframeFieldOfJet fullJet) := by
    apply contDiff_pi'
    intro internal
    apply contDiff_pi'
    intro coordinate
    exact affineCoframeFieldOfJet_componentwiseSmooth
      fullJet internal coordinate
  have gravityAuxiliarySmooth :
      ContDiff ℝ ∞ fun point =>
        physicalIIPlusBivector (affineCoframeFieldOfJet fullJet point) :=
    physicalIIPlusBivector_contDiff.comp coframeSmooth
  exact
    ⟨fun internal coordinate =>
        contDiff_pi.mp (contDiff_pi.mp coframeSmooth internal) coordinate,
      gravityConnectionSmooth,
      fun internalPair spacetimePair =>
        contDiff_pi.mp
          (contDiff_pi.mp gravityAuxiliarySmooth internalPair)
          spacetimePair,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

theorem spatialSkewCoframeActualOn_nondegenerate
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection) :
    (spatialSkewCoframeActualOn base jet).Nondegenerate := by
  intro point
  change
    Matrix.det
        ((skewCoframeActual (spatialSkewCoframeJetLift jet)).coframe point) ≠
      0
  exact skewCoframeActual_nondegenerate _ point

/-- A spatial skew-coframe producer carries no temporal input jet.  Hence the
temporal derivative of its BF momentum vanishes for every base actual.  This
is a property of the generated coframe/simple-`B` profile, not a receipt
stored in the base. -/
theorem spatialSkewCoframeActualOn_BFMomentum_timeDerivative_zero
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection)
    (direction : LorentzBivectorOneForm) :
    fieldDirectionalDerivative
        (lorentzConnectionBFDifferentialMomentum
          (spatialSkewCoframeActualOn base jet)
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection direction))
        0 canonicalLorentzianTimeDirection = 0 := by
  change
    fieldDirectionalDerivative
        (lorentzConnectionBFDifferentialMomentum
          (skewCoframeActual (spatialSkewCoframeJetLift jet))
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection direction))
        0 canonicalLorentzianTimeDirection = 0
  rw [skewCoframeMomentum_directionalDerivative_origin,
    simpleBPairingTangent_eq_normalForm]
  simp only [simpleBPairingTangentNormalForm,
    canonicalLorentzianTimeDirection]
  rw [show spatialSkewCoframeJetLift jet 0 = 0 by rfl]
  simp

/-- Closed coordinate form of the actual BF-divergence operator after the
zero-temporal-row input restriction and the spatial-output projection. -/
def spatialSkewCoframeDivergenceResponseCoordinates
    (jet : LorentzSpatialBivectorDirection) :
    LorentzSpatialBivectorDirection :=
  ![
    ![
      jet 1 1 + jet 2 2,
      -jet 1 0,
      -jet 2 0,
      jet 1 4 + jet 2 5,
      -jet 1 3,
      -jet 2 3],
    ![
      -jet 0 1,
      jet 0 0 + jet 2 2,
      -jet 2 1,
      -jet 0 4,
      jet 0 3 + jet 2 5,
      -jet 2 4],
    ![
      -jet 0 2,
      -jet 1 2,
      jet 0 0 + jet 1 1,
      -jet 0 5,
      -jet 1 5,
      jet 0 3 + jet 1 4]
  ]

/-- The restricted operator is defined by the already proved actual
BF-divergence readout, not by the coordinate table above. -/
def spatialSkewCoframeActualBFDivergenceCoordinates
    (jet : LorentzSpatialBivectorDirection) :
    LorentzSpatialBivectorDirection :=
  fun spatial internalPair =>
    skewCoframeActualBFDivergenceCoordinates
      (spatialSkewCoframeJetLift jet) spatial.succ internalPair

/-- Spatial BF-divergence coordinates read from the base-relative actual. -/
def spatialSkewCoframeActualOnBFDivergenceCoordinates
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection) :
    LorentzSpatialBivectorDirection :=
  fun spatial internalPair =>
    lorentzConnectionBFDifferentialMomentumDivergence
      (spatialSkewCoframeActualOn base jet)
      (lorentzBivectorOneFormCoordinateDirection spatial.succ internalPair) 0

/-- Complete 24-coordinate BF-divergence readout of the same base-relative
actual.  Its temporal row remains an output of the spatial producer. -/
def spatialSkewCoframeActualOnFullBFDivergenceCoordinates
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    lorentzConnectionBFDifferentialMomentumDivergence
      (spatialSkewCoframeActualOn base jet)
      (lorentzBivectorOneFormCoordinateDirection formDirection internalPair) 0

/-- The complete BF-divergence functional of a base-relative spatial
skew-coframe actual is the functional of the generated skew-coframe profile.
All retained base fields lie outside this momentum channel.  Stating the
transport at generic `base` avoids unfolding a later, large source actual. -/
theorem spatialSkewCoframeActualOn_fullBFMomentumDivergence_eq_skew
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection)
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionBFDifferentialMomentumDivergence
        (spatialSkewCoframeActualOn base jet) direction 0 =
      lorentzConnectionBFDifferentialMomentumDivergence
        (skewCoframeActual (spatialSkewCoframeJetLift jet)) direction 0 := by
  rfl

/-- BF divergence reads only the generated coframe/simple-`B` pair, so the
base-relative actual realizes the same actual principal. -/
theorem spatialSkewCoframeActualOnBFDivergenceCoordinates_eq_actualOperator
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection) :
    spatialSkewCoframeActualOnBFDivergenceCoordinates base jet =
      spatialSkewCoframeActualBFDivergenceCoordinates jet := by
  rfl

theorem
    spatialSkewCoframeActualOnFullBFDivergenceCoordinates_eq_actualOperator
    (base : StageNineHolonomicConfiguration)
    (jet : LorentzSpatialBivectorDirection) :
    spatialSkewCoframeActualOnFullBFDivergenceCoordinates base jet =
      skewCoframeActualBFDivergenceCoordinates
        (spatialSkewCoframeJetLift jet) := by
  rfl

/-- Pointwise action provenance of the restricted operator. -/
theorem spatialSkewCoframeActualBFDivergenceCoordinates_apply_actual
    (jet : LorentzSpatialBivectorDirection)
    (spatial : Fin 3) (internalPair : Fin 6) :
    spatialSkewCoframeActualBFDivergenceCoordinates jet spatial internalPair =
      lorentzConnectionBFDifferentialMomentumDivergence
        (skewCoframeActual (spatialSkewCoframeJetLift jet))
        (lorentzBivectorOneFormCoordinateDirection spatial.succ internalPair)
        0 := by
  rfl

/-- The actual restricted operator is exactly the displayed 18-coordinate
closed form. -/
theorem spatialSkewCoframeActualBFDivergenceCoordinates_eq_closedForm
    (jet : LorentzSpatialBivectorDirection) :
    spatialSkewCoframeActualBFDivergenceCoordinates jet =
      spatialSkewCoframeDivergenceResponseCoordinates jet := by
  funext spatial internalPair
  fin_cases spatial <;> fin_cases internalPair <;>
    simp [spatialSkewCoframeActualBFDivergenceCoordinates,
      spatialSkewCoframeDivergenceResponseCoordinates,
      spatialSkewCoframeJetLift,
      skewCoframeActualBFDivergenceCoordinates_apply,
      skewCoframeDivergenceResponseCoordinates,
      canonicalLorentzSpatialBivectorOneForm]

/-- Explicit inverse of the spatial actual principal. -/
def einsteinCartanSpatialSkewCoframeCoordinates
    (response : LorentzSpatialBivectorDirection) :
    LorentzSpatialBivectorDirection :=
  ![
    ![
      (response 1 1 + response 2 2 - response 0 0) / 2,
      -response 1 0,
      -response 2 0,
      (response 1 4 + response 2 5 - response 0 3) / 2,
      -response 1 3,
      -response 2 3],
    ![
      -response 0 1,
      (response 0 0 + response 2 2 - response 1 1) / 2,
      -response 2 1,
      -response 0 4,
      (response 0 3 + response 2 5 - response 1 4) / 2,
      -response 2 4],
    ![
      -response 0 2,
      -response 1 2,
      (response 0 0 + response 1 1 - response 2 2) / 2,
      -response 0 5,
      -response 1 5,
      (response 0 3 + response 1 4 - response 2 5) / 2]
  ]

theorem einsteinCartanSpatialSkewCoframeCoordinates_closedForm_leftInverse
    (jet : LorentzSpatialBivectorDirection) :
    einsteinCartanSpatialSkewCoframeCoordinates
        (spatialSkewCoframeDivergenceResponseCoordinates jet) = jet := by
  funext spatial internalPair
  fin_cases spatial <;> fin_cases internalPair <;>
    simp [einsteinCartanSpatialSkewCoframeCoordinates,
      spatialSkewCoframeDivergenceResponseCoordinates] <;>
    ring

theorem einsteinCartanSpatialSkewCoframeCoordinates_closedForm_rightInverse
    (response : LorentzSpatialBivectorDirection) :
    spatialSkewCoframeDivergenceResponseCoordinates
        (einsteinCartanSpatialSkewCoframeCoordinates response) =
      response := by
  funext spatial internalPair
  fin_cases spatial <;> fin_cases internalPair <;>
    simp [einsteinCartanSpatialSkewCoframeCoordinates,
      spatialSkewCoframeDivergenceResponseCoordinates] <;>
    ring

theorem einsteinCartanSpatialSkewCoframeCoordinates_leftInverse
    (jet : LorentzSpatialBivectorDirection) :
    einsteinCartanSpatialSkewCoframeCoordinates
        (spatialSkewCoframeActualBFDivergenceCoordinates jet) = jet := by
  rw [spatialSkewCoframeActualBFDivergenceCoordinates_eq_closedForm]
  exact
    einsteinCartanSpatialSkewCoframeCoordinates_closedForm_leftInverse jet

theorem einsteinCartanSpatialSkewCoframeCoordinates_rightInverse
    (response : LorentzSpatialBivectorDirection) :
    spatialSkewCoframeActualBFDivergenceCoordinates
        (einsteinCartanSpatialSkewCoframeCoordinates response) =
      response := by
  rw [spatialSkewCoframeActualBFDivergenceCoordinates_eq_closedForm]
  exact
    einsteinCartanSpatialSkewCoframeCoordinates_closedForm_rightInverse
      response

theorem spatialSkewCoframeActualBFDivergenceCoordinates_bijective :
    Function.Bijective spatialSkewCoframeActualBFDivergenceCoordinates := by
  constructor
  · intro first second equality
    have lifted :=
      congrArg einsteinCartanSpatialSkewCoframeCoordinates equality
    simpa only [einsteinCartanSpatialSkewCoframeCoordinates_leftInverse]
      using lifted
  · intro response
    exact
      ⟨einsteinCartanSpatialSkewCoframeCoordinates response,
        einsteinCartanSpatialSkewCoframeCoordinates_rightInverse response⟩

/-- The six temporal output coordinates forced by the same spatial actual
response.  They are readouts, not additional input data. -/
def spatialSkewCoframeTemporalBFDivergencePrediction
    (spatialResponse : LorentzSpatialBivectorDirection) : Fin 6 → ℝ :=
  ![
    spatialResponse 2 4 - spatialResponse 1 5,
    spatialResponse 0 5 - spatialResponse 2 3,
    spatialResponse 1 3 - spatialResponse 0 4,
    spatialResponse 2 1 - spatialResponse 1 2,
    spatialResponse 0 2 - spatialResponse 2 0,
    spatialResponse 1 0 - spatialResponse 0 1
  ]

/-- For every spatial jet, the temporal row of the complete actual output is
exactly the six-coordinate prediction determined by its spatial output. -/
theorem spatialSkewCoframeActualBFDivergenceCoordinates_temporal_prediction
    (jet : LorentzSpatialBivectorDirection) :
    skewCoframeActualBFDivergenceCoordinates
        (spatialSkewCoframeJetLift jet)
        canonicalLorentzianTimeDirection =
      spatialSkewCoframeTemporalBFDivergencePrediction
        (spatialSkewCoframeActualBFDivergenceCoordinates jet) := by
  funext internalPair
  fin_cases internalPair <;>
    simp [spatialSkewCoframeTemporalBFDivergencePrediction,
      spatialSkewCoframeActualBFDivergenceCoordinates,
      spatialSkewCoframeJetLift,
      skewCoframeActualBFDivergenceCoordinates_apply,
      skewCoframeDivergenceResponseCoordinates,
      canonicalLorentzSpatialBivectorOneForm,
      canonicalLorentzianTimeDirection] <;>
    ring

/-- Applying the canonical inverse to any spatial response reconstructs the
unique full actual output whose temporal row is the same fixed prediction. -/
theorem einsteinCartanSpatialSkewCoframeCoordinates_temporal_prediction
    (response : LorentzSpatialBivectorDirection) :
    skewCoframeActualBFDivergenceCoordinates
        (spatialSkewCoframeJetLift
          (einsteinCartanSpatialSkewCoframeCoordinates response))
        canonicalLorentzianTimeDirection =
      spatialSkewCoframeTemporalBFDivergencePrediction response := by
  rw [spatialSkewCoframeActualBFDivergenceCoordinates_temporal_prediction]
  rw [einsteinCartanSpatialSkewCoframeCoordinates_rightInverse]

/-- Base-relative restatement: after the spatial action target uniquely
generates the jet, the omitted temporal row is still a prediction, not a
constructor input. -/
theorem spatialSkewCoframeActualOn_temporal_prediction
    (base : StageNineHolonomicConfiguration)
    (response : LorentzSpatialBivectorDirection) :
    spatialSkewCoframeActualOnFullBFDivergenceCoordinates base
        (einsteinCartanSpatialSkewCoframeCoordinates response)
        canonicalLorentzianTimeDirection =
      spatialSkewCoframeTemporalBFDivergencePrediction response := by
  rw [spatialSkewCoframeActualOnFullBFDivergenceCoordinates_eq_actualOperator]
  exact einsteinCartanSpatialSkewCoframeCoordinates_temporal_prediction
    response

end

end
  SaturationMonoid.PhysicsCore.StageNineEinsteinCartanSpatialSkewCoframeActualResponseOperator
