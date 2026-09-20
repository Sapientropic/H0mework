import H0mework.Physics.Gauge.SU7MotherGaugeConnection

/-!
# SU(7) mother gauge action and exact Stage-5 restriction

A single SU(7) mother connection, adjoint two-form, and multiplier are read
through normalized color/weak/hypercharge trace coordinates.  One mother
coupling plus positive trace normalizations generates the three Stage-5
couplings.  The action adds a continuous full cross-block Frobenius penalty.
On the exact P286 block lift this penalty vanishes and the mother action is
strictly equal to the Stage-5 nonseparable action.
-/

namespace SaturationMonoid.PhysicsCore.SU7MotherGaugeAction

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open EmpiricalReferenceScaleCouplingBoundary
open UnifiedPhysicalMasterAction
open SourceRelativePhysicalStationaryFamily
open NonseparableGravityGaugeSourceAction

noncomputable section

def motherColorCoordinate (matrix : SU7MotherLieMatrix) : ℝ :=
  ((matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
    (Sum.inl 0) (Sum.inl 0)).im

def motherWeakCoordinate (matrix : SU7MotherLieMatrix) : ℝ :=
  ((matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
    (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0))).im

def motherHyperchargeCoordinate (matrix : SU7MotherLieMatrix) : ℝ :=
  ((matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
    hyperPlusIndex hyperPlusIndex).im

def sectorP286Value (strong weak hypercharge : ℝ) : P286LieBlockData :=
  (strong • colorCartanGenerator,
    weak • weakCartanGenerator,
    realScaleHypercharge hypercharge hyperchargeGenerator)

def liftSectorValue (strong weak hypercharge : ℝ) : SU7MotherLieMatrix :=
  p286LieBlockEmbed (sectorP286Value strong weak hypercharge)

@[simp] theorem motherColorCoordinate_liftSectorValue
    (strong weak hypercharge : ℝ) :
    motherColorCoordinate (liftSectorValue strong weak hypercharge) = strong := by
  simp [motherColorCoordinate, liftSectorValue, sectorP286Value,
    p286LieBlockEmbed, rawP286LieBlock, colorCartanGenerator,
    colorCartanRaw]

@[simp] theorem motherWeakCoordinate_liftSectorValue
    (strong weak hypercharge : ℝ) :
    motherWeakCoordinate (liftSectorValue strong weak hypercharge) = weak := by
  simp [motherWeakCoordinate, liftSectorValue, sectorP286Value,
    p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
    weakCartanGenerator, weakCartanRaw]

@[simp] theorem motherHyperchargeCoordinate_liftSectorValue
    (strong weak hypercharge : ℝ) :
    motherHyperchargeCoordinate (liftSectorValue strong weak hypercharge) =
      hypercharge := by
  simp [motherHyperchargeCoordinate, liftSectorValue, sectorP286Value,
    p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
    hyperchargeLieBlock, scalarLieBlock, realScaleHypercharge,
    hyperchargeGenerator, hyperPlusIndex]

structure SU7MotherGaugeConfiguration where
  connection : SU7MotherGaugeConnection
  auxiliary : Fin 6 → SU7MotherLieMatrix
  constitutiveMultiplier : Fin 6 → SU7MotherLieMatrix

@[simp] theorem motherCurvature_zeroPotential
    (exteriorDerivative : Fin 6 → SU7MotherLieMatrix) (pair : Fin 6) :
    motherCurvature
        ({ potential := fun _ => 0
           exteriorDerivative := exteriorDerivative } :
          SU7MotherGaugeConnection) pair = exteriorDerivative pair := by
  apply Subtype.ext
  simp [motherCurvature, suLieBracket]

def projectMotherGaugeConfiguration
    (q : SU7MotherGaugeConfiguration) : StandardModelGaugeConfiguration where
  strong := {
    curvature := fun pair => motherColorCoordinate (motherCurvature q.connection pair)
    auxiliary := fun pair => motherColorCoordinate (q.auxiliary pair)
    constitutiveMultiplier := fun pair =>
      motherColorCoordinate (q.constitutiveMultiplier pair) }
  weak := {
    curvature := fun pair => motherWeakCoordinate (motherCurvature q.connection pair)
    auxiliary := fun pair => motherWeakCoordinate (q.auxiliary pair)
    constitutiveMultiplier := fun pair =>
      motherWeakCoordinate (q.constitutiveMultiplier pair) }
  hypercharge := {
    curvature := fun pair =>
      motherHyperchargeCoordinate (motherCurvature q.connection pair)
    auxiliary := fun pair => motherHyperchargeCoordinate (q.auxiliary pair)
    constitutiveMultiplier := fun pair =>
      motherHyperchargeCoordinate (q.constitutiveMultiplier pair) }

def liftStageFiveGaugeConfiguration
    (q : StandardModelGaugeConfiguration) : SU7MotherGaugeConfiguration where
  connection := {
    potential := fun _ => 0
    exteriorDerivative := fun pair =>
      liftSectorValue (q.strong.curvature pair) (q.weak.curvature pair)
        (q.hypercharge.curvature pair) }
  auxiliary := fun pair =>
    liftSectorValue (q.strong.auxiliary pair) (q.weak.auxiliary pair)
      (q.hypercharge.auxiliary pair)
  constitutiveMultiplier := fun pair =>
    liftSectorValue (q.strong.constitutiveMultiplier pair)
      (q.weak.constitutiveMultiplier pair)
      (q.hypercharge.constitutiveMultiplier pair)

@[simp] theorem motherCurvature_liftStageFiveGaugeConfiguration
    (q : StandardModelGaugeConfiguration) (pair : Fin 6) :
    motherCurvature (liftStageFiveGaugeConfiguration q).connection pair =
      liftSectorValue (q.strong.curvature pair) (q.weak.curvature pair)
        (q.hypercharge.curvature pair) := by
  apply Subtype.ext
  simp [motherCurvature, liftStageFiveGaugeConfiguration, suLieBracket]

@[simp] theorem projectMotherGaugeConfiguration_lift
    (q : StandardModelGaugeConfiguration) :
    projectMotherGaugeConfiguration (liftStageFiveGaugeConfiguration q) = q := by
  rcases q with ⟨⟨strongF, strongB, strongLambda⟩,
    ⟨weakF, weakB, weakLambda⟩, ⟨hyperF, hyperB, hyperLambda⟩⟩
  simp [projectMotherGaugeConfiguration, liftStageFiveGaugeConfiguration]

structure MotherTraceNormalizations where
  strong : ℝˣ
  weak : ℝˣ
  hypercharge : ℝˣ
  strong_pos : 0 < (strong : ℝ)
  weak_pos : 0 < (weak : ℝ)
  hypercharge_pos : 0 < (hypercharge : ℝ)

/-- One mother coupling plus three positive trace normalizations. -/
structure SU7MotherCouplingBoundary where
  renormalizationScale : ℝ
  scale_pos : 0 < renormalizationScale
  motherCouplingSquared : ℝˣ
  mother_pos : 0 < (motherCouplingSquared : ℝ)
  traceNormalizations : MotherTraceNormalizations

def generatedStageFiveBoundary
    (boundary : SU7MotherCouplingBoundary) :
    EmpiricalReferenceScaleCouplings where
  renormalizationScale := boundary.renormalizationScale
  scale_pos := boundary.scale_pos
  strongCouplingSquared :=
    boundary.motherCouplingSquared * boundary.traceNormalizations.strong
  weakCouplingSquared :=
    boundary.motherCouplingSquared * boundary.traceNormalizations.weak
  hyperchargeCouplingSquared :=
    boundary.motherCouplingSquared * boundary.traceNormalizations.hypercharge
  strong_pos := mul_pos boundary.mother_pos
    boundary.traceNormalizations.strong_pos
  weak_pos := mul_pos boundary.mother_pos
    boundary.traceNormalizations.weak_pos
  hypercharge_pos := mul_pos boundary.mother_pos
    boundary.traceNormalizations.hypercharge_pos

def motherBoundaryOfStageFive
    (boundary : EmpiricalReferenceScaleCouplings) :
    SU7MotherCouplingBoundary where
  renormalizationScale := boundary.renormalizationScale
  scale_pos := boundary.scale_pos
  motherCouplingSquared := 1
  mother_pos := by norm_num
  traceNormalizations := {
    strong := boundary.strongCouplingSquared
    weak := boundary.weakCouplingSquared
    hypercharge := boundary.hyperchargeCouplingSquared
    strong_pos := boundary.strong_pos
    weak_pos := boundary.weak_pos
    hypercharge_pos := boundary.hypercharge_pos }

@[simp] theorem generatedStageFiveBoundary_motherBoundaryOfStageFive
    (boundary : EmpiricalReferenceScaleCouplings) :
    generatedStageFiveBoundary (motherBoundaryOfStageFive boundary) = boundary := by
  rcases boundary with ⟨scale, scale_pos, strong, weak, hyper,
    strong_pos, weak_pos, hyper_pos⟩
  simp [generatedStageFiveBoundary, motherBoundaryOfStageFive]

/-- Squared Frobenius residual of all cross-spectral-block entries. -/
def offBlockEnergy (matrix : SU7MotherLieMatrix) : ℝ :=
  ∑ row : SU7MotherIndex, ∑ column : SU7MotherIndex,
    if breakingLevel row = breakingLevel column then 0
    else Complex.normSq
      ((matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) row column)

theorem offBlockEnergy_nonneg (matrix : SU7MotherLieMatrix) :
    0 ≤ offBlockEnergy matrix := by
  unfold offBlockEnergy
  apply Finset.sum_nonneg
  intro row _
  apply Finset.sum_nonneg
  intro column _
  split
  · norm_num
  · exact Complex.normSq_nonneg _

@[simp] theorem offBlockEnergy_zero :
    offBlockEnergy (0 : SU7MotherLieMatrix) = 0 := by
  simp [offBlockEnergy]

@[simp] theorem offBlockEnergy_p286LieBlockEmbed
    (data : P286LieBlockData) :
    offBlockEnergy (p286LieBlockEmbed data) = 0 := by
  unfold offBlockEnergy
  apply Finset.sum_eq_zero
  intro row _
  apply Finset.sum_eq_zero
  intro column _
  by_cases sameLevel : breakingLevel row = breakingLevel column
  · simp [sameLevel]
  · have entryZero := selected_entry_zero_of_breakingLevel_ne
      positiveSource (p286LieBlockEmbed data)
      (p286LieBlockEmbed_selected positiveSource data)
      row column sameLevel
    simp [sameLevel, entryZero]

def motherBreakingPenalty (q : SU7MotherGaugeConfiguration) : ℝ :=
  (∑ direction : LorentzianIndex,
      offBlockEnergy (q.connection.potential direction)) +
    (∑ pair : Fin 6,
      offBlockEnergy (q.connection.exteriorDerivative pair)) +
    (∑ pair : Fin 6, offBlockEnergy (q.auxiliary pair)) +
    (∑ pair : Fin 6, offBlockEnergy (q.constitutiveMultiplier pair))

theorem motherBreakingPenalty_nonneg (q : SU7MotherGaugeConfiguration) :
    0 ≤ motherBreakingPenalty q := by
  unfold motherBreakingPenalty
  apply add_nonneg
  · apply add_nonneg
    · apply add_nonneg
      · exact Finset.sum_nonneg fun direction _ =>
          offBlockEnergy_nonneg (q.connection.potential direction)
      · exact Finset.sum_nonneg fun pair _ =>
          offBlockEnergy_nonneg (q.connection.exteriorDerivative pair)
    · exact Finset.sum_nonneg fun pair _ =>
        offBlockEnergy_nonneg (q.auxiliary pair)
  · exact Finset.sum_nonneg fun pair _ =>
      offBlockEnergy_nonneg (q.constitutiveMultiplier pair)

@[simp] theorem motherBreakingPenalty_lift
    (q : StandardModelGaugeConfiguration) :
    motherBreakingPenalty (liftStageFiveGaugeConfiguration q) = 0 := by
  simp [motherBreakingPenalty, liftStageFiveGaugeConfiguration,
    liftSectorValue]

structure SU7MotherUnifiedConfiguration where
  gravity : JetLocalPhysicalPlebanskiAction.Configuration
  gauge : SU7MotherGaugeConfiguration

def projectMotherUnifiedConfiguration
    (q : SU7MotherUnifiedConfiguration) : UnifiedConfiguration where
  gravity := q.gravity
  gauge := projectMotherGaugeConfiguration q.gauge

def liftStageFiveUnifiedConfiguration
    (q : UnifiedConfiguration) : SU7MotherUnifiedConfiguration where
  gravity := q.gravity
  gauge := liftStageFiveGaugeConfiguration q.gauge

@[simp] theorem projectMotherUnifiedConfiguration_lift
    (q : UnifiedConfiguration) :
    projectMotherUnifiedConfiguration (liftStageFiveUnifiedConfiguration q) = q := by
  rcases q with ⟨gravity, gauge⟩
  simp [projectMotherUnifiedConfiguration, liftStageFiveUnifiedConfiguration]

/-- Stage-6 mother action: Stage-5 physics evaluated on derived trace
coordinates plus a continuous cross-block responsibility penalty. -/
def motherMasterAction
    (source : Source) (boundary : SU7MotherCouplingBoundary)
    (q : SU7MotherUnifiedConfiguration) : ℝ :=
  sourceRelativeMasterAction source q.gravity +
      dynamicStandardModelGaugeAction source q.gravity.tetrad
        (generatedStageFiveBoundary boundary)
        (projectMotherGaugeConfiguration q.gauge) +
    motherBreakingPenalty q.gauge

theorem motherMasterAction_restricts_exactly_to_stageFive
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    motherMasterAction source (motherBoundaryOfStageFive boundary)
        (liftStageFiveUnifiedConfiguration q) =
      nonseparableMasterAction source boundary q := by
  simp [motherMasterAction, nonseparableMasterAction,
    liftStageFiveUnifiedConfiguration]


end
end SaturationMonoid.PhysicsCore.SU7MotherGaugeAction
