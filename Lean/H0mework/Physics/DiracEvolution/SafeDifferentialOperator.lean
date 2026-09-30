import H0mework.Physics.Coframe.CoframeNativeConjugateMatterFrameAction
import H0mework.Physics.DualVariation.MatterVariation
import H0mework.Physics.DualVariation.RepairedMatterEquationReadout

/-!
# Cauchy-safe repaired Dirac operators

These operators reread a genuine primal/adjoint candidate pair in one common
holonomic actual.  They expose the exact mother-action zero fibers consumed by
a source/current-owned Cauchy compiler; they do not construct or accept a
solution field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterDifferentialOperator

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeConjugateMatterFrameAction
open StageNineCoframeNativeMatterFrameAction
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity

noncomputable section

set_option autoImplicit false

/-- Install a candidate matter section while retaining every other action
coefficient of the selected current. -/
def cauchySafeMatterCandidateActual
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  { current with matter := candidate }

/-- Install both independent Dirac fields into the same candidate actual. -/
def cauchySafeMatterDualCandidateActual
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (dualCandidate :
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  { current with
    matter := candidate
    conjugateMatter := dualCandidate }

@[simp] theorem cauchySafeMatterCandidateActual_coframe
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier) :
    (cauchySafeMatterCandidateActual current candidate).coframe =
      current.coframe :=
  rfl

/-- The repaired mother-action Dirac vector on a genuine candidate section.
Its kinetic jet, repaired right-chiral Yukawa term, and point value are all
reread from that candidate. -/
def cauchySafeMatterDifferentialOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  generatedContinuumDiracDualMatterVector source 0 point
    (toContinuumPointField
      (cauchySafeMatterCandidateActual current candidate) point)

/-- The branch-free repaired temporal derivative generated after rereading
the same candidate section. -/
def cauchySafeMatterCandidateVelocity
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    (cauchySafeMatterCandidateActual current candidate) point

theorem cauchySafeMatterDifferentialOperator_eq_zero_iff_actionLaw
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint) :
    cauchySafeMatterDifferentialOperator source current candidate point = 0 ↔
      HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
        (cauchySafeMatterCandidateActual current candidate) point
        (holonomicMatterCovariantDerivative
          (cauchySafeMatterCandidateActual current candidate) point 0) := by
  unfold cauchySafeMatterDifferentialOperator
  exact
    (holonomicDiracDualCurrentCoframeMatterTimeActionLaw_iff_generatedContinuumDiracDualMatterVector_zero
      source (cauchySafeMatterCandidateActual current candidate) point).symm

/-- Exact primal normal form consumed by a Cauchy compiler. -/
theorem cauchySafeMatterDifferentialOperator_eq_zero_iff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    cauchySafeMatterDifferentialOperator source current candidate point = 0 ↔
      holonomicMatterCovariantDerivative
          (cauchySafeMatterCandidateActual current candidate) point 0 =
        cauchySafeMatterCandidateVelocity current candidate point := by
  let actual := cauchySafeMatterCandidateActual current candidate
  have actualNoncharacteristic :
      coframeTemporalPrincipalScalar (actual.coframe point) ≠ 0 := by
    change coframeTemporalPrincipalScalar (current.coframe point) ≠ 0
    exact noncharacteristic
  constructor
  · intro zero
    have actualLaw :
        HolonomicDiracDualCurrentCoframeMatterTimeActionLaw actual point
          (holonomicMatterCovariantDerivative actual point 0) :=
      (cauchySafeMatterDifferentialOperator_eq_zero_iff_actionLaw
        source current candidate point).1 zero
    exact holonomicDiracDualCurrentCoframeMatterTimeActionLaw_unique actual point
      actualNoncharacteristic _ _ actualLaw
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
        actual point actualNoncharacteristic)
  · intro derivativeEq
    apply
      (cauchySafeMatterDifferentialOperator_eq_zero_iff_actionLaw
        source current candidate point).2
    rw [derivativeEq]
    exact
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
        actual point actualNoncharacteristic

/-! ## Real linearity of the fixed-current primal operator -/

/-- The candidate covariant derivative preserves addition at every point
where both candidate coordinate fields are differentiable. -/
theorem cauchySafeMatterCandidate_covariantDerivative_add
    (current : StageNineHolonomicConfiguration)
    (first second : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint)
    (firstDifferentiable :
      DifferentiableAt ℝ
        (fun candidate ↦ matterCoordinateEquiv (first candidate)) point)
    (secondDifferentiable :
      DifferentiableAt ℝ
        (fun candidate ↦ matterCoordinateEquiv (second candidate)) point)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (cauchySafeMatterCandidateActual current (first + second)) point
          direction =
      holonomicMatterCovariantDerivative
          (cauchySafeMatterCandidateActual current first) point direction +
        holonomicMatterCovariantDerivative
          (cauchySafeMatterCandidateActual current second) point direction := by
  have derivativeAdd :
      fieldDirectionalDerivative
          (fun candidate ↦ matterCoordinateEquiv ((first + second) candidate))
          point direction =
        fieldDirectionalDerivative
            (fun candidate ↦ matterCoordinateEquiv (first candidate))
            point direction +
          fieldDirectionalDerivative
            (fun candidate ↦ matterCoordinateEquiv (second candidate))
            point direction := by
    unfold fieldDirectionalDerivative
    have fieldEq :
        (fun candidate ↦ matterCoordinateEquiv ((first + second) candidate)) =
          (fun candidate ↦ matterCoordinateEquiv (first candidate)) +
            (fun candidate ↦ matterCoordinateEquiv (second candidate)) := by
      funext candidate
      exact matterCoordinateEquiv.map_add _ _
    rw [fieldEq, fderiv_add firstDifferentiable secondDifferentiable]
    rfl
  apply matterCoordinateEquiv.injective
  unfold holonomicMatterCovariantDerivative
    cauchySafeMatterCandidateActual
  simp only
  rw [derivativeAdd]
  simp only [Pi.add_apply, map_add, matterCoordinateEquiv.map_add]
  module

/-- At a fixed current and point, the mother-action Dirac operator preserves
addition of differentiable candidate sections. -/
theorem cauchySafeMatterDifferentialOperator_add
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (first second : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint)
    (firstDifferentiable :
      DifferentiableAt ℝ
        (fun candidate ↦ matterCoordinateEquiv (first candidate)) point)
    (secondDifferentiable :
      DifferentiableAt ℝ
        (fun candidate ↦ matterCoordinateEquiv (second candidate)) point) :
    cauchySafeMatterDifferentialOperator source current (first + second)
        point =
      cauchySafeMatterDifferentialOperator source current first point +
        cauchySafeMatterDifferentialOperator source current second point := by
  unfold cauchySafeMatterDifferentialOperator
  rw [show
      toContinuumPointField
          (cauchySafeMatterCandidateActual current (first + second)) point =
        withMatterJets
          (toContinuumPointField
            (cauchySafeMatterCandidateActual current first) point)
          ((toContinuumPointField
              (cauchySafeMatterCandidateActual current first) point).matter +
            (1 : ℝ) •
              (cauchySafeMatterCandidateActual current second).matter point)
          ((toContinuumPointField
              (cauchySafeMatterCandidateActual current first) point
              ).matterCovariantDerivative +
            (1 : ℝ) • fun direction ↦
              holonomicMatterCovariantDerivative
                (cauchySafeMatterCandidateActual current second) point
                direction) by
    apply StageNineContinuumPointField.ext <;> try rfl
    · simp [withMatterJets, toContinuumPointField,
        cauchySafeMatterCandidateActual]
      module
    · funext direction
      change
        holonomicMatterCovariantDerivative
            (cauchySafeMatterCandidateActual current (first + second)) point
              direction =
          holonomicMatterCovariantDerivative
              (cauchySafeMatterCandidateActual current first) point direction +
            (1 : ℝ) • holonomicMatterCovariantDerivative
              (cauchySafeMatterCandidateActual current second) point direction
      convert
        cauchySafeMatterCandidate_covariantDerivative_add current first second
          point firstDifferentiable secondDifferentiable direction using 1
      all_goals module]
  have affine :=
    generatedContinuumDiracDualMatterVector_withMatterJets_affine
      source point
      (toContinuumPointField
        (cauchySafeMatterCandidateActual current first) point)
      ((cauchySafeMatterCandidateActual current second).matter point)
      (fun direction ↦
        holonomicMatterCovariantDerivative
          (cauchySafeMatterCandidateActual current second) point direction)
      1
  have variationEq :
      diracDualMatterFieldVariationVector source point
          (toContinuumPointField
            (cauchySafeMatterCandidateActual current first) point)
          ((cauchySafeMatterCandidateActual current second).matter point)
          (fun direction ↦
            holonomicMatterCovariantDerivative
              (cauchySafeMatterCandidateActual current second) point
              direction) =
        generatedContinuumDiracDualMatterVector source 0 point
          (toContinuumPointField
            (cauchySafeMatterCandidateActual current second) point) := by
    unfold diracDualMatterFieldVariationVector
      generatedContinuumDiracDualMatterVector
      generatedContinuumMatterKineticVector
      generatedContinuumDiracDualYukawaVector
      matterCovariantDerivativeVariationVector
      matterCovariantDerivativeKineticSum
    simp [toContinuumPointField, cauchySafeMatterCandidateActual]
  apply affine.trans
  rw [variationEq]
  module

/-- The candidate covariant derivative commutes with real scalar
multiplication at every differentiability point. -/
theorem cauchySafeMatterCandidate_covariantDerivative_real_smul
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (parameter : ℝ)
    (point : BasePoint)
    (candidateDifferentiable :
      DifferentiableAt ℝ
        (fun position ↦ matterCoordinateEquiv (candidate position)) point)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (cauchySafeMatterCandidateActual current (parameter • candidate))
          point direction =
      parameter • holonomicMatterCovariantDerivative
        (cauchySafeMatterCandidateActual current candidate) point direction := by
  have derivativeSmul :
      fieldDirectionalDerivative
          (fun position ↦
            matterCoordinateEquiv ((parameter • candidate) position))
          point direction =
        parameter • fieldDirectionalDerivative
          (fun position ↦ matterCoordinateEquiv (candidate position))
          point direction := by
    unfold fieldDirectionalDerivative
    have fieldEq :
        (fun position ↦
          matterCoordinateEquiv ((parameter • candidate) position)) =
        parameter •
          (fun position ↦ matterCoordinateEquiv (candidate position)) := by
      funext position
      exact matterCoordinateEquiv.map_smul parameter (candidate position)
    rw [fieldEq, fderiv_const_smul candidateDifferentiable parameter]
    rfl
  unfold holonomicMatterCovariantDerivative
    cauchySafeMatterCandidateActual
  rw [derivativeSmul]
  simp only [Pi.smul_apply, matterCoordinateEquiv_symm_real_smul,
    diracMatrixMatterAction_real_smul,
    diracExteriorMotherLieAction_matter_real_smul]
  module

private theorem matterCovariantDerivativeVariationVector_congr_coframe
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (first second : StageNineContinuumPointField)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier)
    (coframeEq : first.coframe = second.coframe) :
    matterCovariantDerivativeVariationVector source 0 point first variation =
      matterCovariantDerivativeVariationVector source 0 point second
        variation := by
  unfold matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  rw [coframeEq]

/-- At a fixed current and point, the mother-action Dirac operator commutes
with real scalar multiplication of a differentiable candidate section. -/
theorem cauchySafeMatterDifferentialOperator_real_smul
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (parameter : ℝ)
    (point : BasePoint)
    (candidateDifferentiable :
      DifferentiableAt ℝ
        (fun position ↦ matterCoordinateEquiv (candidate position)) point) :
    cauchySafeMatterDifferentialOperator source current
        (parameter • candidate) point =
      parameter •
        cauchySafeMatterDifferentialOperator source current candidate point := by
  have covariantDerivativeSmul :
      holonomicMatterCovariantDerivative
          (cauchySafeMatterCandidateActual current (parameter • candidate))
          point =
        parameter • holonomicMatterCovariantDerivative
          (cauchySafeMatterCandidateActual current candidate) point := by
    funext direction
    exact cauchySafeMatterCandidate_covariantDerivative_real_smul current
      candidate parameter point candidateDifferentiable direction
  let scaledField :=
    toContinuumPointField
      (cauchySafeMatterCandidateActual current (parameter • candidate)) point
  let candidateField :=
    toContinuumPointField
      (cauchySafeMatterCandidateActual current candidate) point
  have fieldCoframeEq : scaledField.coframe = candidateField.coframe := rfl
  have fieldDerivativeSmul :
      scaledField.matterCovariantDerivative =
        parameter • candidateField.matterCovariantDerivative := by
    exact covariantDerivativeSmul
  have fieldMatterSmul :
      scaledField.matter = parameter • candidateField.matter := by
    rfl
  have fieldScalarEq : scaledField.scalar = candidateField.scalar := rfl
  have kineticSmul :
      matterCovariantDerivativeVariationVector source 0 point scaledField
          scaledField.matterCovariantDerivative =
        parameter • matterCovariantDerivativeVariationVector source 0 point
          candidateField candidateField.matterCovariantDerivative := by
    rw [fieldDerivativeSmul]
    rw [matterCovariantDerivativeVariationVector_congr_coframe source point
      scaledField candidateField _ fieldCoframeEq]
    exact matterCovariantDerivativeVariationVector_real_smul source point
      candidateField parameter candidateField.matterCovariantDerivative
  have yukawaSmul :
      generatedContinuumDiracDualYukawaVector source 0 point scaledField =
        parameter • generatedContinuumDiracDualYukawaVector source 0 point
          candidateField := by
    unfold generatedContinuumDiracDualYukawaVector
    simp only [scalarFrameRelativeCoordinates_zeroChart,
      matterFrameRelative_zeroChart]
    rw [fieldScalarEq, fieldMatterSmul,
      diracDualRightChiralYukawaAction_matter_real_smul]
  unfold cauchySafeMatterDifferentialOperator
    generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
  change
    matterCovariantDerivativeVariationVector source 0 point scaledField
          scaledField.matterCovariantDerivative +
        generatedContinuumDiracDualYukawaVector source 0 point scaledField =
      parameter •
        (matterCovariantDerivativeVariationVector source 0 point candidateField
            candidateField.matterCovariantDerivative +
          generatedContinuumDiracDualYukawaVector source 0 point
            candidateField)
  rw [kineticSmul, yukawaSmul]
  change
    (parameter : ℂ) •
          matterCovariantDerivativeVariationVector source 0 point
            candidateField candidateField.matterCovariantDerivative +
        (parameter : ℂ) •
          generatedContinuumDiracDualYukawaVector source 0 point
            candidateField =
      (parameter : ℂ) •
        (matterCovariantDerivativeVariationVector source 0 point
            candidateField candidateField.matterCovariantDerivative +
          generatedContinuumDiracDualYukawaVector source 0 point
            candidateField)
  exact (smul_add (parameter : ℂ) _ _).symm

/-! ## Independent adjoint equation on the same candidate actual -/

/-- The densitized frame-adjoint operator, including the full coframe/volume
drift, evaluated on the same primal/adjoint candidate pair. -/
def cauchySafeAdjointDifferentialOperator
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (dualCandidate :
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  let actual :=
    cauchySafeMatterDualCandidateActual current candidate dualCandidate
  ((generatedVolumeDensity (toContinuumPointField actual point) : ℂ) •
      (holonomicFrameConjugateMatterDerivative actual point 0).comp
        (identityCoframeMatterPrincipal
          canonicalLorentzianTimeDirection)) -
    holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
      actual point

/-- The branch-free adjoint velocity recomputed from the same candidate pair. -/
def cauchySafeAdjointCandidateVelocity
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (dualCandidate :
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity
    (cauchySafeMatterDualCandidateActual current candidate dualCandidate) point

theorem cauchySafeAdjointDifferentialOperator_eq_zero_iff_actionLaw
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (dualCandidate :
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) :
    cauchySafeAdjointDifferentialOperator current candidate dualCandidate
        point = 0 ↔
      HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
        (cauchySafeMatterDualCandidateActual current candidate dualCandidate)
        point
        (holonomicFrameConjugateMatterDerivative
          (cauchySafeMatterDualCandidateActual current candidate dualCandidate)
          point 0) := by
  unfold cauchySafeAdjointDifferentialOperator
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
  exact sub_eq_zero

/-- Exact independent-adjoint normal form consumed by the joint compiler. -/
theorem cauchySafeAdjointDifferentialOperator_eq_zero_iff
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (dualCandidate :
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    cauchySafeAdjointDifferentialOperator current candidate dualCandidate
        point = 0 ↔
      holonomicFrameConjugateMatterDerivative
          (cauchySafeMatterDualCandidateActual current candidate dualCandidate)
          point 0 =
        cauchySafeAdjointCandidateVelocity current candidate dualCandidate
          point := by
  let actual :=
    cauchySafeMatterDualCandidateActual current candidate dualCandidate
  have actualNondegenerate : Matrix.det (actual.coframe point) ≠ 0 := by
    change Matrix.det (current.coframe point) ≠ 0
    exact nondegenerate
  constructor
  · intro zero
    have actualLaw :
        HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
          actual point
          (holonomicFrameConjugateMatterDerivative actual point 0) :=
      (cauchySafeAdjointDifferentialOperator_eq_zero_iff_actionLaw
        current candidate dualCandidate point).1 zero
    exact
      holonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw_unique
        actual point actualNondegenerate _ _ actualLaw
        (holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity_satisfies
          actual point actualNondegenerate)
  · intro derivativeEq
    apply
      (cauchySafeAdjointDifferentialOperator_eq_zero_iff_actionLaw
        current candidate dualCandidate point).2
    rw [derivativeEq]
    exact
      holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity_satisfies
        actual point actualNondegenerate

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterDifferentialOperator
