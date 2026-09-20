import H0mework.Physics.Holonomic.GeneratedHolonomicChartAction

/-!
# Stage-9 generated-transition scalar first jet

The source-generated chart transition acts on the actual exterior-degree-four
scalar representation.  This module differentiates that finite action and
proves that the inhomogeneous P286 connection shift cancels its logarithmic
derivative, so the holonomic scalar covariant derivative transforms on the
same actual field.

This is a branch-free chart transporter.  It reads only the source, ordered
chart pair, and primitive holonomic field.  In particular it does not inspect
P286 current support, select an event branch, or claim a global source-time
evolution.  Any future discrete event adapter must remain downstream and
consume independently generated, source-owned event provenance.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceGeneratedHolonomicChartAction

open StageNineDynamicBreakingVacuum
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open GaugeProjection.ConcreteBlockDiagonal
open ProofFreeRicherAnholonomicSource
open scoped ContDiff

noncomputable section

local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

theorem scalarCoordinateAction_embeddedP286HyperchargeElement_basis
    (phase : Circle) (index : ScalarBasisIndex) :
    scalarCoordinateAction (embeddedP286HyperchargeElement phase)
        (EuclideanSpace.single index 1) =
      ((phase ^ exteriorHyperchargeWeight index : Circle) : ℂ) •
        EuclideanSpace.single index 1 := by
  let basisVector : ScalarCoordinateCarrier :=
    EuclideanSpace.single index 1
  have basisPreimage :
      scalarCoordinateEquiv.symm basisVector = su7ExteriorBasis 4 index := by
    apply (su7ExteriorBasis 4).repr.injective
    ext candidate
    simp [basisVector, scalarCoordinateEquiv]
  change
    scalarCoordinateAction (embeddedP286HyperchargeElement phase) basisVector =
      ((phase ^ exteriorHyperchargeWeight index : Circle) : ℂ) • basisVector
  unfold scalarCoordinateAction exteriorBreakingScalarRepresentation
  rw [basisPreimage]
  rw [p286Hypercharge_exterior_basis]
  rw [exteriorHyperchargeCharacter_eq_zpow]
  rw [map_smul]
  congr 1
  exact scalarCoordinateEquiv.apply_eq_iff_eq_symm_apply.mpr basisPreimage.symm

theorem scalarCoordinateAction_embeddedP286HyperchargeElement_apply
    (phase : Circle) (coordinates : ScalarCoordinateCarrier)
    (index : ScalarBasisIndex) :
    scalarCoordinateAction (embeddedP286HyperchargeElement phase) coordinates index =
      ((phase ^ exteriorHyperchargeWeight index : Circle) : ℂ) * coordinates index := by
  classical
  have expansion :
      (∑ candidate : ScalarBasisIndex,
          coordinates candidate • EuclideanSpace.single candidate 1) = coordinates := by
    ext candidate
    simp [Pi.single_apply]
  calc
    scalarCoordinateAction (embeddedP286HyperchargeElement phase) coordinates index =
        scalarCoordinateAction (embeddedP286HyperchargeElement phase)
          (∑ candidate : ScalarBasisIndex,
            coordinates candidate • EuclideanSpace.single candidate 1) index := by
              rw [expansion]
    _ = (∑ candidate : ScalarBasisIndex,
          coordinates candidate •
            scalarCoordinateAction (embeddedP286HyperchargeElement phase)
              (EuclideanSpace.single candidate 1)) index := by
            simp only [scalarCoordinateAction, map_sum, map_smul]
    _ = ((phase ^ exteriorHyperchargeWeight index : Circle) : ℂ) *
          coordinates index := by
            simp_rw [scalarCoordinateAction_embeddedP286HyperchargeElement_basis]
            simp [Pi.single_apply, mul_comm]

theorem fundamentalMotherLieAction_motherHyperchargeDirection_basis
    (index : SU7MotherIndex) :
    fundamentalMotherLieAction motherHyperchargeDirection
        (su7FundamentalBasis index) =
      (Complex.I * (fundamentalHyperchargeWeight index : ℂ)) •
        su7FundamentalBasis index := by
  funext row
  fin_cases index <;> fin_cases row <;>
    simp [fundamentalMotherLieAction, motherHyperchargeDirection,
      p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock, hyperchargeGenerator,
      su7FundamentalBasis, Matrix.mulVecLin, Matrix.mulVec,
      fundamentalHyperchargeWeight]

theorem exteriorMotherLieAction_basis_generatedTransition
    (degree : ℕ) (matrix : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) :
    exteriorMotherLieAction degree matrix (su7ExteriorBasis degree index) =
      exteriorBasisLieAction degree matrix index := by
  simp [exteriorMotherLieAction, Finsupp.single_apply]

theorem exteriorBasisInput_wedge_eq_basis_generatedTransition
    (degree : ℕ) (index : ExteriorBasisIndex degree) :
    (exteriorPower.ιMulti ℂ degree) (exteriorBasisInput degree index) =
      su7ExteriorBasis degree index := by
  rw [su7ExteriorBasis, exteriorPower.basis_apply]
  rfl

theorem exteriorPosition_sum_eq_subset_sum_complex_generatedTransition {degree : ℕ}
    (index : ExteriorBasisIndex degree) (value : SU7MotherIndex → ℂ) :
    (∑ position : Fin degree,
        value (exteriorPositionEquiv index position).1) =
      ∑ basisIndex ∈ index.1, value basisIndex := by
  calc
    _ = ∑ basisIndex : {basisIndex // basisIndex ∈ index.1},
          value basisIndex :=
      (exteriorPositionEquiv index).sum_comp
        (fun basisIndex => value basisIndex)
    _ = _ := (Finset.sum_subtype index.1 (by simp) value).symm

theorem exteriorBasisLieAction_motherHyperchargeDirection_basis
    (degree : ℕ) (index : ExteriorBasisIndex degree) :
    exteriorBasisLieAction degree motherHyperchargeDirection index =
      (Complex.I * (exteriorHyperchargeWeight index : ℂ)) •
        su7ExteriorBasis degree index := by
  unfold exteriorBasisLieAction
  calc
    _ = ∑ position : Fin degree,
          (Complex.I *
              (fundamentalHyperchargeWeight
                (exteriorPositionEquiv index position).1 : ℂ)) •
            su7ExteriorBasis degree index := by
      apply Finset.sum_congr rfl
      intro position _
      change
        (exteriorPower.ιMulti ℂ degree)
            (exteriorBasisLieActionInput degree
              motherHyperchargeDirection index position) = _
      rw [exteriorBasisLieActionTerm_eq_update]
      simp only [exteriorBasisInput]
      rw [fundamentalMotherLieAction_motherHyperchargeDirection_basis]
      rw [(exteriorPower.ιMulti ℂ degree).map_update_smul,
        show su7FundamentalBasis
              (exteriorPositionEquiv index position).1 =
            exteriorBasisInput degree index position by rfl,
        Function.update_eq_self,
        exteriorBasisInput_wedge_eq_basis_generatedTransition]
    _ = (Complex.I * (exteriorHyperchargeWeight index : ℂ)) •
          su7ExteriorBasis degree index := by
      rw [← Finset.sum_smul]
      have scalarSum :
          (∑ position : Fin degree,
              Complex.I *
                (fundamentalHyperchargeWeight
                  (exteriorPositionEquiv index position).1 : ℂ)) =
            Complex.I * (exteriorHyperchargeWeight index : ℂ) := by
        calc
          _ = ∑ basisIndex ∈ index.1,
                Complex.I *
                  (fundamentalHyperchargeWeight basisIndex : ℂ) :=
            exteriorPosition_sum_eq_subset_sum_complex_generatedTransition index
              (fun basisIndex =>
                Complex.I *
                  (fundamentalHyperchargeWeight basisIndex : ℂ))
          _ = _ := by
            simp only [exteriorHyperchargeWeight]
            push_cast
            rw [Finset.mul_sum]
      rw [scalarSum]

theorem scalarMotherLieAction_motherHyperchargeDirection_apply
    (coordinates : ScalarCoordinateCarrier) (index : ScalarBasisIndex) :
    scalarMotherLieAction motherHyperchargeDirection coordinates index =
      (Complex.I * (exteriorHyperchargeWeight index : ℂ)) *
        coordinates index := by
  classical
  have scalarMotherLieAction_basis : ∀ candidate : ScalarBasisIndex,
      scalarMotherLieAction motherHyperchargeDirection
          (EuclideanSpace.single candidate 1) =
        (Complex.I * (exteriorHyperchargeWeight candidate : ℂ)) •
          EuclideanSpace.single candidate 1 := by
    intro candidate
    let basisVector : ScalarCoordinateCarrier :=
      EuclideanSpace.single candidate 1
    have basisPreimage :
        scalarCoordinateEquiv.symm basisVector = su7ExteriorBasis 4 candidate := by
      apply (su7ExteriorBasis 4).repr.injective
      ext other
      simp [basisVector, scalarCoordinateEquiv]
    change
      scalarMotherLieAction motherHyperchargeDirection basisVector =
        (Complex.I * (exteriorHyperchargeWeight candidate : ℂ)) • basisVector
    unfold scalarMotherLieAction
    rw [basisPreimage]
    rw [exteriorMotherLieAction_basis_generatedTransition,
      exteriorBasisLieAction_motherHyperchargeDirection_basis]
    rw [map_smul]
    congr 1
    exact scalarCoordinateEquiv.apply_eq_iff_eq_symm_apply.mpr basisPreimage.symm
  let basisVector : ScalarCoordinateCarrier := EuclideanSpace.single index 1
  have basisPreimage :
      scalarCoordinateEquiv.symm basisVector = su7ExteriorBasis 4 index := by
    apply (su7ExteriorBasis 4).repr.injective
    ext candidate
    simp [basisVector, scalarCoordinateEquiv]
  have expansion :
      (∑ candidate : ScalarBasisIndex,
          coordinates candidate • EuclideanSpace.single candidate 1) = coordinates := by
    ext candidate
    simp [Pi.single_apply]
  calc
    scalarMotherLieAction motherHyperchargeDirection coordinates index =
        scalarMotherLieAction motherHyperchargeDirection
          (∑ candidate : ScalarBasisIndex,
            coordinates candidate • EuclideanSpace.single candidate 1) index := by
              rw [expansion]
    _ = (∑ candidate : ScalarBasisIndex,
          coordinates candidate •
            scalarMotherLieAction motherHyperchargeDirection
              (EuclideanSpace.single candidate 1)) index := by
            simp only [scalarMotherLieAction, map_sum, map_smul]
    _ = (Complex.I * (exteriorHyperchargeWeight index : ℂ)) *
          coordinates index := by
            simp_rw [scalarMotherLieAction_basis]
            simp [Pi.single_apply, mul_comm]

def baseCoordinateLinear
    (direction : LorentzianIndex) : BasePoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj direction).comp
    (EuclideanSpace.equiv LorentzianIndex ℝ).toContinuousLinearMap

@[simp] theorem baseCoordinateLinear_apply
    (direction : LorentzianIndex) (point : BasePoint) :
    baseCoordinateLinear direction point = point direction :=
  rfl

def generatedExteriorPhaseLinear
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (weight : ℤ) : BasePoint →L[ℝ] ℂ :=
  Complex.I •
    Complex.ofRealCLM.comp
      ((((weight : ℝ) *
          (chartWeight terminal - chartWeight initial) *
          source.continuousContactRate) •
        baseCoordinateLinear 0))

@[simp] theorem generatedExteriorPhaseLinear_apply
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (weight : ℤ) (point : BasePoint) :
    generatedExteriorPhaseLinear source initial terminal weight point =
      Complex.I *
        (((weight : ℝ) *
          (chartWeight terminal - chartWeight initial) *
          source.continuousContactRate * point 0 : ℝ) : ℂ) := by
  simp [generatedExteriorPhaseLinear, smul_eq_mul]

def generatedExteriorPhaseCoefficient
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (weight : ℤ) (point : BasePoint) : ℂ :=
  Complex.exp
    (generatedExteriorPhaseLinear source initial terminal weight point)

theorem generatedExteriorPhaseCoefficient_eq_character
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (weight : ℤ) (point : BasePoint) :
    generatedExteriorPhaseCoefficient source initial terminal weight point =
      (((Circle.exp
        ((chartWeight terminal - chartWeight initial) *
          source.continuousContactRate * point 0)) ^ weight : Circle) : ℂ) := by
  rw [← Circle.exp_intCast_mul]
  rw [Circle.coe_exp]
  simp only [generatedExteriorPhaseCoefficient,
    generatedExteriorPhaseLinear_apply]
  congr 1
  push_cast
  ring

theorem generatedExteriorPhaseCoefficient_hasFDerivAt
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (weight : ℤ) (point : BasePoint) :
    HasFDerivAt
        (generatedExteriorPhaseCoefficient source initial terminal weight)
        (((Complex.exp
            (generatedExteriorPhaseLinear source initial terminal weight point)) •
          (1 : ℂ →L[ℝ] ℂ)).comp
            (generatedExteriorPhaseLinear source initial terminal weight))
        point := by
  exact
    ((Complex.hasDerivAt_exp
      (generatedExteriorPhaseLinear source initial terminal weight point)).complexToReal_fderiv.comp
        point
        (generatedExteriorPhaseLinear source initial terminal weight).hasFDerivAt)

theorem fieldDirectionalDerivative_generatedExteriorPhaseCoefficient
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (weight : ℤ) (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (generatedExteriorPhaseCoefficient source initial terminal weight)
        point direction =
      (Complex.I * (weight : ℂ) *
          generatedTransitionDerivativeCoefficient
            source initial terminal direction) *
        generatedExteriorPhaseCoefficient source initial terminal weight point := by
  unfold fieldDirectionalDerivative
  rw [(generatedExteriorPhaseCoefficient_hasFDerivAt
    source initial terminal weight point).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    generatedExteriorPhaseCoefficient, generatedExteriorPhaseLinear_apply,
    coordinateDirection]
  by_cases directionZero : direction = 0
  · subst direction
    simp [generatedTransitionDerivativeCoefficient, smul_eq_mul]
    ring
  · simp [generatedTransitionDerivativeCoefficient, directionZero]

theorem generatedExteriorPhaseCoefficient_contDiff
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (weight : ℤ) :
    ContDiff ℝ ∞
      (generatedExteriorPhaseCoefficient source initial terminal weight) := by
  unfold generatedExteriorPhaseCoefficient
  fun_prop

theorem scalarCoordinateAction_generatedTransition_apply
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (coordinates : ScalarCoordinateCarrier)
    (index : ScalarBasisIndex) :
    scalarCoordinateAction
        (generatedTransition source initial terminal point) coordinates index =
      generatedExteriorPhaseCoefficient source initial terminal
          (exteriorHyperchargeWeight index) point * coordinates index := by
  unfold generatedTransition
  rw [scalarCoordinateAction_embeddedP286HyperchargeElement_apply]
  exact congrArg (fun coefficient : ℂ => coefficient * coordinates index)
    (generatedExteriorPhaseCoefficient_eq_character
      source initial terminal (exteriorHyperchargeWeight index) point).symm

theorem generatedTransition_scalarAction_contDiff
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (field : BasePoint → ScalarCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ fun point =>
      scalarCoordinateAction
        (generatedTransition source initial terminal point) (field point) := by
  rw [contDiff_piLp]
  intro index
  simp_rw [scalarCoordinateAction_generatedTransition_apply]
  exact
      (generatedExteriorPhaseCoefficient_contDiff source initial terminal
      (exteriorHyperchargeWeight index)).mul
      (((contDiff_piLp 2).mp fieldSmooth) index)

theorem fieldDirectionalDerivative_scalarCoordinateAction_generatedTransition
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (field : BasePoint → ScalarCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ ∞ field)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          scalarCoordinateAction
            (generatedTransition source initial terminal candidate)
            (field candidate))
        point direction =
      scalarCoordinateAction
          (generatedTransition source initial terminal point)
          (fieldDirectionalDerivative field point direction) +
        scalarMotherLieAction
          (generatedTransitionLogDerivative source initial terminal direction)
          (scalarCoordinateAction
            (generatedTransition source initial terminal point)
            (field point)) := by
  let transformed : BasePoint → ScalarCoordinateCarrier := fun candidate =>
    scalarCoordinateAction
      (generatedTransition source initial terminal candidate) (field candidate)
  have fieldDifferentiable : DifferentiableAt ℝ field point :=
    (fieldSmooth.differentiable (by simp)).differentiableAt
  have transformedSmooth : ContDiff ℝ ∞ transformed :=
    generatedTransition_scalarAction_contDiff
      source initial terminal field fieldSmooth
  have transformedDifferentiable : DifferentiableAt ℝ transformed point :=
    (transformedSmooth.differentiable (by simp)).differentiableAt
  unfold fieldDirectionalDerivative
  apply PiLp.ext
  intro index
  have transformedCoordinateDerivative :=
    ((PiLp.hasFDerivAt_apply (p := 2) (E := fun _ : ScalarBasisIndex => ℂ)
      (transformed point) index).comp point transformedDifferentiable.hasFDerivAt).fderiv
  have fieldCoordinateDerivative :=
    ((PiLp.hasFDerivAt_apply (p := 2) (E := fun _ : ScalarBasisIndex => ℂ)
      (field point) index).comp point fieldDifferentiable.hasFDerivAt).fderiv
  have coefficientDifferentiable : DifferentiableAt ℝ
      (generatedExteriorPhaseCoefficient source initial terminal
        (exteriorHyperchargeWeight index)) point :=
    ((generatedExteriorPhaseCoefficient_contDiff source initial terminal
      (exteriorHyperchargeWeight index)).differentiable (by simp)).differentiableAt
  have transformedCoordinateDerivativeApply :
      (fderiv ℝ transformed point (coordinateDirection direction)) index =
        fderiv ℝ (fun candidate => transformed candidate index) point
          (coordinateDirection direction) := by
    have equality := congrArg
      (fun derivative : BasePoint →L[ℝ] ℂ =>
        derivative (coordinateDirection direction))
      transformedCoordinateDerivative
    have functionEquality :
        ((fun value : ScalarCoordinateCarrier => value index) ∘ transformed) =
          (fun candidate => transformed candidate index) := by
      rfl
    rw [functionEquality] at equality
    simpa only [ContinuousLinearMap.comp_apply, PiLp.proj_apply] using equality.symm
  have fieldCoordinateDerivativeApply :
      fderiv ℝ (fun candidate => field candidate index) point
          (coordinateDirection direction) =
        (fderiv ℝ field point (coordinateDirection direction)) index := by
    have equality := congrArg
      (fun derivative : BasePoint →L[ℝ] ℂ =>
        derivative (coordinateDirection direction))
      fieldCoordinateDerivative
    have functionEquality :
        ((fun value : ScalarCoordinateCarrier => value index) ∘ field) =
          (fun candidate => field candidate index) := by
      rfl
    rw [functionEquality] at equality
    simpa only [ContinuousLinearMap.comp_apply, PiLp.proj_apply] using equality
  change
    (fderiv ℝ transformed point (coordinateDirection direction)) index = _
  rw [transformedCoordinateDerivativeApply]
  change
    fderiv ℝ
        (fun candidate =>
          scalarCoordinateAction
            (generatedTransition source initial terminal candidate)
            (field candidate) index)
        point (coordinateDirection direction) = _
  rw [show
      (fun candidate =>
        scalarCoordinateAction
          (generatedTransition source initial terminal candidate)
          (field candidate) index) =
        (fun candidate =>
          generatedExteriorPhaseCoefficient source initial terminal
              (exteriorHyperchargeWeight index) candidate *
            field candidate index) by
      funext candidate
      exact scalarCoordinateAction_generatedTransition_apply
        source initial terminal candidate (field candidate) index]
  have fieldCoordinateDifferentiable : DifferentiableAt ℝ
      (fun candidate => field candidate index) point :=
    ((((contDiff_piLp 2).mp fieldSmooth) index).differentiable
      (by simp)).differentiableAt
  rw [fderiv_fun_mul coefficientDifferentiable fieldCoordinateDifferentiable,
    add_apply, smul_apply, smul_apply]
  rw [show
      (fderiv ℝ
          (generatedExteriorPhaseCoefficient source initial terminal
            (exteriorHyperchargeWeight index)) point)
          (coordinateDirection direction) =
        fieldDirectionalDerivative
          (generatedExteriorPhaseCoefficient source initial terminal
            (exteriorHyperchargeWeight index)) point direction by rfl]
  rw [fieldDirectionalDerivative_generatedExteriorPhaseCoefficient]
  rw [fieldCoordinateDerivativeApply]
  simp only [PiLp.add_apply]
  rw [scalarCoordinateAction_generatedTransition_apply]
  rw [generatedTransitionLogDerivative]
  rw [scalarMotherLieAction_real_smul]
  simp only [PiLp.smul_apply, Complex.real_smul]
  rw [scalarMotherLieAction_motherHyperchargeDirection_apply]
  rw [scalarCoordinateAction_generatedTransition_apply]
  ring

theorem fundamentalMotherLieAction_embeddedHypercharge_commutes_p286
    (phase : Circle) (data : P286LieBlockData)
    (vector : SU7FundamentalCarrier) :
    su7FundamentalRepresentation (embeddedP286HyperchargeElement phase)
        (fundamentalMotherLieAction (p286LieBlockEmbed data) vector) =
      fundamentalMotherLieAction (p286LieBlockEmbed data)
        (su7FundamentalRepresentation
          (embeddedP286HyperchargeElement phase) vector) := by
  change
    Matrix.mulVec
        (embeddedP286HyperchargeElement phase :
          Matrix SU7MotherIndex SU7MotherIndex ℂ)
        (Matrix.mulVec
          (p286LieBlockEmbed data :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) vector) =
      Matrix.mulVec
        (p286LieBlockEmbed data :
          Matrix SU7MotherIndex SU7MotherIndex ℂ)
        (Matrix.mulVec
          (embeddedP286HyperchargeElement phase :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) vector)
  calc
    _ = Matrix.mulVec
          ((embeddedP286HyperchargeElement phase :
              Matrix SU7MotherIndex SU7MotherIndex ℂ) *
            (p286LieBlockEmbed data :
              Matrix SU7MotherIndex SU7MotherIndex ℂ)) vector :=
      Matrix.mulVec_mulVec
        (v := vector)
        (M := (embeddedP286HyperchargeElement phase :
          Matrix SU7MotherIndex SU7MotherIndex ℂ))
        (N := (p286LieBlockEmbed data :
          Matrix SU7MotherIndex SU7MotherIndex ℂ))
    _ = Matrix.mulVec
          ((p286LieBlockEmbed data :
              Matrix SU7MotherIndex SU7MotherIndex ℂ) *
            (embeddedP286HyperchargeElement phase :
              Matrix SU7MotherIndex SU7MotherIndex ℂ)) vector :=
      congrArg (fun matrix => Matrix.mulVec matrix vector)
        (_root_.SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.embeddedP286HyperchargeElement_commutes_p286LieBlockEmbed
          phase data).eq
    _ = _ := (Matrix.mulVec_mulVec
      (v := vector)
      (M := (p286LieBlockEmbed data :
        Matrix SU7MotherIndex SU7MotherIndex ℂ))
      (N := (embeddedP286HyperchargeElement phase :
        Matrix SU7MotherIndex SU7MotherIndex ℂ))).symm

theorem su7ExteriorPowerRepresentation_embeddedHypercharge_exteriorBasisLieAction
    (phase : Circle) (degree : ℕ) (data : P286LieBlockData)
    (index : ExteriorBasisIndex degree) :
    su7ExteriorPowerRepresentation degree
        (embeddedP286HyperchargeElement phase)
        (exteriorBasisLieAction degree (p286LieBlockEmbed data) index) =
      (exteriorHyperchargeCharacter phase index : ℂ) •
        exteriorBasisLieAction degree (p286LieBlockEmbed data) index := by
  unfold exteriorBasisLieAction
  rw [map_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro position _
  change
    exteriorPower.map degree
        (su7FundamentalRepresentation
          (embeddedP286HyperchargeElement phase))
        ((exteriorPower.ιMulti ℂ degree)
          (exteriorBasisLieActionInput degree
            (p286LieBlockEmbed data) index position)) =
      (exteriorHyperchargeCharacter phase index : ℂ) •
        (exteriorPower.ιMulti ℂ degree)
          (exteriorBasisLieActionInput degree
            (p286LieBlockEmbed data) index position)
  rw [exteriorPower.map_apply_ιMulti]
  have transformedInput :
      ((su7FundamentalRepresentation
          (embeddedP286HyperchargeElement phase)) ∘
        exteriorBasisLieActionInput degree
          (p286LieBlockEmbed data) index position) =
        (fun candidate =>
          (fundamentalHyperchargeCharacter phase
              (exteriorPositionEquiv index candidate).1 : ℂ) •
            exteriorBasisLieActionInput degree
              (p286LieBlockEmbed data) index position candidate) := by
    funext candidate
    by_cases candidatePosition : candidate = position
    · subst candidate
      simp only [Function.comp_apply, exteriorBasisLieActionInput,
        if_pos]
      rw [fundamentalMotherLieAction_embeddedHypercharge_commutes_p286]
      rw [p286Hypercharge_fundamental_basis]
      exact map_smul _ _ _
    · simp only [Function.comp_apply, exteriorBasisLieActionInput,
        candidatePosition, if_false]
      exact p286Hypercharge_fundamental_basis phase _
  rw [transformedInput, (exteriorPower.ιMulti ℂ degree).map_smul_univ]
  congr 1
  change
    (∏ candidate : Fin degree,
        Circle.coeHom
          (fundamentalHyperchargeCharacter phase
            (exteriorPositionEquiv index candidate).1)) =
      Circle.coeHom
        (∏ candidate : Fin degree,
          fundamentalHyperchargeCharacter phase
            (exteriorPositionEquiv index candidate).1)
  exact (map_prod Circle.coeHom
      (fun candidate : Fin degree =>
        fundamentalHyperchargeCharacter phase
          (exteriorPositionEquiv index candidate).1) Finset.univ).symm

theorem exteriorMotherLieAction_embeddedHypercharge_commutes_p286
    (phase : Circle) (degree : ℕ) (data : P286LieBlockData)
    (field : ⋀[ℂ]^degree SU7FundamentalCarrier) :
    exteriorMotherLieAction degree (p286LieBlockEmbed data)
        (su7ExteriorPowerRepresentation degree
          (embeddedP286HyperchargeElement phase) field) =
      su7ExteriorPowerRepresentation degree
        (embeddedP286HyperchargeElement phase)
        (exteriorMotherLieAction degree (p286LieBlockEmbed data) field) := by
  classical
  let basis := su7ExteriorBasis degree
  have expansion :
      (∑ index : ExteriorBasisIndex degree,
          basis.repr field index • basis index) = field :=
    basis.sum_repr field
  rw [← expansion]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro index _
  rw [p286Hypercharge_exterior_basis]
  rw [map_smul]
  rw [exteriorMotherLieAction_basis_generatedTransition]
  rw [su7ExteriorPowerRepresentation_embeddedHypercharge_exteriorBasisLieAction]

theorem scalarMotherLieAction_embeddedHypercharge_commutes_p286
    (phase : Circle) (data : P286LieBlockData)
    (coordinates : ScalarCoordinateCarrier) :
    scalarMotherLieAction (p286LieBlockEmbed data)
        (scalarCoordinateAction
          (embeddedP286HyperchargeElement phase) coordinates) =
      scalarCoordinateAction (embeddedP286HyperchargeElement phase)
        (scalarMotherLieAction (p286LieBlockEmbed data) coordinates) := by
  apply scalarCoordinateEquiv.symm.injective
  simp only [scalarMotherLieAction, scalarCoordinateAction,
    scalarCoordinateEquiv.symm_apply_apply]
  exact exteriorMotherLieAction_embeddedHypercharge_commutes_p286
    phase 4 data (scalarCoordinateEquiv.symm coordinates)

theorem scalarMotherLieAction_sub
    (first second : SU7MotherLieMatrix)
    (coordinates : ScalarCoordinateCarrier) :
    scalarMotherLieAction (first - second) coordinates =
      scalarMotherLieAction first coordinates -
        scalarMotherLieAction second coordinates := by
  calc
    scalarMotherLieAction (first - second) coordinates =
        scalarMotherLieAction (first + -second) coordinates := by
      rw [sub_eq_add_neg]
    _ = scalarMotherLieAction first coordinates +
          scalarMotherLieAction (-second) coordinates :=
      scalarMotherLieAction_add first (-second) coordinates
    _ = scalarMotherLieAction first coordinates -
          scalarMotherLieAction second coordinates := by
      rw [show -second = (-1 : ℝ) • second by
          apply Subtype.ext
          ext row column
          simp,
        scalarMotherLieAction_real_smul]
      rw [neg_one_smul]
      rfl

theorem holonomicScalarCovariantDerivative_sourceGeneratedHolonomicChartAction
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        (sourceGeneratedHolonomicChartAction source initial terminal
          configuration)
        point direction =
      scalarCoordinateAction
        (generatedTransition source initial terminal point)
        (holonomicScalarCovariantDerivative configuration point direction) := by
  rcases smooth with ⟨_, _, _, _, _, _, scalarSmooth, _, _⟩
  unfold holonomicScalarCovariantDerivative
  rw [show
      (sourceGeneratedHolonomicChartAction source initial terminal
        configuration).scalar =
        (fun candidate =>
          scalarCoordinateAction
            (generatedTransition source initial terminal candidate)
            (configuration.scalar candidate)) by rfl]
  simp only [sourceGeneratedHolonomicChartAction_gaugeConnection]
  rw [fieldDirectionalDerivative_scalarCoordinateAction_generatedTransition
    source initial terminal configuration.scalar scalarSmooth point direction]
  rw [p286LieBlockEmbed_sub]
  rw [p286LieBlockEmbed_generatedTransitionP286LogDerivative]
  rw [scalarMotherLieAction_sub]
  rw [show generatedTransition source initial terminal point =
      embeddedP286HyperchargeElement
        (Circle.exp
          ((chartWeight terminal - chartWeight initial) *
            source.continuousContactRate * point 0)) by rfl]
  rw [scalarMotherLieAction_embeddedHypercharge_commutes_p286]
  rw [scalarCoordinateAction_add]
  abel

end
end SaturationMonoid.PhysicsCore.StageNineSourceGeneratedHolonomicChartAction
