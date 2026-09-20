import H0mework.Physics.Coframe.CoframeFirstVariation

/-!
# S9-C3e2b: actual joint gravity/gauge coframe regularity

For a smooth primitive holonomic configuration, this module derives joint
regularity in the spacetime point and an arbitrary nondegenerate candidate
coframe for the Plebanski simplicity/BF block and all three gauge blocks.
Connection derivatives and curvatures are generated from the primitive
fields; no curvature, differentiability, or domination receipt is accepted.

The terminal theorem is deliberately local at every
`(point, candidateCoframe)` with nonzero determinant.  It is the gravity/gauge
input to the later common-density corridor and does not itself claim uniform
domination or differentiation under the spacetime integral.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCoframeVariation
open StageNineCoframeLocalDifferentiability
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open EmpiricalReferenceScaleCouplingBoundary
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option maxHeartbeats 1800000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Module.Free.ChooseBasisIndex.fintype ℝ P286LieBlockData

abbrev CoframeJoint := BasePoint × LorentzianCoframe

/-! ## Actual holonomic curvature regularity -/

theorem gravityConnectionDerivative_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      gravityConnectionDerivative configuration point derivativeDirection
        formDirection internalOut internalIn := by
  let connectionCoordinate : BasePoint → ℝ := fun point =>
    configuration.gravityConnection point formDirection internalOut internalIn
  have coordinateSmooth : ContDiff ℝ ∞ connectionCoordinate :=
    smooth.2.1 formDirection internalOut internalIn
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => connectionCoordinate)) := by
    exact coordinateSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ connectionCoordinate point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  unfold gravityConnectionDerivative
  change ContDiff ℝ ∞ fun point =>
    fderiv ℝ connectionCoordinate point
      (coordinateDirection derivativeDirection)
  exact derivativeSmooth.clm_apply contDiff_const

theorem holonomicGravityCurvature_component_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      holonomicGravityCurvature configuration point internal spacetime := by
  unfold holonomicGravityCurvature
  dsimp only
  apply contDiff_const.mul
  apply ContDiff.add
  · apply ContDiff.sub
    · exact gravityConnectionDerivative_contDiff configuration smooth
        (pairFirst spacetime) (pairSecond spacetime)
        (pairFirst internal) (pairSecond internal)
    · exact gravityConnectionDerivative_contDiff configuration smooth
        (pairSecond spacetime) (pairFirst spacetime)
        (pairFirst internal) (pairSecond internal)
  · apply ContDiff.sum
    intro middle _
    exact ((smooth.2.1 (pairFirst spacetime)
        (pairFirst internal) middle).mul
      (smooth.2.1 (pairSecond spacetime)
        middle (pairSecond internal))).sub
      ((smooth.2.1 (pairSecond spacetime)
        (pairFirst internal) middle).mul
      (smooth.2.1 (pairFirst spacetime)
        middle (pairSecond internal)))

/-- Local `C¹` connection components generate a continuous curvature
component.  This is the fixed-contact counterpart of
`holonomicGravityCurvature_component_contDiff`; it avoids upgrading a local
nondegenerate germ to a globally smooth connection. -/
theorem holonomicGravityCurvature_component_contDiffAt_of_connectionComponents
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (connectionRegular : ∀ direction internalOut internalIn,
      ContDiffAt ℝ 1
        (fun candidate =>
          configuration.gravityConnection candidate direction
            internalOut internalIn) point)
    (internal spacetime : Fin 6) :
    ContDiffAt ℝ 0
      (fun candidate =>
        holonomicGravityCurvature configuration candidate internal spacetime)
      point := by
  have derivativeRegular
      (derivativeDirection formDirection internalOut internalIn :
        LorentzianIndex) :
      ContDiffAt ℝ 0
        (fun candidate =>
          gravityConnectionDerivative configuration candidate
            derivativeDirection formDirection internalOut internalIn) point := by
    unfold gravityConnectionDerivative
    exact
      ((connectionRegular formDirection internalOut internalIn).fderiv_right
        (m := 0) (by norm_num)).clm_apply contDiffAt_const
  unfold holonomicGravityCurvature
  dsimp only
  refine contDiffAt_const.mul
    (((derivativeRegular (pairFirst spacetime) (pairSecond spacetime)
      (pairFirst internal) (pairSecond internal)).sub
      (derivativeRegular (pairSecond spacetime) (pairFirst spacetime)
        (pairFirst internal) (pairSecond internal))).add ?_)
  apply ContDiffAt.sum
  intro middle _
  exact
    (((connectionRegular (pairFirst spacetime)
      (pairFirst internal) middle).of_le (by norm_num)).mul
      ((connectionRegular (pairSecond spacetime)
        middle (pairSecond internal)).of_le (by norm_num))).sub
      (((connectionRegular (pairSecond spacetime)
        (pairFirst internal) middle).of_le (by norm_num)).mul
        ((connectionRegular (pairFirst spacetime)
          middle (pairSecond internal)).of_le (by norm_num)))

theorem suLieBracket_add_left_local
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    suLieBracket (first + second) residual =
      suLieBracket first residual + suLieBracket second residual := by
  apply Subtype.ext
  simp [suLieBracket, Matrix.add_mul, Matrix.mul_add]
  abel

theorem suLieBracket_add_right_local
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    suLieBracket residual (first + second) =
      suLieBracket residual first + suLieBracket residual second := by
  apply Subtype.ext
  simp [suLieBracket, Matrix.add_mul, Matrix.mul_add]
  abel

theorem suLieBracket_smul_left_local
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    suLieBracket (parameter • first) residual =
      parameter • suLieBracket first residual := by
  apply Subtype.ext
  simp [suLieBracket]
  rw [smul_sub]

theorem suLieBracket_smul_right_local
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    suLieBracket residual (parameter • first) =
      parameter • suLieBracket residual first := by
  apply Subtype.ext
  simp [suLieBracket]
  rw [smul_sub]

theorem p286LieBracket_add_left_local
    (first second residual : P286LieBlockData) :
    p286LieBracket (first + second) residual =
      p286LieBracket first residual + p286LieBracket second residual := by
  apply Prod.ext
  · exact suLieBracket_add_left_local first.1 second.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_add_left_local first.2.1 second.2.1 residual.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_add_right_local
    (first second residual : P286LieBlockData) :
    p286LieBracket residual (first + second) =
      p286LieBracket residual first + p286LieBracket residual second := by
  apply Prod.ext
  · exact suLieBracket_add_right_local first.1 second.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_add_right_local first.2.1 second.2.1 residual.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_smul_left_local
    (parameter : ℝ) (first residual : P286LieBlockData) :
    p286LieBracket (parameter • first) residual =
      parameter • p286LieBracket first residual := by
  apply Prod.ext
  · exact suLieBracket_smul_left_local parameter first.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_smul_left_local parameter first.2.1 residual.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_smul_right_local
    (parameter : ℝ) (first residual : P286LieBlockData) :
    p286LieBracket residual (parameter • first) =
      parameter • p286LieBracket residual first := by
  apply Prod.ext
  · exact suLieBracket_smul_right_local parameter first.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_smul_right_local parameter first.2.1 residual.2.1
    · simp [p286LieBracket]

def jointP286CoordinateLieBracket
    (first second : P286CoordinateCarrier) : P286CoordinateCarrier :=
  p286CoordinateEquiv
    (p286LieBracket (p286CoordinateEquiv.symm first)
      (p286CoordinateEquiv.symm second))

theorem jointP286CoordinateLieBracket_add_left
    (first second residual : P286CoordinateCarrier) :
    jointP286CoordinateLieBracket (first + second) residual =
      jointP286CoordinateLieBracket first residual +
        jointP286CoordinateLieBracket second residual := by
  unfold jointP286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm.map_add,
    p286LieBracket_add_left_local, map_add]

theorem jointP286CoordinateLieBracket_add_right
    (first second residual : P286CoordinateCarrier) :
    jointP286CoordinateLieBracket residual (first + second) =
      jointP286CoordinateLieBracket residual first +
        jointP286CoordinateLieBracket residual second := by
  unfold jointP286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm.map_add,
    p286LieBracket_add_right_local, map_add]

theorem jointP286CoordinateLieBracket_smul_left
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    jointP286CoordinateLieBracket (parameter • first) residual =
      parameter • jointP286CoordinateLieBracket first residual := by
  unfold jointP286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm.map_smul,
    p286LieBracket_smul_left_local, map_smul]

theorem jointP286CoordinateLieBracket_smul_right
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    jointP286CoordinateLieBracket residual (parameter • first) =
      parameter • jointP286CoordinateLieBracket residual first := by
  unfold jointP286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm.map_smul,
    p286LieBracket_smul_right_local, map_smul]

def jointP286CoordinateLieBracketBilinear :
    P286CoordinateCarrier →ₗ[ℝ]
      P286CoordinateCarrier →ₗ[ℝ] P286CoordinateCarrier where
  toFun first :=
    { toFun := fun second => jointP286CoordinateLieBracket first second
      map_add' := by
        intro second third
        exact jointP286CoordinateLieBracket_add_right second third first
      map_smul' := by
        intro parameter second
        exact jointP286CoordinateLieBracket_smul_right parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact jointP286CoordinateLieBracket_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    exact jointP286CoordinateLieBracket_smul_left parameter first residual

theorem jointP286CoordinateLieBracket_contDiff
    (first second : BasePoint → P286CoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second) :
    ContDiff ℝ ∞ fun point =>
      jointP286CoordinateLieBracket (first point) (second point) := by
  have outerSmooth : ContDiff ℝ ∞ fun point =>
      jointP286CoordinateLieBracketBilinear.toContinuousBilinearMap
        (first point) :=
    jointP286CoordinateLieBracketBilinear.toContinuousBilinearMap.contDiff.comp
      firstSmooth
  simpa [jointP286CoordinateLieBracketBilinear] using
    outerSmooth.clm_apply secondSmooth

theorem p286ConnectionDerivative_coordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (derivativeDirection formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        (p286ConnectionDerivative configuration point derivativeDirection
          formDirection) := by
  let connectionCoordinate : BasePoint → P286CoordinateCarrier := fun point =>
    p286CoordinateEquiv
      (configuration.gaugeConnection point formDirection)
  have coordinateSmooth : ContDiff ℝ ∞ connectionCoordinate :=
    smooth.2.2.2.2.1 formDirection
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => connectionCoordinate)) := by
    exact coordinateSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ connectionCoordinate point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  unfold p286ConnectionDerivative fieldDirectionalDerivative
  simp only [p286CoordinateEquiv.apply_symm_apply]
  exact derivativeSmooth.clm_apply contDiff_const

theorem holonomicGaugeCurvature_coordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        (holonomicGaugeCurvature configuration point pair) := by
  have firstDerivative := p286ConnectionDerivative_coordinate_contDiff
    configuration smooth (pairFirst pair) (pairSecond pair)
  have secondDerivative := p286ConnectionDerivative_coordinate_contDiff
    configuration smooth (pairSecond pair) (pairFirst pair)
  have firstConnection : ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        (configuration.gaugeConnection point (pairFirst pair)) :=
    smooth.2.2.2.2.1 (pairFirst pair)
  have secondConnection : ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        (configuration.gaugeConnection point (pairSecond pair)) :=
    smooth.2.2.2.2.1 (pairSecond pair)
  have bracketSmooth := jointP286CoordinateLieBracket_contDiff
    (fun point => p286CoordinateEquiv
      (configuration.gaugeConnection point (pairFirst pair)))
    (fun point => p286CoordinateEquiv
      (configuration.gaugeConnection point (pairSecond pair)))
    firstConnection secondConnection
  rw [show (fun point => p286CoordinateEquiv
      (holonomicGaugeCurvature configuration point pair)) =
    fun point =>
      p286CoordinateEquiv
          (p286ConnectionDerivative configuration point
            (pairFirst pair) (pairSecond pair)) -
        p286CoordinateEquiv
          (p286ConnectionDerivative configuration point
            (pairSecond pair) (pairFirst pair)) +
        jointP286CoordinateLieBracket
          (p286CoordinateEquiv
            (configuration.gaugeConnection point (pairFirst pair)))
          (p286CoordinateEquiv
            (configuration.gaugeConnection point (pairSecond pair))) by
      funext point
      simp [holonomicGaugeCurvature, jointP286CoordinateLieBracket]]
  exact firstDerivative.sub secondDerivative |>.add bracketSmooth

def p286StrongCoordinateProjection :
    P286CoordinateCarrier →ₗ[ℝ] SpecialUnitaryLieMatrix (Fin 3) where
  toFun coordinate := (p286CoordinateEquiv.symm coordinate).1
  map_add' := by simp
  map_smul' := by simp

def p286WeakCoordinateProjection :
    P286CoordinateCarrier →ₗ[ℝ] SpecialUnitaryLieMatrix (Fin 2) where
  toFun coordinate := (p286CoordinateEquiv.symm coordinate).2.1
  map_add' := by simp
  map_smul' := by simp

def p286HyperchargeValueCoordinateProjection :
    P286CoordinateCarrier →ₗ[ℝ] ℂ where
  toFun coordinate := (p286CoordinateEquiv.symm coordinate).2.2.1
  map_add' := by simp
  map_smul' := by simp

@[simp] theorem p286StrongCoordinateProjection_apply
    (data : P286LieBlockData) :
    p286StrongCoordinateProjection (p286CoordinateEquiv data) = data.1 := by
  simp [p286StrongCoordinateProjection]

@[simp] theorem p286WeakCoordinateProjection_apply
    (data : P286LieBlockData) :
    p286WeakCoordinateProjection (p286CoordinateEquiv data) = data.2.1 := by
  simp [p286WeakCoordinateProjection]

@[simp] theorem p286HyperchargeValueCoordinateProjection_apply
    (data : P286LieBlockData) :
    p286HyperchargeValueCoordinateProjection (p286CoordinateEquiv data) =
      data.2.2.1 := by
  simp [p286HyperchargeValueCoordinateProjection]

theorem holonomicStrongCurvature_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point pair =>
      (holonomicGaugeCurvature configuration point pair).1 := by
  apply contDiff_pi'
  intro pair
  have coordinateSmooth := holonomicGaugeCurvature_coordinate_contDiff
    configuration smooth pair
  rw [show (fun point =>
      (holonomicGaugeCurvature configuration point pair).1) =
    fun point => p286StrongCoordinateProjection
      (p286CoordinateEquiv
        (holonomicGaugeCurvature configuration point pair)) by
      funext point
      simp]
  exact p286StrongCoordinateProjection.toContinuousLinearMap.contDiff.comp
    coordinateSmooth

theorem holonomicWeakCurvature_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point pair =>
      (holonomicGaugeCurvature configuration point pair).2.1 := by
  apply contDiff_pi'
  intro pair
  have coordinateSmooth := holonomicGaugeCurvature_coordinate_contDiff
    configuration smooth pair
  rw [show (fun point =>
      (holonomicGaugeCurvature configuration point pair).2.1) =
    fun point => p286WeakCoordinateProjection
      (p286CoordinateEquiv
        (holonomicGaugeCurvature configuration point pair)) by
      funext point
      simp]
  exact p286WeakCoordinateProjection.toContinuousLinearMap.contDiff.comp
    coordinateSmooth

theorem holonomicHyperchargeCurvature_component_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (pair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      (holonomicGaugeCurvature configuration point pair).2.2.1 := by
  have coordinateSmooth := holonomicGaugeCurvature_coordinate_contDiff
    configuration smooth pair
  rw [show (fun point =>
      (holonomicGaugeCurvature configuration point pair).2.2.1) =
    fun point => p286HyperchargeValueCoordinateProjection
      (p286CoordinateEquiv
        (holonomicGaugeCurvature configuration point pair)) by
      funext point
      simp]
  exact
    p286HyperchargeValueCoordinateProjection.toContinuousLinearMap.contDiff.comp
      coordinateSmooth

theorem holonomicStrongAuxiliary_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point pair =>
      (configuration.gaugeAuxiliary point pair).1 := by
  apply contDiff_pi'
  intro pair
  rw [show (fun point => (configuration.gaugeAuxiliary point pair).1) =
    fun point => p286StrongCoordinateProjection
      (p286CoordinateEquiv (configuration.gaugeAuxiliary point pair)) by
      funext point
      simp]
  exact p286StrongCoordinateProjection.toContinuousLinearMap.contDiff.comp
    (smooth.2.2.2.2.2.1 pair)

theorem holonomicWeakAuxiliary_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point pair =>
      (configuration.gaugeAuxiliary point pair).2.1 := by
  apply contDiff_pi'
  intro pair
  rw [show (fun point => (configuration.gaugeAuxiliary point pair).2.1) =
    fun point => p286WeakCoordinateProjection
      (p286CoordinateEquiv (configuration.gaugeAuxiliary point pair)) by
      funext point
      simp]
  exact p286WeakCoordinateProjection.toContinuousLinearMap.contDiff.comp
    (smooth.2.2.2.2.2.1 pair)

theorem holonomicHyperchargeAuxiliary_component_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (pair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      (configuration.gaugeAuxiliary point pair).2.2.1 := by
  rw [show (fun point => (configuration.gaugeAuxiliary point pair).2.2.1) =
    fun point => p286HyperchargeValueCoordinateProjection
      (p286CoordinateEquiv (configuration.gaugeAuxiliary point pair)) by
      funext point
      simp]
  exact
    p286HyperchargeValueCoordinateProjection.toContinuousLinearMap.contDiff.comp
      (smooth.2.2.2.2.2.1 pair)

/-! ## Joint coframe operators -/

theorem gaugeTwoForm_coordinate_expansion
    (form : GaugeTwoForm) :
    form = ∑ input : Fin 6,
      form input • (fun candidate => if candidate = input then 1 else 0) := by
  funext output
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single output]
  · simp
  · intro input inputNe
    simp [inputNe.symm]

theorem jointCoframeTwoFormLinear_component_contDiffAt
    (center : CoframeJoint)
    (form : CoframeJoint → GaugeTwoForm)
    (formSmooth : ContDiffAt ℝ ∞ form center)
    (output : Fin 6) :
    ContDiffAt ℝ ∞ (fun joint =>
      coframeTwoFormLinear joint.2 (form joint) output) center := by
  change ContDiffAt ℝ ∞ (fun joint =>
    ∑ input : Fin 6,
      coframeWedge joint.2 output input * form joint input) center
  apply ContDiffAt.sum
  intro input _
  exact ((contDiff_pi.mp (contDiff_pi.mp coframeWedge_contDiff
      output) input).contDiffAt.comp center contDiffAt_snd).mul
    (contDiffAt_pi.mp formSmooth input)

theorem jointCoframeHodgeOperatorCoefficient_contDiffAt
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (output input : Fin 6) :
    ContDiffAt ℝ ∞ (fun joint =>
      gaugeOperatorCoefficient
        (coframeGaugeSpacetimeHodgeLinear joint.2) output input) center :=
  (coframeHodgeOperatorCoefficient_contDiffAt
      center.2 nondegenerate output input).comp center contDiffAt_snd

theorem jointGaugeSpacetimeHodge_component_contDiffAt
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (form : CoframeJoint → GaugeTwoForm)
    (formSmooth : ContDiffAt ℝ ∞ form center)
    (output : Fin 6) :
    ContDiffAt ℝ ∞ (fun joint =>
      coframeGaugeSpacetimeHodgeLinear joint.2 (form joint) output) center := by
  rw [show (fun joint =>
      coframeGaugeSpacetimeHodgeLinear joint.2 (form joint) output) =
    fun joint => ∑ input : Fin 6,
      gaugeOperatorCoefficient
          (coframeGaugeSpacetimeHodgeLinear joint.2) output input *
        form joint input by
      funext joint
      conv_lhs => rw [gaugeTwoForm_coordinate_expansion (form joint)]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, gaugeOperatorCoefficient]
      apply Finset.sum_congr rfl
      intro input _
      ring]
  apply ContDiffAt.sum
  intro input _
  exact (jointCoframeHodgeOperatorCoefficient_contDiffAt
      center nondegenerate output input).mul
    (contDiffAt_pi.mp formSmooth input)

theorem jointGravityCoframePairing_contDiffAt
    (center : CoframeJoint)
    (first second : CoframeJoint → PhysicalBivector)
    (firstSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => first joint internal spacetime) center)
    (secondSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => second joint internal spacetime) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      gravityCoframePairing joint.2 (first joint) (second joint)) center := by
  unfold gravityCoframePairing coframeTwoFormMetricPairing
  apply ContDiffAt.sum
  intro internal _
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro pair _
  exact ((contDiffAt_const.mul
      (jointCoframeTwoFormLinear_component_contDiffAt center
        (fun joint => first joint internal)
        (by
          apply contDiffAt_pi'
          intro spacetime
          exact firstSmooth internal spacetime)
        pair)).mul
      (jointCoframeTwoFormLinear_component_contDiffAt center
        (fun joint => second joint internal)
        (by
          apply contDiffAt_pi'
          intro spacetime
          exact secondSmooth internal spacetime)
        pair))

theorem jointGravitySpacetimeHodge_component_contDiffAt
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (bivector : CoframeJoint → PhysicalBivector)
    (bivectorSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => bivector joint internal spacetime) center)
    (internal spacetime : Fin 6) :
    ContDiffAt ℝ ∞ (fun joint =>
      gravitySpacetimeHodge joint.2 (bivector joint) internal spacetime)
      center := by
  exact jointGaugeSpacetimeHodge_component_contDiffAt center nondegenerate
    (fun joint => bivector joint internal)
    (by
      apply contDiffAt_pi'
      intro input
      exact bivectorSmooth internal input)
    spacetime

/-! ## Joint gravity sector -/

theorem generatedGravitySimplicityDensity_joint_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGravitySimplicityDensity
        (withCoframe (toContinuumPointField configuration joint.1) joint.2))
      center := by
  change ContDiffAt ℝ ∞ (fun joint =>
    gravitySimplicityMultiplierPairing
      (configuration.gravitySimplicityMultiplier joint.1)
      (configuration.gravityAuxiliary joint.1 -
        physicalIIPlusBivector joint.2)) center
  unfold gravitySimplicityMultiplierPairing
  apply ContDiffAt.sum
  intro internal _
  apply ContDiffAt.sum
  intro spacetime _
  have multiplierSmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      configuration.gravitySimplicityMultiplier joint.1 internal spacetime)
      center :=
    (smooth.2.2.2.1 internal spacetime).contDiffAt.comp
      center contDiffAt_fst
  have auxiliarySmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      configuration.gravityAuxiliary joint.1 internal spacetime) center :=
    (smooth.2.2.1 internal spacetime).contDiffAt.comp center contDiffAt_fst
  have simplicitySmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      physicalIIPlusBivector joint.2 internal spacetime) center :=
    (contDiff_pi.mp (contDiff_pi.mp physicalIIPlusBivector_contDiff
      internal) spacetime).contDiffAt.comp center contDiffAt_snd
  exact multiplierSmooth.mul ((auxiliarySmooth.sub simplicitySmooth).pow 2)

theorem holonomicGravityAuxiliary_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ configuration.gravityAuxiliary := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro spacetime
  exact smooth.2.2.1 internal spacetime

theorem holonomicGravityInternalDualAuxiliary_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point =>
      gravityInternalDualEquiv (configuration.gravityAuxiliary point) := by
  have actual :=
    gravityInternalDualLinear.toContinuousLinearMap.contDiff.comp
      (holonomicGravityAuxiliary_contDiff configuration smooth)
  change ContDiff ℝ ∞ fun point =>
    gravityInternalDualLinear (configuration.gravityAuxiliary point)
  rw [show (fun point =>
      gravityInternalDualLinear (configuration.gravityAuxiliary point)) =
    gravityInternalDualLinear.toContinuousLinearMap ∘
      configuration.gravityAuxiliary by
      funext point
      rfl]
  exact actual

theorem gravityCurvatureBFPairing_joint_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun joint =>
      gravityCoframePairing joint.2
        (configuration.gravityAuxiliary joint.1)
        (gravitySpacetimeHodge joint.2
          (holonomicGravityCurvature configuration joint.1))) center := by
  have auxiliarySmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        configuration.gravityAuxiliary joint.1 internal spacetime) center :=
    fun internal spacetime =>
      (smooth.2.2.1 internal spacetime).contDiffAt.comp
        center contDiffAt_fst
  have curvatureSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        holonomicGravityCurvature configuration joint.1 internal spacetime)
        center :=
    fun internal spacetime =>
      (holonomicGravityCurvature_component_contDiff configuration smooth
        internal spacetime).contDiffAt.comp center contDiffAt_fst
  have curvatureHodgeSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        gravitySpacetimeHodge joint.2
          (holonomicGravityCurvature configuration joint.1)
          internal spacetime) center :=
    fun internal spacetime =>
      jointGravitySpacetimeHodge_component_contDiffAt center nondegenerate
        (fun joint => holonomicGravityCurvature configuration joint.1)
        curvatureSmooth internal spacetime
  exact jointGravityCoframePairing_contDiffAt center
    (fun joint => configuration.gravityAuxiliary joint.1)
    (fun joint => gravitySpacetimeHodge joint.2
      (holonomicGravityCurvature configuration joint.1))
    auxiliarySmooth curvatureHodgeSmooth

theorem gravityConstitutiveBFPairing_joint_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun joint =>
      gravityCoframePairing joint.2
        (configuration.gravityAuxiliary joint.1)
        (gravitySpacetimeHodge joint.2
          (gravityInternalDualEquiv
            (configuration.gravityAuxiliary joint.1)))) center := by
  have auxiliarySmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        configuration.gravityAuxiliary joint.1 internal spacetime) center :=
    fun internal spacetime =>
      (smooth.2.2.1 internal spacetime).contDiffAt.comp
        center contDiffAt_fst
  have dualAuxiliarySmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        gravityInternalDualEquiv
          (configuration.gravityAuxiliary joint.1) internal spacetime) center :=
    fun internal spacetime =>
      (contDiff_pi.mp (contDiff_pi.mp
        (holonomicGravityInternalDualAuxiliary_contDiff configuration smooth)
        internal) spacetime).contDiffAt.comp center contDiffAt_fst
  have dualHodgeSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        gravitySpacetimeHodge joint.2
          (gravityInternalDualEquiv
            (configuration.gravityAuxiliary joint.1)) internal spacetime)
          center :=
    fun internal spacetime =>
      jointGravitySpacetimeHodge_component_contDiffAt center nondegenerate
        (fun joint => gravityInternalDualEquiv
          (configuration.gravityAuxiliary joint.1))
        dualAuxiliarySmooth internal spacetime
  exact jointGravityCoframePairing_contDiffAt center
    (fun joint => configuration.gravityAuxiliary joint.1)
    (fun joint => gravitySpacetimeHodge joint.2
      (gravityInternalDualEquiv
        (configuration.gravityAuxiliary joint.1)))
    auxiliarySmooth dualHodgeSmooth

theorem generatedGravityBFDensity_joint_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGravityBFDensity
        (withCoframe (toContinuumPointField configuration joint.1) joint.2))
      center := by
  have constitutiveScaled : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      (1 / 2 : ℝ) *
        gravityCoframePairing joint.2
          (configuration.gravityAuxiliary joint.1)
          (gravitySpacetimeHodge joint.2
            (gravityInternalDualEquiv
              (configuration.gravityAuxiliary joint.1)))) center :=
    contDiffAt_const.mul
      (gravityConstitutiveBFPairing_joint_contDiffAt
        configuration smooth center nondegenerate)
  have actual := (gravityCurvatureBFPairing_joint_contDiffAt
      configuration smooth center nondegenerate).sub constitutiveScaled
  simpa only [generatedGravityBFDensity, withCoframe,
    toContinuumPointField] using actual

/-! ## Joint gauge sector -/

def jointSpecialUnitaryLiePairingBilinear
    {n : Type*} [Fintype n] [DecidableEq n] :
    SpecialUnitaryLieMatrix n →ₗ[ℝ]
      SpecialUnitaryLieMatrix n →ₗ[ℝ] ℝ where
  toFun first :=
    { toFun := fun second => specialUnitaryLiePairing first second
      map_add' := by
        intro second third
        exact coframeSpecialUnitaryLiePairing_add_right second third first
      map_smul' := by
        intro parameter second
        exact coframeSpecialUnitaryLiePairing_smul_right
          parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact coframeSpecialUnitaryLiePairing_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    exact coframeSpecialUnitaryLiePairing_smul_left parameter first residual

def specialUnitaryEntryRealLinear
    {n : Type*} [Fintype n] [DecidableEq n]
    (row column : n) : SpecialUnitaryLieMatrix n →ₗ[ℝ] ℝ where
  toFun matrix := ((matrix : Matrix n n ℂ) row column).re
  map_add' := by
    intro first second
    simp
  map_smul' := by
    intro parameter matrix
    simp

@[simp] theorem specialUnitaryEntryRealLinear_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (row column : n) (matrix : SpecialUnitaryLieMatrix n) :
    specialUnitaryEntryRealLinear row column matrix =
      ((matrix : Matrix n n ℂ) row column).re :=
  rfl

def specialUnitaryEntryImagLinear
    {n : Type*} [Fintype n] [DecidableEq n]
    (row column : n) : SpecialUnitaryLieMatrix n →ₗ[ℝ] ℝ where
  toFun matrix := ((matrix : Matrix n n ℂ) row column).im
  map_add' := by
    intro first second
    simp
  map_smul' := by
    intro parameter matrix
    simp

@[simp] theorem specialUnitaryEntryImagLinear_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (row column : n) (matrix : SpecialUnitaryLieMatrix n) :
    specialUnitaryEntryImagLinear row column matrix =
      ((matrix : Matrix n n ℂ) row column).im :=
  rfl

theorem specialUnitaryLiePairing_joint_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (center : CoframeJoint)
    (first second : CoframeJoint → SpecialUnitaryLieMatrix n)
    (firstSmooth : ContDiffAt ℝ ∞ first center)
    (secondSmooth : ContDiffAt ℝ ∞ second center) :
    ContDiffAt ℝ ∞ (fun joint =>
      specialUnitaryLiePairing (first joint) (second joint)) center := by
  rw [show (fun joint =>
      specialUnitaryLiePairing (first joint) (second joint)) =
    fun joint => -∑ row : n, ∑ middle : n,
      (specialUnitaryEntryRealLinear row middle (first joint) *
          specialUnitaryEntryRealLinear middle row (second joint) -
        specialUnitaryEntryImagLinear row middle (first joint) *
          specialUnitaryEntryImagLinear middle row (second joint)) by
      funext joint
      simp [specialUnitaryLiePairing, Matrix.trace, Matrix.mul_apply,
        specialUnitaryEntryRealLinear, specialUnitaryEntryImagLinear,
        Complex.mul_re, Finset.sum_sub_distrib]
      rfl]
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro row _
  apply ContDiffAt.sum
  intro middle _
  have firstReal : ContDiffAt ℝ ∞ (fun joint =>
      specialUnitaryEntryRealLinear row middle (first joint)) center := by
    exact specialUnitaryEntryRealLinear row middle
      |>.toContinuousLinearMap.contDiff.contDiffAt.comp center firstSmooth
  have secondReal : ContDiffAt ℝ ∞ (fun joint =>
      specialUnitaryEntryRealLinear middle row (second joint)) center := by
    exact specialUnitaryEntryRealLinear middle row
      |>.toContinuousLinearMap.contDiff.contDiffAt.comp center secondSmooth
  have firstImag : ContDiffAt ℝ ∞ (fun joint =>
      specialUnitaryEntryImagLinear row middle (first joint)) center := by
    exact specialUnitaryEntryImagLinear row middle
      |>.toContinuousLinearMap.contDiff.contDiffAt.comp center firstSmooth
  have secondImag : ContDiffAt ℝ ∞ (fun joint =>
      specialUnitaryEntryImagLinear middle row (second joint)) center := by
    exact specialUnitaryEntryImagLinear middle row
      |>.toContinuousLinearMap.contDiff.contDiffAt.comp center secondSmooth
  exact (firstReal.mul secondReal).sub (firstImag.mul secondImag)

theorem hyperchargeLiePairing_joint_contDiffAt
    (center : CoframeJoint)
    (first second : CoframeJoint → HyperchargeLieScalar)
    (firstValueSmooth : ContDiffAt ℝ ∞
      (fun joint => (first joint).1) center)
    (secondValueSmooth : ContDiffAt ℝ ∞
      (fun joint => (second joint).1) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      hyperchargeLiePairing (first joint) (second joint)) center := by
  have firstReal : ContDiffAt ℝ ∞
      (fun joint => (first joint).1.re) center := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.contDiff.contDiffAt.comp center firstValueSmooth
  have secondReal : ContDiffAt ℝ ∞
      (fun joint => (second joint).1.re) center := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.contDiff.contDiffAt.comp center secondValueSmooth
  have firstImag : ContDiffAt ℝ ∞
      (fun joint => (first joint).1.im) center := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.contDiff.contDiffAt.comp center firstValueSmooth
  have secondImag : ContDiffAt ℝ ∞
      (fun joint => (second joint).1.im) center := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.contDiff.contDiffAt.comp center secondValueSmooth
  unfold hyperchargeLiePairing
  simp_rw [Complex.mul_re]
  exact ((firstReal.mul secondReal).sub (firstImag.mul secondImag)).neg

theorem jointCoframeGaugeOperatorCoefficient_contDiffAt
    (center : CoframeJoint) (output input : Fin 6) :
    ContDiffAt ℝ ∞ (fun joint =>
      gaugeOperatorCoefficient (coframeTwoFormLinear joint.2)
        output input) center :=
  (coframeGaugeOperatorCoefficient_contDiff output input).contDiffAt.comp
    center contDiffAt_snd

theorem jointScaledCoframeHodgeOperatorCoefficient_contDiffAt
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (coupling : ℝ) (output input : Fin 6) :
    ContDiffAt ℝ ∞ (fun joint =>
      gaugeOperatorCoefficient
        (coupling • coframeGaugeSpacetimeHodgeLinear joint.2)
        output input) center :=
  (scaledCoframeHodgeOperatorCoefficient_contDiffAt center.2
    nondegenerate coupling output input).comp center contDiffAt_snd

theorem specialUnitaryGaugeCurvaturePairing_joint_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (curvature auxiliary : CoframeJoint →
      Fin 6 → SpecialUnitaryLieMatrix n)
    (curvatureSmooth : ContDiffAt ℝ ∞ curvature center)
    (auxiliarySmooth : ContDiffAt ℝ ∞ auxiliary center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGaugeTwoFormMetricPairing
        (@specialUnitaryLiePairing n _ _) joint.2 (auxiliary joint)
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear joint.2)
          (curvature joint))) center := by
  unfold generatedGaugeTwoFormMetricPairing liftGaugeTwoFormOperator
  simp_rw [specialUnitaryLiePairing_sum_left,
    specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_left,
    coframeSpecialUnitaryLiePairing_smul_right]
  simp_rw [specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_right]
  apply ContDiffAt.sum
  intro pair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro auxiliaryInput _
  apply ContDiffAt.sum
  intro hodgeOutput _
  exact (jointCoframeGaugeOperatorCoefficient_contDiffAt
      center pair auxiliaryInput).mul
    ((jointCoframeGaugeOperatorCoefficient_contDiffAt
      center pair hodgeOutput).mul (by
        apply ContDiffAt.sum
        intro curvatureInput _
        exact (jointCoframeHodgeOperatorCoefficient_contDiffAt
          center nondegenerate hodgeOutput curvatureInput).mul
            (specialUnitaryLiePairing_joint_contDiffAt center
              (fun joint => auxiliary joint auxiliaryInput)
              (fun joint => curvature joint curvatureInput)
              (contDiffAt_pi.mp auxiliarySmooth auxiliaryInput)
              (contDiffAt_pi.mp curvatureSmooth curvatureInput))))

theorem specialUnitaryGaugeConstitutivePairing_joint_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (coupling : ℝ)
    (auxiliary : CoframeJoint → Fin 6 → SpecialUnitaryLieMatrix n)
    (auxiliarySmooth : ContDiffAt ℝ ∞ auxiliary center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGaugeTwoFormMetricPairing
        (@specialUnitaryLiePairing n _ _) joint.2 (auxiliary joint)
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear joint.2)
          (liftGaugeTwoFormOperator
            (coupling • coframeGaugeSpacetimeHodgeLinear joint.2)
            (auxiliary joint)))) center := by
  unfold generatedGaugeTwoFormMetricPairing liftGaugeTwoFormOperator
  simp_rw [specialUnitaryLiePairing_sum_left,
    specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_left,
    coframeSpecialUnitaryLiePairing_smul_right]
  simp_rw [specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_right]
  simp_rw [specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_right]
  apply ContDiffAt.sum
  intro pair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro firstAuxiliaryInput _
  apply ContDiffAt.sum
  intro coframeOutput _
  exact (jointCoframeGaugeOperatorCoefficient_contDiffAt
      center pair firstAuxiliaryInput).mul
    ((jointCoframeGaugeOperatorCoefficient_contDiffAt
      center pair coframeOutput).mul (by
        apply ContDiffAt.sum
        intro hodgeOutput _
        exact (jointCoframeHodgeOperatorCoefficient_contDiffAt
          center nondegenerate coframeOutput hodgeOutput).mul (by
            apply ContDiffAt.sum
            intro secondAuxiliaryInput _
            exact (jointScaledCoframeHodgeOperatorCoefficient_contDiffAt
              center nondegenerate coupling hodgeOutput
                secondAuxiliaryInput).mul
              (specialUnitaryLiePairing_joint_contDiffAt center
                (fun joint => auxiliary joint firstAuxiliaryInput)
                (fun joint => auxiliary joint secondAuxiliaryInput)
                (contDiffAt_pi.mp auxiliarySmooth firstAuxiliaryInput)
                (contDiffAt_pi.mp auxiliarySmooth
                  secondAuxiliaryInput)))))

theorem specialUnitaryGaugeSector_joint_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (coupling : ℝ)
    (curvature auxiliary : CoframeJoint →
      Fin 6 → SpecialUnitaryLieMatrix n)
    (curvatureSmooth : ContDiffAt ℝ ∞ curvature center)
    (auxiliarySmooth : ContDiffAt ℝ ∞ auxiliary center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing n _ _) joint.2
        (coframeGaugeSpacetimeHodgeLinear joint.2)
        (coupling • coframeGaugeSpacetimeHodgeLinear joint.2)
        (curvature joint) (auxiliary joint)) center := by
  unfold generatedGaugeSectorBFDensity
  exact (specialUnitaryGaugeCurvaturePairing_joint_contDiffAt
      center nondegenerate curvature auxiliary curvatureSmooth
        auxiliarySmooth).sub
    (contDiffAt_const.mul
      (specialUnitaryGaugeConstitutivePairing_joint_contDiffAt
        center nondegenerate coupling auxiliary auxiliarySmooth))

theorem hyperchargeGaugeCurvaturePairing_joint_contDiffAt
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (curvature auxiliary : CoframeJoint → Fin 6 → HyperchargeLieScalar)
    (curvatureValueSmooth : ∀ input : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (curvature joint input).1) center)
    (auxiliaryValueSmooth : ∀ input : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (auxiliary joint input).1) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGaugeTwoFormMetricPairing hyperchargeLiePairing joint.2
        (auxiliary joint)
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear joint.2)
          (curvature joint))) center := by
  unfold generatedGaugeTwoFormMetricPairing liftGaugeTwoFormOperator
  simp_rw [hyperchargeLiePairing_sum_left,
    hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_left,
    coframeHyperchargeLiePairing_smul_right]
  simp_rw [hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_right]
  apply ContDiffAt.sum
  intro pair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro auxiliaryInput _
  apply ContDiffAt.sum
  intro hodgeOutput _
  exact (jointCoframeGaugeOperatorCoefficient_contDiffAt
      center pair auxiliaryInput).mul
    ((jointCoframeGaugeOperatorCoefficient_contDiffAt
      center pair hodgeOutput).mul (by
        apply ContDiffAt.sum
        intro curvatureInput _
        exact (jointCoframeHodgeOperatorCoefficient_contDiffAt
          center nondegenerate hodgeOutput curvatureInput).mul
            (hyperchargeLiePairing_joint_contDiffAt center
              (fun joint => auxiliary joint auxiliaryInput)
              (fun joint => curvature joint curvatureInput)
              (auxiliaryValueSmooth auxiliaryInput)
              (curvatureValueSmooth curvatureInput))))

theorem hyperchargeGaugeConstitutivePairing_joint_contDiffAt
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (coupling : ℝ)
    (auxiliary : CoframeJoint → Fin 6 → HyperchargeLieScalar)
    (auxiliaryValueSmooth : ∀ input : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (auxiliary joint input).1) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGaugeTwoFormMetricPairing hyperchargeLiePairing joint.2
        (auxiliary joint)
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear joint.2)
          (liftGaugeTwoFormOperator
            (coupling • coframeGaugeSpacetimeHodgeLinear joint.2)
            (auxiliary joint)))) center := by
  unfold generatedGaugeTwoFormMetricPairing liftGaugeTwoFormOperator
  simp_rw [hyperchargeLiePairing_sum_left,
    hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_left,
    coframeHyperchargeLiePairing_smul_right]
  simp_rw [hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_right]
  simp_rw [hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_right]
  apply ContDiffAt.sum
  intro pair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro firstAuxiliaryInput _
  apply ContDiffAt.sum
  intro coframeOutput _
  exact (jointCoframeGaugeOperatorCoefficient_contDiffAt
      center pair firstAuxiliaryInput).mul
    ((jointCoframeGaugeOperatorCoefficient_contDiffAt
      center pair coframeOutput).mul (by
        apply ContDiffAt.sum
        intro hodgeOutput _
        exact (jointCoframeHodgeOperatorCoefficient_contDiffAt
          center nondegenerate coframeOutput hodgeOutput).mul (by
            apply ContDiffAt.sum
            intro secondAuxiliaryInput _
            exact (jointScaledCoframeHodgeOperatorCoefficient_contDiffAt
              center nondegenerate coupling hodgeOutput
                secondAuxiliaryInput).mul
              (hyperchargeLiePairing_joint_contDiffAt center
                (fun joint => auxiliary joint firstAuxiliaryInput)
                (fun joint => auxiliary joint secondAuxiliaryInput)
                (auxiliaryValueSmooth firstAuxiliaryInput)
                (auxiliaryValueSmooth secondAuxiliaryInput)))))

theorem hyperchargeGaugeSector_joint_contDiffAt
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (coupling : ℝ)
    (curvature auxiliary : CoframeJoint → Fin 6 → HyperchargeLieScalar)
    (curvatureValueSmooth : ∀ input : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (curvature joint input).1) center)
    (auxiliaryValueSmooth : ∀ input : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (auxiliary joint input).1) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGaugeSectorBFDensity hyperchargeLiePairing joint.2
        (coframeGaugeSpacetimeHodgeLinear joint.2)
        (coupling • coframeGaugeSpacetimeHodgeLinear joint.2)
        (curvature joint) (auxiliary joint)) center := by
  unfold generatedGaugeSectorBFDensity
  exact (hyperchargeGaugeCurvaturePairing_joint_contDiffAt center
      nondegenerate curvature auxiliary curvatureValueSmooth
        auxiliaryValueSmooth).sub
    (contDiffAt_const.mul
      (hyperchargeGaugeConstitutivePairing_joint_contDiffAt center
        nondegenerate coupling auxiliary auxiliaryValueSmooth))

theorem generatedStrongGaugeSector_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing (Fin 3) _ _) joint.2
        (coframeGaugeSpacetimeHodgeLinear joint.2)
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear joint.2)
        (fun pair =>
          (holonomicGaugeCurvature configuration joint.1 pair).1)
        (fun pair => (configuration.gaugeAuxiliary joint.1 pair).1)) center := by
  have curvatureSmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      fun pair => (holonomicGaugeCurvature configuration joint.1 pair).1)
      center := by
    exact ((holonomicStrongCurvature_contDiff configuration smooth).comp
      contDiff_fst).contDiffAt
  have auxiliarySmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      fun pair => (configuration.gaugeAuxiliary joint.1 pair).1) center := by
    exact ((holonomicStrongAuxiliary_contDiff configuration smooth).comp
      contDiff_fst).contDiffAt
  exact specialUnitaryGaugeSector_joint_contDiffAt center nondegenerate
    ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)
    (fun joint pair =>
      (holonomicGaugeCurvature configuration joint.1 pair).1)
    (fun joint pair => (configuration.gaugeAuxiliary joint.1 pair).1)
    curvatureSmooth auxiliarySmooth

theorem generatedWeakGaugeSector_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing (Fin 2) _ _) joint.2
        (coframeGaugeSpacetimeHodgeLinear joint.2)
        (((sourceGeneratedUnifiedCouplings source).weakCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear joint.2)
        (fun pair =>
          (holonomicGaugeCurvature configuration joint.1 pair).2.1)
        (fun pair => (configuration.gaugeAuxiliary joint.1 pair).2.1)) center := by
  have curvatureSmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      fun pair =>
        (holonomicGaugeCurvature configuration joint.1 pair).2.1) center := by
    exact ((holonomicWeakCurvature_contDiff configuration smooth).comp
      contDiff_fst).contDiffAt
  have auxiliarySmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      fun pair => (configuration.gaugeAuxiliary joint.1 pair).2.1) center := by
    exact ((holonomicWeakAuxiliary_contDiff configuration smooth).comp
      contDiff_fst).contDiffAt
  exact specialUnitaryGaugeSector_joint_contDiffAt center nondegenerate
    ((sourceGeneratedUnifiedCouplings source).weakCouplingSquared : ℝ)
    (fun joint pair =>
      (holonomicGaugeCurvature configuration joint.1 pair).2.1)
    (fun joint pair => (configuration.gaugeAuxiliary joint.1 pair).2.1)
    curvatureSmooth auxiliarySmooth

theorem generatedHyperchargeGaugeSector_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedGaugeSectorBFDensity hyperchargeLiePairing joint.2
        (coframeGaugeSpacetimeHodgeLinear joint.2)
        (((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared :
          ℝ) • coframeGaugeSpacetimeHodgeLinear joint.2)
        (fun pair =>
          (holonomicGaugeCurvature configuration joint.1 pair).2.2)
        (fun pair => (configuration.gaugeAuxiliary joint.1 pair).2.2)) center := by
  have curvatureValueSmooth : ∀ input : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        (holonomicGaugeCurvature configuration joint.1 input).2.2.1) center :=
    fun input =>
      (holonomicHyperchargeCurvature_component_contDiff configuration smooth
        input).contDiffAt.comp center contDiffAt_fst
  have auxiliaryValueSmooth : ∀ input : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        (configuration.gaugeAuxiliary joint.1 input).2.2.1) center :=
    fun input =>
      (holonomicHyperchargeAuxiliary_component_contDiff configuration smooth
        input).contDiffAt.comp center contDiffAt_fst
  exact hyperchargeGaugeSector_joint_contDiffAt center nondegenerate
    ((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ)
    (fun joint pair =>
      (holonomicGaugeCurvature configuration joint.1 pair).2.2)
    (fun joint pair => (configuration.gaugeAuxiliary joint.1 pair).2.2)
    curvatureValueSmooth auxiliaryValueSmooth

def holonomicGravitySimplicityDensityFamily
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  generatedGravitySimplicityDensity
    (withCoframe (toContinuumPointField configuration joint.1) joint.2)

def holonomicGravityBFDensityFamily
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  generatedGravityBFDensity
    (withCoframe (toContinuumPointField configuration joint.1) joint.2)

def holonomicStrongGaugeDensityFamily
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  generatedGaugeSectorBFDensity
    (@specialUnitaryLiePairing (Fin 3) _ _) joint.2
    (coframeGaugeSpacetimeHodgeLinear joint.2)
    (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
      coframeGaugeSpacetimeHodgeLinear joint.2)
    (fun pair => (holonomicGaugeCurvature configuration joint.1 pair).1)
    (fun pair => (configuration.gaugeAuxiliary joint.1 pair).1)

def holonomicWeakGaugeDensityFamily
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  generatedGaugeSectorBFDensity
    (@specialUnitaryLiePairing (Fin 2) _ _) joint.2
    (coframeGaugeSpacetimeHodgeLinear joint.2)
    (((sourceGeneratedUnifiedCouplings source).weakCouplingSquared : ℝ) •
      coframeGaugeSpacetimeHodgeLinear joint.2)
    (fun pair => (holonomicGaugeCurvature configuration joint.1 pair).2.1)
    (fun pair => (configuration.gaugeAuxiliary joint.1 pair).2.1)

def holonomicHyperchargeGaugeDensityFamily
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  generatedGaugeSectorBFDensity hyperchargeLiePairing joint.2
    (coframeGaugeSpacetimeHodgeLinear joint.2)
    (((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared :
      ℝ) • coframeGaugeSpacetimeHodgeLinear joint.2)
    (fun pair => (holonomicGaugeCurvature configuration joint.1 pair).2.2)
    (fun pair => (configuration.gaugeAuxiliary joint.1 pair).2.2)

theorem holonomicGravitySimplicityDensityFamily_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (center : CoframeJoint) :
    ContDiffAt ℝ ∞
      (holonomicGravitySimplicityDensityFamily configuration) center := by
  unfold holonomicGravitySimplicityDensityFamily
  exact generatedGravitySimplicityDensity_joint_contDiffAt
    configuration smooth center

theorem holonomicGravityBFDensityFamily_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞ (holonomicGravityBFDensityFamily configuration) center := by
  unfold holonomicGravityBFDensityFamily
  exact generatedGravityBFDensity_joint_contDiffAt
    configuration smooth center nondegenerate

theorem holonomicStrongGaugeDensityFamily_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞
      (holonomicStrongGaugeDensityFamily source configuration) center := by
  unfold holonomicStrongGaugeDensityFamily
  exact generatedStrongGaugeSector_joint_contDiffAt
    source configuration smooth center nondegenerate

theorem holonomicWeakGaugeDensityFamily_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞
      (holonomicWeakGaugeDensityFamily source configuration) center := by
  unfold holonomicWeakGaugeDensityFamily
  exact generatedWeakGaugeSector_joint_contDiffAt
    source configuration smooth center nondegenerate

theorem holonomicHyperchargeGaugeDensityFamily_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞
      (holonomicHyperchargeGaugeDensityFamily source configuration) center := by
  unfold holonomicHyperchargeGaugeDensityFamily
  exact generatedHyperchargeGaugeSector_joint_contDiffAt
    source configuration smooth center nondegenerate

def holonomicCoframeGravityGaugeDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  holonomicGravitySimplicityDensityFamily configuration joint +
    holonomicGravityBFDensityFamily configuration joint +
    holonomicStrongGaugeDensityFamily source configuration joint +
    holonomicWeakGaugeDensityFamily source configuration joint +
    holonomicHyperchargeGaugeDensityFamily source configuration joint

theorem holonomicCoframeGravityGaugeDensity_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (holonomicCoframeGravityGaugeDensity source configuration)
      (point, candidate) := by
  let center : CoframeJoint := (point, candidate)
  have jointInfinite : ContDiffAt ℝ ∞
      (holonomicCoframeGravityGaugeDensity source configuration) center := by
    unfold holonomicCoframeGravityGaugeDensity
    exact (((
      holonomicGravitySimplicityDensityFamily_contDiffAt
        configuration smooth center).add
      (holonomicGravityBFDensityFamily_contDiffAt
        configuration smooth center nondegenerate)).add
      (holonomicStrongGaugeDensityFamily_contDiffAt
        source configuration smooth center nondegenerate)).add
      (holonomicWeakGaugeDensityFamily_contDiffAt
        source configuration smooth center nondegenerate) |>.add
      (holonomicHyperchargeGaugeDensityFamily_contDiffAt
        source configuration smooth center nondegenerate)
  simpa only [center] using jointInfinite.of_le (by norm_num)

end


end SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity
