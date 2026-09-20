import H0mework.Physics.Coframe.CoframeFirstVariation

/-!
# S9-C3e2b: joint point--coframe regularity for scalar and matter sectors

This module derives the chart-zero scalar and matter regularity directly from
the primitive smooth holonomic configuration.  It deliberately imports only
the coframe first-variation mouth and does not consume any historical scalar,
matter, P286-variation, or pointwise-equation module.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeScalarMatterRegularity

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCoframeVariation
open StageNineCoframeLocalDifferentiability
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open scoped ContDiff Matrix.Norms.Elementwise TensorProduct

noncomputable section

set_option maxHeartbeats 2000000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

@[simp] theorem scalarFrameRelativeCoordinates_zeroChart_local
    (source : SmoothUnifiedSource) (point : BasePoint)
    (coordinates : ScalarCoordinateCarrier) :
    scalarFrameRelativeCoordinates source 0 point coordinates = coordinates := by
  unfold scalarFrameRelativeCoordinates generatedScalarFrame
  rw [generatedTransition_normalized]
  simpa only [inv_one] using scalarCoordinateAction_one coordinates

@[simp] theorem matterFrameRelative_zeroChart_local
    (source : SmoothUnifiedSource) (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) :
    matterFrameRelative source 0 point matter = matter := by
  unfold matterFrameRelative generatedScalarFrame
  rw [generatedTransition_normalized]
  have representationOne :
      diracExteriorMatterGaugeRepresentation 1 =
        (1 : Module.End ℂ DiracExteriorMatterCarrier) :=
    map_one diracExteriorMatterGaugeRepresentation
  rw [inv_one, representationOne]
  rfl

@[simp] theorem matterDualFrameRelative_zeroChart_local
    (source : SmoothUnifiedSource) (point : BasePoint)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualFrameRelative source 0 point dual = dual := by
  apply LinearMap.ext
  intro matter
  unfold matterDualFrameRelative generatedScalarFrame
  rw [generatedTransition_normalized]
  have representationOne :
      diracExteriorMatterGaugeRepresentation 1 =
        (1 : Module.End ℂ DiracExteriorMatterCarrier) :=
    map_one diracExteriorMatterGaugeRepresentation
  rw [representationOne]
  rfl

/-!
## Dependency-light coordinate bilinear bridges

The following laws are proved here from the actual exterior representation.
They avoid importing the historical connection-variation chain merely to
obtain analytic bilinear structure.
-/

theorem p286LieBlockEmbed_real_smul
    (parameter : ℝ) (data : P286LieBlockData) :
    p286LieBlockEmbed (parameter • data) =
      parameter • p286LieBlockEmbed data := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock]

theorem fundamentalMotherLieAction_add
    (first second : SU7MotherLieMatrix) :
    fundamentalMotherLieAction (first + second) =
      fundamentalMotherLieAction first + fundamentalMotherLieAction second := by
  apply LinearMap.ext
  intro vector
  funext row
  simp [fundamentalMotherLieAction, Matrix.mulVecLin, Matrix.mulVec]

theorem fundamentalMotherLieAction_real_smul
    (parameter : ℝ) (matrix : SU7MotherLieMatrix) :
    fundamentalMotherLieAction (parameter • matrix) =
      (parameter : ℂ) • fundamentalMotherLieAction matrix := by
  apply LinearMap.ext
  intro vector
  funext row
  simp [fundamentalMotherLieAction, Matrix.mulVecLin, Matrix.mulVec]

def exteriorBasisInput
    (degree : ℕ) (index : ExteriorBasisIndex degree) :
    Fin degree → SU7FundamentalCarrier :=
  fun position =>
    su7FundamentalBasis (exteriorPositionEquiv index position).1

def exteriorBasisLieActionInput
    (degree : ℕ) (matrix : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) (position : Fin degree) :
    Fin degree → SU7FundamentalCarrier :=
  fun candidate =>
    if candidate = position then
      fundamentalMotherLieAction matrix
        (su7FundamentalBasis (exteriorPositionEquiv index candidate).1)
    else
      su7FundamentalBasis (exteriorPositionEquiv index candidate).1

theorem exteriorBasisLieActionTerm_eq_update
    (degree : ℕ) (matrix : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) (position : Fin degree) :
    (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree matrix index position) =
      (exteriorPower.ιMulti ℂ degree)
        (Function.update (exteriorBasisInput degree index) position
          (fundamentalMotherLieAction matrix
            (exteriorBasisInput degree index position))) := by
  apply congrArg (exteriorPower.ιMulti ℂ degree)
  funext candidate
  by_cases equality : candidate = position
  · subst candidate
    simp [exteriorBasisLieActionInput, exteriorBasisInput]
  · simp [exteriorBasisLieActionInput, exteriorBasisInput, equality]

theorem exteriorBasisLieAction_add
    (degree : ℕ) (first second : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) :
    exteriorBasisLieAction degree (first + second) index =
      exteriorBasisLieAction degree first index +
        exteriorBasisLieAction degree second index := by
  unfold exteriorBasisLieAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro position _
  change
    (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree (first + second) index position) =
      (exteriorPower.ιMulti ℂ degree)
          (exteriorBasisLieActionInput degree first index position) +
        (exteriorPower.ιMulti ℂ degree)
          (exteriorBasisLieActionInput degree second index position)
  rw [exteriorBasisLieActionTerm_eq_update,
    exteriorBasisLieActionTerm_eq_update,
    exteriorBasisLieActionTerm_eq_update]
  rw [fundamentalMotherLieAction_add, LinearMap.add_apply]
  exact (exteriorPower.ιMulti ℂ degree).map_update_add
    (exteriorBasisInput degree index) position
    (fundamentalMotherLieAction first
      (exteriorBasisInput degree index position))
    (fundamentalMotherLieAction second
      (exteriorBasisInput degree index position))

theorem exteriorBasisLieAction_real_smul
    (degree : ℕ) (parameter : ℝ) (matrix : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) :
    exteriorBasisLieAction degree (parameter • matrix) index =
      (parameter : ℂ) • exteriorBasisLieAction degree matrix index := by
  unfold exteriorBasisLieAction
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro position _
  change
    (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree (parameter • matrix) index
          position) =
      (parameter : ℂ) •
        (exteriorPower.ιMulti ℂ degree)
          (exteriorBasisLieActionInput degree matrix index position)
  rw [exteriorBasisLieActionTerm_eq_update,
    exteriorBasisLieActionTerm_eq_update]
  rw [fundamentalMotherLieAction_real_smul, LinearMap.smul_apply]
  exact (exteriorPower.ιMulti ℂ degree).map_update_smul
    (exteriorBasisInput degree index) position (parameter : ℂ)
    (fundamentalMotherLieAction matrix
      (exteriorBasisInput degree index position))

theorem exteriorMotherLieAction_add
    (degree : ℕ) (first second : SU7MotherLieMatrix) :
    exteriorMotherLieAction degree (first + second) =
      exteriorMotherLieAction degree first +
        exteriorMotherLieAction degree second := by
  apply LinearMap.ext
  intro field
  unfold exteriorMotherLieAction
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    exteriorBasisLieAction_add, smul_add, Finset.sum_add_distrib]

theorem exteriorMotherLieAction_real_smul
    (degree : ℕ) (parameter : ℝ) (matrix : SU7MotherLieMatrix) :
    exteriorMotherLieAction degree (parameter • matrix) =
      (parameter : ℂ) • exteriorMotherLieAction degree matrix := by
  apply LinearMap.ext
  intro field
  unfold exteriorMotherLieAction
  simp only [LinearMap.coe_mk, AddHom.coe_mk,
    exteriorBasisLieAction_real_smul, LinearMap.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  module

theorem exteriorSpinorMotherLieAction_add
    (first second : SU7MotherLieMatrix) :
    exteriorSpinorMotherLieAction (first + second) =
      exteriorSpinorMotherLieAction first +
        exteriorSpinorMotherLieAction second := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  simp [exteriorSpinorMotherLieAction, exteriorMotherLieAction_add]

theorem exteriorSpinorMotherLieAction_real_smul
    (parameter : ℝ) (matrix : SU7MotherLieMatrix) :
    exteriorSpinorMotherLieAction (parameter • matrix) =
      (parameter : ℂ) • exteriorSpinorMotherLieAction matrix := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  simp [exteriorSpinorMotherLieAction, exteriorMotherLieAction_real_smul]

theorem diracExteriorMotherLieAction_add
    (first second : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction (first + second) =
      diracExteriorMotherLieAction first +
        diracExteriorMotherLieAction second := by
  apply LinearMap.ext
  intro matter
  funext spinIndex
  simp [diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction_add]

theorem diracExteriorMotherLieAction_real_smul
    (parameter : ℝ) (matrix : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction (parameter • matrix) =
      (parameter : ℂ) • diracExteriorMotherLieAction matrix := by
  apply LinearMap.ext
  intro matter
  funext spinIndex
  simp [diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction_real_smul]

theorem scalarMotherLieAction_add
    (first second : SU7MotherLieMatrix)
    (scalar : ScalarCoordinateCarrier) :
    scalarMotherLieAction (first + second) scalar =
      scalarMotherLieAction first scalar +
        scalarMotherLieAction second scalar := by
  unfold scalarMotherLieAction
  rw [exteriorMotherLieAction_add, LinearMap.add_apply, map_add]

theorem scalarMotherLieAction_real_smul
    (parameter : ℝ) (matrix : SU7MotherLieMatrix)
    (scalar : ScalarCoordinateCarrier) :
    scalarMotherLieAction (parameter • matrix) scalar =
      parameter • scalarMotherLieAction matrix scalar := by
  unfold scalarMotherLieAction
  rw [exteriorMotherLieAction_real_smul, LinearMap.smul_apply, map_smul]
  rfl

theorem scalarMotherLieAction_add_right
    (matrix : SU7MotherLieMatrix)
    (first second : ScalarCoordinateCarrier) :
    scalarMotherLieAction matrix (first + second) =
      scalarMotherLieAction matrix first +
        scalarMotherLieAction matrix second := by
  unfold scalarMotherLieAction
  simp only [map_add]

theorem scalarMotherLieAction_real_smul_right
    (matrix : SU7MotherLieMatrix) (parameter : ℝ)
    (scalar : ScalarCoordinateCarrier) :
    scalarMotherLieAction matrix (parameter • scalar) =
      parameter • scalarMotherLieAction matrix scalar := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  unfold scalarMotherLieAction
  simp only [map_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

theorem matterP286ActionCoordinate_add_right
    (matrix : P286CoordinateCarrier)
    (first second : MatterCoordinateCarrier) :
    matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
          (matterCoordinateEquiv.symm (first + second))) =
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
            (matterCoordinateEquiv.symm first)) +
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
            (matterCoordinateEquiv.symm second)) := by
  simp only [map_add]

theorem matterP286ActionCoordinate_real_smul_right
    (matrix : P286CoordinateCarrier) (parameter : ℝ)
    (matter : MatterCoordinateCarrier) :
    matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
          (matterCoordinateEquiv.symm (parameter • matter))) =
      parameter •
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
            (matterCoordinateEquiv.symm matter)) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [map_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

def scalarP286ActionBilinear :
    P286CoordinateCarrier →ₗ[ℝ]
      ScalarCoordinateCarrier →ₗ[ℝ] ScalarCoordinateCarrier where
  toFun matrix :=
    { toFun := fun scalar =>
        scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix)) scalar
      map_add' := by
        intro first second
        exact scalarMotherLieAction_add_right _ _ _
      map_smul' := by
        intro parameter scalar
        exact scalarMotherLieAction_real_smul_right _ _ _ }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro scalar
    change
      scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm (first + second)))
          scalar =
        scalarMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm first)) scalar +
          scalarMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm second)) scalar
    rw [p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
      scalarMotherLieAction_add]
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro scalar
    change
      scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm (parameter • matrix)))
          scalar =
        parameter • scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix)) scalar
    rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
      scalarMotherLieAction_real_smul]

def matterP286ActionCoordinateBilinear :
    P286CoordinateCarrier →ₗ[ℝ]
      MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun matrix :=
    { toFun := fun matter =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
            (matterCoordinateEquiv.symm matter))
      map_add' := by
        intro first second
        exact matterP286ActionCoordinate_add_right _ _ _
      map_smul' := by
        intro parameter matter
        exact matterP286ActionCoordinate_real_smul_right _ _ _ }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm (first + second)))
            (matterCoordinateEquiv.symm matter)) =
        matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed (p286CoordinateEquiv.symm first))
              (matterCoordinateEquiv.symm matter)) +
          matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed (p286CoordinateEquiv.symm second))
              (matterCoordinateEquiv.symm matter))
    rw [p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
      diracExteriorMotherLieAction_add]
    simp only [LinearMap.add_apply, map_add]
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm (parameter • matrix)))
            (matterCoordinateEquiv.symm matter)) =
        parameter •
          matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
              (matterCoordinateEquiv.symm matter))
    rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
      diracExteriorMotherLieAction_real_smul]
    simp only [LinearMap.smul_apply, map_smul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

theorem exteriorYukawaMassMap_add
    (first second : ExteriorBreakingScalarCarrier) :
    exteriorYukawaMassMap (first + second) =
      exteriorYukawaMassMap first + exteriorYukawaMassMap second := by
  apply LinearMap.ext
  intro matter
  change
    exteriorWedge 2 4 matter (first + second) =
      exteriorWedge 2 4 matter first + exteriorWedge 2 4 matter second
  exact map_add (exteriorWedge 2 4 matter) first second

theorem exteriorYukawaMassMap_smul
    (coefficient : ℂ) (scalar : ExteriorBreakingScalarCarrier) :
    exteriorYukawaMassMap (coefficient • scalar) =
      coefficient • exteriorYukawaMassMap scalar := by
  apply LinearMap.ext
  intro matter
  change
    exteriorWedge 2 4 matter (coefficient • scalar) =
      coefficient • exteriorWedge 2 4 matter scalar
  exact map_smul (exteriorWedge 2 4 matter) coefficient scalar

theorem exteriorYukawaInternalAction_add
    (first second : ExteriorBreakingScalarCarrier) :
    exteriorYukawaInternalAction (first + second) =
      exteriorYukawaInternalAction first +
        exteriorYukawaInternalAction second := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  apply Prod.ext
  · exact LinearMap.congr_fun (exteriorYukawaMassMap_add first second)
      degreeTwo
  · simp [exteriorYukawaInternalAction]

theorem exteriorYukawaInternalAction_smul
    (coefficient : ℂ) (scalar : ExteriorBreakingScalarCarrier) :
    exteriorYukawaInternalAction (coefficient • scalar) =
      coefficient • exteriorYukawaInternalAction scalar := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  apply Prod.ext
  · exact LinearMap.congr_fun
      (exteriorYukawaMassMap_smul coefficient scalar) degreeTwo
  · simp [exteriorYukawaInternalAction]

theorem diracExteriorYukawaInternalAction_add
    (first second : ExteriorBreakingScalarCarrier) :
    diracExteriorYukawaInternalAction (first + second) =
      diracExteriorYukawaInternalAction first +
        diracExteriorYukawaInternalAction second := by
  apply LinearMap.ext
  intro field
  funext spinIndex
  exact LinearMap.congr_fun (exteriorYukawaInternalAction_add first second)
    (field spinIndex)

theorem diracExteriorYukawaInternalAction_smul
    (coefficient : ℂ) (scalar : ExteriorBreakingScalarCarrier) :
    diracExteriorYukawaInternalAction (coefficient • scalar) =
      coefficient • diracExteriorYukawaInternalAction scalar := by
  apply LinearMap.ext
  intro field
  funext spinIndex
  exact LinearMap.congr_fun
    (exteriorYukawaInternalAction_smul coefficient scalar) (field spinIndex)

theorem chiralExteriorYukawaAction_add
    (first second : ExteriorBreakingScalarCarrier) :
    chiralExteriorYukawaAction (first + second) =
      chiralExteriorYukawaAction first +
        chiralExteriorYukawaAction second := by
  apply LinearMap.ext
  intro field
  change
    diracMatrixMatterAction leftChiralityProjector
        (diracMatrixMatterAction (diracGamma 0)
          (diracExteriorYukawaInternalAction (first + second)
            (diracMatrixMatterAction rightChiralityProjector field))) =
      diracMatrixMatterAction leftChiralityProjector
          (diracMatrixMatterAction (diracGamma 0)
            (diracExteriorYukawaInternalAction first
              (diracMatrixMatterAction rightChiralityProjector field))) +
        diracMatrixMatterAction leftChiralityProjector
          (diracMatrixMatterAction (diracGamma 0)
            (diracExteriorYukawaInternalAction second
              (diracMatrixMatterAction rightChiralityProjector field)))
  rw [LinearMap.congr_fun (diracExteriorYukawaInternalAction_add first second)]
  rw [LinearMap.add_apply, map_add, map_add]

theorem chiralExteriorYukawaAction_smul
    (coefficient : ℂ)
    (scalar : ExteriorBreakingScalarCarrier) :
    chiralExteriorYukawaAction (coefficient • scalar) =
      coefficient • chiralExteriorYukawaAction scalar := by
  apply LinearMap.ext
  intro field
  change
    diracMatrixMatterAction leftChiralityProjector
        (diracMatrixMatterAction (diracGamma 0)
          (diracExteriorYukawaInternalAction (coefficient • scalar)
            (diracMatrixMatterAction rightChiralityProjector field))) =
      coefficient •
        diracMatrixMatterAction leftChiralityProjector
          (diracMatrixMatterAction (diracGamma 0)
            (diracExteriorYukawaInternalAction scalar
              (diracMatrixMatterAction rightChiralityProjector field)))
  rw [LinearMap.congr_fun
    (diracExteriorYukawaInternalAction_smul coefficient scalar)]
  rw [LinearMap.smul_apply, map_smul, map_smul]

theorem chiralExteriorYukawaCoordinate_add_right
    (scalar : ScalarCoordinateCarrier)
    (first second : MatterCoordinateCarrier) :
    matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm scalar)
          (matterCoordinateEquiv.symm (first + second))) =
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm first)) +
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm second)) := by
  simp only [map_add]

theorem chiralExteriorYukawaCoordinate_real_smul_right
    (scalar : ScalarCoordinateCarrier) (parameter : ℝ)
    (matter : MatterCoordinateCarrier) :
    matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm scalar)
          (matterCoordinateEquiv.symm (parameter • matter))) =
      parameter •
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter)) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [map_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

def chiralExteriorYukawaCoordinateRealBilinear :
    ScalarCoordinateCarrier →ₗ[ℝ]
      MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun scalar :=
    { toFun := fun matter =>
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter))
      map_add' := by
        intro first second
        exact chiralExteriorYukawaCoordinate_add_right scalar first second
      map_smul' := by
        intro parameter matter
        exact chiralExteriorYukawaCoordinate_real_smul_right
          scalar parameter matter }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (first + second))
            (matterCoordinateEquiv.symm matter)) =
        matterCoordinateEquiv
            (chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm first)
              (matterCoordinateEquiv.symm matter)) +
          matterCoordinateEquiv
            (chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm second)
              (matterCoordinateEquiv.symm matter))
    rw [scalarCoordinateEquiv.symm.map_add,
      chiralExteriorYukawaAction_add, LinearMap.add_apply, map_add]
  map_smul' := by
    intro parameter scalar
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (parameter • scalar))
            (matterCoordinateEquiv.symm matter)) =
        parameter •
          matterCoordinateEquiv
            (chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm scalar)
              (matterCoordinateEquiv.symm matter))
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [scalarCoordinateEquiv.symm.map_smul,
      chiralExteriorYukawaAction_smul, LinearMap.smul_apply, map_smul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

def diracMatrixMatterCoordinateRealBilinear :
    DiracMatrix →ₗ[ℝ]
      MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun matrix :=
    (coframeDiracMatrixMatterCoordinateBilinear matrix).restrictScalars ℝ
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    exact LinearMap.congr_fun
      (coframeDiracMatrixMatterCoordinateBilinear.map_add first second) matter
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro matter
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact LinearMap.congr_fun
      (coframeDiracMatrixMatterCoordinateBilinear.map_smul
        (parameter : ℂ) matrix) matter

theorem holonomicScalarCoordinateDerivative_contDiff_local
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      fieldDirectionalDerivative configuration.scalar point direction := by
  have scalarSmooth : ContDiff ℝ ∞ configuration.scalar :=
    smooth.2.2.2.2.2.2.1
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry
        (fun _ : BasePoint => configuration.scalar)) := by
    exact scalarSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ configuration.scalar point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv (contDiff_id : ContDiff ℝ ∞
        (fun point : BasePoint => point)) (by simp)
  unfold fieldDirectionalDerivative
  exact derivativeSmooth.clm_apply contDiff_const

theorem holonomicScalarP286Action_contDiff_local
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      scalarMotherLieAction
        (p286LieBlockEmbed (configuration.gaugeConnection point direction))
        (configuration.scalar point) := by
  have matrixSmooth : ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        (configuration.gaugeConnection point direction) :=
    smooth.2.2.2.2.1 direction
  have scalarSmooth : ContDiff ℝ ∞ configuration.scalar :=
    smooth.2.2.2.2.2.2.1
  have actionSmooth : ContDiff ℝ ∞ fun point =>
      scalarP286ActionBilinear
        (p286CoordinateEquiv
          (configuration.gaugeConnection point direction))
        (configuration.scalar point) :=
    (scalarP286ActionBilinear.toContinuousBilinearMap.contDiff.comp
      matrixSmooth).clm_apply scalarSmooth
  change ContDiff ℝ ∞ fun point =>
    scalarMotherLieAction
      (p286LieBlockEmbed
        (p286CoordinateEquiv.symm
          (p286CoordinateEquiv
            (configuration.gaugeConnection point direction))))
      (configuration.scalar point) at actionSmooth
  simpa only [
    p286CoordinateEquiv.symm_apply_apply] using actionSmooth

theorem holonomicScalarCovariantDerivative_contDiff_local
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      holonomicScalarCovariantDerivative configuration point direction := by
  unfold holonomicScalarCovariantDerivative
  exact (holonomicScalarCoordinateDerivative_contDiff_local
      configuration smooth direction).add
    (holonomicScalarP286Action_contDiff_local
      configuration smooth direction)

theorem scalarCoordinatePairingRe_joint_contDiff_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (first second : E → ScalarCoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second) :
    ContDiff ℝ ∞ fun point =>
      scalarCoordinatePairingRe (first point) (second point) := by
  unfold scalarCoordinatePairingRe
  apply ContDiff.sum
  intro index _
  let coordinateLinear : ScalarCoordinateCarrier →L[ℝ] ℂ :=
    (PiLp.projₗ (𝕜 := ℂ) 2
      (fun _ : ScalarBasisIndex => ℂ) index)
      |>.toContinuousLinearMap |>.restrictScalars ℝ
  have firstEntry : ContDiff ℝ ∞ fun point => first point index := by
    change ContDiff ℝ ∞ fun point => coordinateLinear (first point)
    exact coordinateLinear.contDiff.comp firstSmooth
  have secondEntry : ContDiff ℝ ∞ fun point => second point index := by
    change ContDiff ℝ ∞ fun point => coordinateLinear (second point)
    exact coordinateLinear.contDiff.comp secondSmooth
  have conjugateFirst : ContDiff ℝ ∞ fun point => star (first point index) := by
    change ContDiff ℝ ∞ fun point =>
      Complex.conjCLE (first point index)
    exact Complex.conjCLE.contDiff.comp firstEntry
  exact Complex.reCLM.contDiff.comp (conjugateFirst.mul secondEntry)

theorem generatedScalarKineticDensity_pointCoframe_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedScalarKineticDensity source 0 pair.1
          (withCoframe
            (toContinuumPointField configuration pair.1) pair.2))
      (point, candidate) := by
  have metricInverseSmooth : ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        (lorentzianMetricOfCoframe pair.2)⁻¹)
      (point, candidate) := by
    have sndSmooth : ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe => pair.2)
        (point, candidate) := contDiffAt_snd
    have outer : ContDiffAt ℝ ∞
        (fun coframe : LorentzianCoframe =>
          (lorentzianMetricOfCoframe coframe)⁻¹) candidate :=
      lorentzianMetric_inv_contDiffAt candidate candidateNondegenerate
    rw [show (fun pair : BasePoint × LorentzianCoframe =>
        (lorentzianMetricOfCoframe pair.2)⁻¹) =
      (fun coframe : LorentzianCoframe =>
        (lorentzianMetricOfCoframe coframe)⁻¹) ∘
          (fun pair : BasePoint × LorentzianCoframe => pair.2) by rfl]
    exact outer.comp (point, candidate) sndSmooth
  have derivativeSmooth : ∀ direction : LorentzianIndex,
      ContDiff ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          holonomicScalarCovariantDerivative configuration pair.1 direction) := by
    intro direction
    exact (holonomicScalarCovariantDerivative_contDiff_local
      configuration smooth direction).comp contDiff_fst
  have jointInfinite : ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedScalarKineticDensity source 0 pair.1
          (withCoframe
            (toContinuumPointField configuration pair.1) pair.2))
      (point, candidate) := by
    simp only [generatedScalarKineticDensity,
      scalarFrameRelativeCovariantDerivative,
      scalarFrameRelativeCoordinates_zeroChart_local,
      withCoframe, toContinuumPointField]
    apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro first _
    apply ContDiffAt.sum
    intro second _
    exact (contDiffAt_pi.mp
        (contDiffAt_pi.mp metricInverseSmooth first) second).mul
      ((scalarCoordinatePairingRe_joint_contDiff_local
          _ _ (derivativeSmooth first) (derivativeSmooth second)).contDiffAt)
  exact jointInfinite.of_le (by norm_num)

theorem generatedScalarPotential_pointCoframe_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe) :
    ContDiffAt ℝ 1
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedScalarPotential source 0 pair.1
          (withCoframe
            (toContinuumPointField configuration pair.1) pair.2).scalar)
      (point, candidate) := by
  have scalarSmooth : ContDiff ℝ ∞ configuration.scalar :=
    smooth.2.2.2.2.2.2.1
  have jointInfinite : ContDiff ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedScalarPotential source 0 pair.1
          (withCoframe
            (toContinuumPointField configuration pair.1) pair.2).scalar) := by
    simp only [generatedScalarPotential,
      scalarFrameRelativeCoordinates_zeroChart_local,
      withCoframe, toContinuumPointField]
    unfold scalarCoordinateSquaredNorm
    apply ContDiff.sum
    intro index _
    let scalarDifference := fun pair : BasePoint × LorentzianCoframe =>
      configuration.scalar pair.1 - sourceGeneratedVacuumCoordinates source
    have scalarDifferenceSmooth : ContDiff ℝ ∞ scalarDifference := by
      exact (scalarSmooth.comp contDiff_fst).sub contDiff_const
    let coordinateLinear : ScalarCoordinateCarrier →L[ℝ] ℂ :=
      (PiLp.projₗ (𝕜 := ℂ) 2
        (fun _ : ScalarBasisIndex => ℂ) index)
        |>.toContinuousLinearMap |>.restrictScalars ℝ
    let coordinate := fun pair : BasePoint × LorentzianCoframe =>
      scalarDifference pair index
    have coordinateSmooth : ContDiff ℝ ∞ coordinate := by
      change ContDiff ℝ ∞ fun pair =>
        coordinateLinear (scalarDifference pair)
      exact coordinateLinear.contDiff.comp scalarDifferenceSmooth
    have realSmooth : ContDiff ℝ ∞ fun pair => (coordinate pair).re :=
      Complex.reCLM.contDiff.comp coordinateSmooth
    have imaginarySmooth : ContDiff ℝ ∞ fun pair => (coordinate pair).im :=
      Complex.imCLM.contDiff.comp coordinateSmooth
    simpa only [coordinate, scalarDifference, Complex.normSq_apply] using
      realSmooth.mul realSmooth |>.add (imaginarySmooth.mul imaginarySmooth)
  exact jointInfinite.contDiffAt.of_le (by norm_num)

theorem holonomicMatterCoordinateDerivative_contDiff_local
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv
          (configuration.matter candidate)) point direction := by
  have matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry
        (fun _ : BasePoint =>
          fun point => matterCoordinateEquiv (configuration.matter point))) := by
    exact matterSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ
        (fun candidate => matterCoordinateEquiv
          (configuration.matter candidate)) point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv (contDiff_id : ContDiff ℝ ∞
        (fun point : BasePoint => point)) (by simp)
  unfold fieldDirectionalDerivative
  exact derivativeSmooth.clm_apply contDiff_const

theorem holonomicMatterCovariantDerivative_coordinate_contDiff_local
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (holonomicMatterCovariantDerivative configuration point direction) := by
  have derivativeSmooth :=
    holonomicMatterCoordinateDerivative_contDiff_local
      configuration smooth direction
  have matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1
  have gravitySmooth : ∀ formDirection internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        configuration.gravityConnection point formDirection
          internalOut internalIn :=
    smooth.2.1
  have gaugeSmooth : ∀ formDirection,
      ContDiff ℝ ∞ fun point =>
        p286CoordinateEquiv
          (configuration.gaugeConnection point formDirection) :=
    smooth.2.2.2.2.1
  have spinMatrixSmooth : ContDiff ℝ ∞ fun point =>
      diracSpinConnectionLift
        (configuration.gravityConnection point) direction := by
    apply contDiff_pi'
    intro row
    apply contDiff_pi'
    intro column
    unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply ContDiff.sum
    intro pair _
    have realCoefficientSmooth : ContDiff ℝ ∞ fun point =>
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          configuration.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) :=
      contDiff_const.mul
        (gravitySmooth direction (lorentzBivectorFirst pair)
          (lorentzBivectorSecond pair))
    have complexCoefficientSmooth : ContDiff ℝ ∞ fun point =>
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          configuration.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp realCoefficientSmooth
    have coefficientSmooth : ContDiff ℝ ∞ fun point =>
        ((2 : ℂ)⁻¹ *
          (minkowskiInternalSign (lorentzBivectorFirst pair) *
            configuration.gravityConnection point direction
              (lorentzBivectorFirst pair)
              (lorentzBivectorSecond pair) : ℝ) : ℂ) := by
      exact contDiff_const.mul complexCoefficientSmooth
    exact coefficientSmooth.mul contDiff_const
  have spinActionSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (configuration.gravityConnection point) direction)
          (configuration.matter point)) := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        spinMatrixSmooth).clm_apply matterSmooth
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (configuration.gravityConnection point) direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (configuration.matter point)))) at actual
    simpa only [
      matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeActionSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (configuration.gaugeConnection point direction))
          (configuration.matter point)) := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff.comp
        (gaugeSmooth direction)).clm_apply matterSmooth
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (configuration.gaugeConnection point direction))))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (configuration.matter point)))) at actual
    simpa only [
      p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicMatterCovariantDerivative
  simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
  exact derivativeSmooth.add spinActionSmooth |>.add gaugeActionSmooth

theorem generatedContinuumMatterVector_pointCoframe_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (generatedContinuumMatterVector source 0 pair.1
            (withCoframe
              (toContinuumPointField configuration pair.1) pair.2)))
      (point, candidate) := by
  have gammaSmooth : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := pair.2, derivative := 0 } direction)
        (point, candidate) := by
    intro direction
    have sndSmooth : ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe => pair.2)
        (point, candidate) := contDiffAt_snd
    have outer : ContDiffAt ℝ ∞
        (fun coframe : LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := coframe, derivative := 0 } direction) candidate :=
      inverseCoframeDiracGamma_contDiffAt candidate
        candidateNondegenerate direction
    rw [show (fun pair : BasePoint × LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := pair.2, derivative := 0 } direction) =
      (fun coframe : LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := coframe, derivative := 0 } direction) ∘
        (fun pair : BasePoint × LorentzianCoframe => pair.2) by rfl]
    exact outer.comp (point, candidate) sndSmooth
  have derivativeSmooth : ∀ direction : LorentzianIndex,
      ContDiff ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv
            (holonomicMatterCovariantDerivative configuration pair.1
              direction)) := by
    intro direction
    exact (holonomicMatterCovariantDerivative_coordinate_contDiff_local
      configuration smooth direction).comp contDiff_fst
  have kineticDirectionSmooth : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := pair.2, derivative := 0 } direction)
              (holonomicMatterCovariantDerivative configuration pair.1
                direction)))
        (point, candidate) := by
    intro direction
    have actualGamma := gammaSmooth direction
    have actualDerivative : ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv
            (holonomicMatterCovariantDerivative configuration pair.1
              direction)) (point, candidate) :=
      (derivativeSmooth direction).contDiffAt
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp (point, candidate) actualGamma).clm_apply
          actualDerivative
    change ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := pair.2, derivative := 0 } direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv
                (holonomicMatterCovariantDerivative configuration pair.1
                  direction))))) (point, candidate) at actual
    simpa only [
      matterCoordinateEquiv.symm_apply_apply] using actual
  have scalarSmooth : ContDiff ℝ ∞ configuration.scalar :=
    smooth.2.2.2.2.2.2.1
  have matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1
  have yukawaSmooth : ContDiff ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (configuration.scalar pair.1))
            (configuration.matter pair.1))) := by
    have scalarOnProduct : ContDiff ℝ ∞ fun pair :
        BasePoint × LorentzianCoframe => configuration.scalar pair.1 :=
      scalarSmooth.comp contDiff_fst
    have matterOnProduct : ContDiff ℝ ∞ fun pair :
        BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv (configuration.matter pair.1) :=
      matterSmooth.comp contDiff_fst
    have actual :=
      (chiralExteriorYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        scalarOnProduct).clm_apply matterOnProduct
    change ContDiff ℝ ∞ fun pair : BasePoint × LorentzianCoframe =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar pair.1))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (configuration.matter pair.1)))) at actual
    simpa only [
      matterCoordinateEquiv.symm_apply_apply] using actual
  simp only [generatedContinuumMatterVector,
    matterDerivativeFrameRelative, matterFrameRelative_zeroChart_local,
    scalarFrameRelativeCoordinates_zeroChart_local,
    withCoframe, toContinuumPointField]
  simp only [map_add, map_smul, map_sum]
  exact
    ((contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : BasePoint × LorentzianCoframe => (Complex.I : ℂ))
        (point, candidate)).smul
      (ContDiffAt.sum fun direction _ => kineticDirectionSmooth direction)).add
      yukawaSmooth.contDiffAt

theorem generatedContinuumMatterDensity_pointCoframe_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedContinuumMatterDensity source 0 pair.1
          (withCoframe
            (toContinuumPointField configuration pair.1) pair.2))
      (point, candidate) := by
  let vector := fun pair : BasePoint × LorentzianCoframe =>
    generatedContinuumMatterVector source 0 pair.1
      (withCoframe
        (toContinuumPointField configuration pair.1) pair.2)
  have vectorCoordinateSmooth : ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (vector pair)) (point, candidate) :=
    generatedContinuumMatterVector_pointCoframe_coordinate_contDiffAt
      source configuration smooth point candidate candidateNondegenerate
  have dualCoordinateSmooth : ∀ index : MatterCoordinateIndex,
      ContDiff ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          configuration.conjugateMatter pair.1
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))) := by
    intro index
    exact (smooth.2.2.2.2.2.2.2.2 index).comp contDiff_fst
  have pairingSumSmooth : ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector pair) index *
            configuration.conjugateMatter pair.1
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))))
      (point, candidate) := by
    apply ContDiffAt.sum
    intro index _
    have vectorEntrySmooth : ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv (vector pair) index) (point, candidate) := by
      fun_prop
    exact vectorEntrySmooth.mul (dualCoordinateSmooth index).contDiffAt
  have dualPairingSmooth : ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter pair.1 (vector pair))
      (point, candidate) := by
    rw [show (fun pair : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter pair.1 (vector pair)) =
      fun pair => ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector pair) index *
          configuration.conjugateMatter pair.1
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
      funext pair
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        coframeMatterDual_coordinate_expansion
          (configuration.conjugateMatter pair.1)
          (matterCoordinateEquiv (vector pair))]
    exact pairingSumSmooth
  have realPairingSmooth : ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        (configuration.conjugateMatter pair.1 (vector pair)).re)
      (point, candidate) :=
    Complex.reCLM.contDiff.contDiffAt.comp (point, candidate)
      dualPairingSmooth
  have exactDensity :
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedContinuumMatterDensity source 0 pair.1
          (withCoframe
            (toContinuumPointField configuration pair.1) pair.2)) =
      fun pair =>
        (configuration.conjugateMatter pair.1 (vector pair)).re := by
    funext pair
    simp only [generatedContinuumMatterDensity,
      matterDualFrameRelative_zeroChart_local,
      withCoframe, toContinuumPointField, vector]
  rw [exactDensity]
  exact realPairingSmooth.of_le (by norm_num)

theorem generatedScalarMatterSector_pointCoframe_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedScalarKineticDensity source 0 pair.1
            (withCoframe
              (toContinuumPointField configuration pair.1) pair.2) -
          generatedScalarPotential source 0 pair.1
            (withCoframe
              (toContinuumPointField configuration pair.1) pair.2).scalar +
          generatedContinuumMatterDensity source 0 pair.1
            (withCoframe
              (toContinuumPointField configuration pair.1) pair.2))
      (point, candidate) := by
  exact ((generatedScalarKineticDensity_pointCoframe_contDiffAt
      source configuration smooth point candidate candidateNondegenerate).sub
    (generatedScalarPotential_pointCoframe_contDiffAt
      source configuration smooth point candidate)).add
    (generatedContinuumMatterDensity_pointCoframe_contDiffAt
      source configuration smooth point candidate candidateNondegenerate)

end

end SaturationMonoid.PhysicsCore.StageNineCoframeScalarMatterRegularity
