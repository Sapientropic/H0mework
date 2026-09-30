import H0mework.Physics.DiracEvolution.SafeCanonicalAffineSpatialDifferenceQuotientTest
import H0mework.Physics.DiracEvolution.SafeCommutedCoefficientBound
import Mathlib.Analysis.Calculus.MeanValue

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientCommutator

open Set
open ProofFreeRicherAnholonomicSource
open StageNineDiracMatterSymmetricHyperbolicFluxBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedCoefficientBound
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineHolonomicField
open StageNineMatterCoordinateFirstOrderCommutator

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance differenceQuotientCommutatorMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-- The complete fixed-source first-order coefficient block acting on one
value-and-first-jet carrier. -/
def fixedMatterFirstJetActionLinear
    (point : BasePoint) :
    MatterCoordinateFirstJetCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun jet :=
    (∑ direction : LorentzianIndex,
      fixedEvolutionPrincipalCoordinateCLM direction point
        (jet.2 direction)) +
      fixedMatterLowerCoefficient point jet.1
  map_add' first second := by
    simp only [Prod.fst_add, Prod.snd_add, WithLp.ofLp_add, Pi.add_apply,
      map_add, Finset.sum_add_distrib]
    abel
  map_smul' parameter jet := by
    simp only [Prod.smul_fst, Prod.smul_snd, WithLp.ofLp_smul, Pi.smul_apply,
      map_smul, RingHom.id_apply, Finset.smul_sum, smul_add]

def fixedMatterFirstJetActionCLM
    (point : BasePoint) :
    MatterCoordinateFirstJetCarrier →L[ℝ] MatterCoordinateCarrier :=
  ⟨fixedMatterFirstJetActionLinear point,
    (fixedMatterFirstJetActionLinear point
      ).continuous_of_finiteDimensional⟩

theorem fixedMatterFirstJetActionCLM_contDiff_one :
    ContDiff ℝ 1 fixedMatterFirstJetActionCLM := by
  rw [contDiff_clm_apply_iff]
  intro jet
  have principalRegular : ContDiff ℝ 1 (fun point =>
      ∑ direction : LorentzianIndex,
        fixedEvolutionPrincipalCoordinateCLM direction point
          (jet.2 direction)) := by
    exact ContDiff.sum fun direction _ =>
      (fixedEvolutionPrincipalCoordinateCLM_contDiff direction).clm_apply
        contDiff_const
  exact principalRegular.add
    (fixedMatterLowerCoefficient_contDiff_one.clm_apply contDiff_const)

theorem fixedMatterFirstJetActionCLM_directionalDerivative
    (point : BasePoint)
    (jet : MatterCoordinateFirstJetCarrier)
    (commutedDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => fixedMatterFirstJetActionCLM candidate jet)
        point commutedDirection =
      fixedMatterCoefficientChangedReadCLM point jet commutedDirection := by
  have principalTermDerivative (direction : LorentzianIndex) :
      fieldDirectionalDerivative (fun candidate =>
          fixedEvolutionPrincipalCoordinateCLM direction candidate
            (jet.2 direction)) point commutedDirection =
        (fieldDirectionalDerivative
          (fixedEvolutionPrincipalCoordinateCLM direction) point
          commutedDirection) (jet.2 direction) := by
    unfold fieldDirectionalDerivative
    rw [fderiv_clm_apply
      ((fixedEvolutionPrincipalCoordinateCLM_contDiff direction
        ).differentiable one_ne_zero).differentiableAt
      (differentiableAt_const (c := jet.2 direction))]
    simp
  have lowerTermDerivative :
      fieldDirectionalDerivative (fun candidate =>
          fixedMatterLowerCoefficient candidate jet.1)
          point commutedDirection =
        (fieldDirectionalDerivative fixedMatterLowerCoefficient point
          commutedDirection) jet.1 := by
    unfold fieldDirectionalDerivative
    rw [fderiv_clm_apply
      (fixedMatterLowerCoefficient_contDiff_one.differentiable one_ne_zero
        ).differentiableAt
      (differentiableAt_const (c := jet.1))]
    simp
  have principalDifferentiable : DifferentiableAt ℝ (fun candidate =>
      ∑ direction : LorentzianIndex,
        fixedEvolutionPrincipalCoordinateCLM direction candidate
          (jet.2 direction)) point := by
    apply DifferentiableAt.fun_sum
    intro direction _
    exact ((fixedEvolutionPrincipalCoordinateCLM_contDiff direction
      ).differentiable one_ne_zero).differentiableAt.clm_apply
        (differentiableAt_const (c := jet.2 direction))
  have lowerDifferentiable : DifferentiableAt ℝ (fun candidate =>
      fixedMatterLowerCoefficient candidate jet.1) point :=
    (fixedMatterLowerCoefficient_contDiff_one.differentiable one_ne_zero
      ).differentiableAt.clm_apply (differentiableAt_const (c := jet.1))
  change fderiv ℝ (fun candidate =>
      (∑ direction : LorentzianIndex,
        fixedEvolutionPrincipalCoordinateCLM direction candidate
          (jet.2 direction)) +
        fixedMatterLowerCoefficient candidate jet.1) point
          (coordinateDirection commutedDirection) = _
  rw [fderiv_fun_add principalDifferentiable lowerDifferentiable,
    fderiv_fun_sum (u := Finset.univ) (fun direction _ =>
      ((fixedEvolutionPrincipalCoordinateCLM_contDiff direction
        ).differentiable one_ne_zero).differentiableAt.clm_apply
          (differentiableAt_const (c := jet.2 direction)))]
  simp only [add_apply]
  change (∑ direction : LorentzianIndex,
      fieldDirectionalDerivative (fun candidate =>
        fixedEvolutionPrincipalCoordinateCLM direction candidate
          (jet.2 direction)) point commutedDirection) +
      fieldDirectionalDerivative (fun candidate =>
        fixedMatterLowerCoefficient candidate jet.1)
        point commutedDirection = _
  rw [show (∑ direction : LorentzianIndex,
      fieldDirectionalDerivative (fun candidate =>
        fixedEvolutionPrincipalCoordinateCLM direction candidate
          (jet.2 direction)) point commutedDirection) =
      ∑ direction : LorentzianIndex,
        (fieldDirectionalDerivative
          (fixedEvolutionPrincipalCoordinateCLM direction) point
          commutedDirection) (jet.2 direction) by
    apply Finset.sum_congr rfl
    intro direction _
    exact principalTermDerivative direction,
    lowerTermDerivative]
  rfl

/-- Exact finite-difference commutator of the complete source coefficient
block. -/
def fixedMatterCoefficientFiniteDifferenceRead
    (first second : BasePoint)
    (scale : ℝ)
    (shiftedJet : MatterCoordinateFirstJetCarrier) :
    MatterCoordinateCarrier :=
  scale •
    ((fixedMatterFirstJetActionCLM second -
      fixedMatterFirstJetActionCLM first) shiftedJet)

theorem fixedMatterFirstJetAction_finiteDifference
    (first second : BasePoint)
    (scale : ℝ)
    (firstJet secondJet : MatterCoordinateFirstJetCarrier) :
    scale •
        (fixedMatterFirstJetActionCLM second secondJet -
          fixedMatterFirstJetActionCLM first firstJet) =
      fixedMatterFirstJetActionCLM first
          (scale • (secondJet - firstJet)) +
        fixedMatterCoefficientFiniteDifferenceRead
          first second scale secondJet := by
  simp only [map_smul, map_sub, fixedMatterCoefficientFiniteDifferenceRead,
    sub_apply]
  module

def fixedMatterFirstJetActionOnSlice
    (point : ℝ × DiracMatterSpatialCoordinates) :
    MatterCoordinateFirstJetCarrier →L[ℝ] MatterCoordinateCarrier :=
  fixedMatterFirstJetActionCLM
    (diracMatterSpacetimeCoordinatePoint point.1 point.2)

theorem fixedMatterFirstJetActionOnSlice_contDiff_one :
    ContDiff ℝ 1 fixedMatterFirstJetActionOnSlice := by
  exact fixedMatterFirstJetActionCLM_contDiff_one.comp
    (diracMatterSpacetimeCoordinatePoint_joint_contDiff.of_le (by norm_num))

theorem fixedMatterCoefficientFiniteDifferenceRead_norm_le_onBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (coefficientBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedMatterCoefficientChangedReadCLM
          (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (space : DiracMatterSpatialCoordinates)
    (spatialDirection : Fin 3)
    (step : ℝ)
    (spaceMem : space ∈ Icc a b)
    (shiftedSpaceMem :
      space + step • Pi.single spatialDirection 1 ∈ Icc a b)
    (scale : ℝ)
    (jet : MatterCoordinateFirstJetCarrier) :
    ‖fixedMatterCoefficientFiniteDifferenceRead
        (diracMatterSpacetimeCoordinatePoint time space)
        (diracMatterSpacetimeCoordinatePoint time
          (space + step • Pi.single spatialDirection 1))
        scale jet‖ ≤
      |scale| * (C * |step|) * ‖jet‖ := by
  let point := diracMatterSpacetimeCoordinatePoint time space
  let path : ℝ → MatterCoordinateCarrier := fun parameter =>
    fixedMatterFirstJetActionCLM
      (diracMatterCoordinateLine point spatialDirection.succ
        (parameter * step)) jet
  have pathDerivative (parameter : ℝ) : HasDerivAt path
      (step • fixedMatterCoefficientChangedReadCLM
        (diracMatterCoordinateLine point spatialDirection.succ
          (parameter * step)) jet spatialDirection.succ) parameter := by
    have lineDerivative : HasDerivAt (fun candidate : ℝ =>
        diracMatterCoordinateLine point spatialDirection.succ
          (candidate * step))
        (step • coordinateDirection spatialDirection.succ) parameter := by
      let directionLinear : ℝ →L[ℝ] BasePoint :=
        (1 : ℝ →L[ℝ] ℝ).smulRight
          (step • coordinateDirection spatialDirection.succ)
      have derivative := (hasDerivAt_const (x := parameter) point).add
        directionLinear.hasFDerivAt.hasDerivAt
      have lineEq : (fun candidate : ℝ =>
          diracMatterCoordinateLine point spatialDirection.succ
            (candidate * step)) =
          fun candidate => point + directionLinear candidate := by
        funext candidate
        change point + (candidate * step) •
            coordinateDirection spatialDirection.succ =
          point + candidate •
            (step • coordinateDirection spatialDirection.succ)
        rw [smul_smul]
      rw [lineEq]
      exact derivative.congr_deriv (by simp [directionLinear])
    have outerRegular : ContDiff ℝ 1 (fun candidate =>
        fixedMatterFirstJetActionCLM candidate jet) :=
      fixedMatterFirstJetActionCLM_contDiff_one.clm_apply
        (contDiff_const (c := jet))
    have composed :=
      (outerRegular.differentiable one_ne_zero
        (diracMatterCoordinateLine point spatialDirection.succ
          (parameter * step))).hasFDerivAt.comp_hasDerivAt
            parameter lineDerivative
    have outerDerivative : HasDerivAt path
        (fderiv ℝ (fun candidate =>
          fixedMatterFirstJetActionCLM candidate jet)
          (diracMatterCoordinateLine point spatialDirection.succ
            (parameter * step))
          (step • coordinateDirection spatialDirection.succ)) parameter := by
      simpa [path, Function.comp_def] using composed
    apply outerDerivative.congr_deriv
    rw [map_smul]
    change step • fieldDirectionalDerivative (fun candidate =>
        fixedMatterFirstJetActionCLM candidate jet)
        (diracMatterCoordinateLine point spatialDirection.succ
          (parameter * step)) spatialDirection.succ = _
    rw [fixedMatterFirstJetActionCLM_directionalDerivative]
  have pathDerivativeBound : ∀ parameter ∈ Icc (0 : ℝ) 1,
      ‖step • fixedMatterCoefficientChangedReadCLM
        (diracMatterCoordinateLine point spatialDirection.succ
          (parameter * step)) jet spatialDirection.succ‖ ≤
        |step| * C * ‖jet‖ := by
    intro parameter parameterMem
    have intermediateSpaceMem :
        space + (parameter * step) • Pi.single spatialDirection 1 ∈
          Icc a b := by
      have lineMem := (convex_Icc a b).lineMap_mem
        spaceMem shiftedSpaceMem parameterMem
      simpa [AffineMap.lineMap_apply, smul_smul, add_comm] using lineMem
    have operatorBound := coefficientBound time timeMem
      (space + (parameter * step) • Pi.single spatialDirection 1)
      intermediateSpaceMem
    have applyBound :
        ‖fixedMatterCoefficientChangedReadCLM
            (diracMatterCoordinateLine point spatialDirection.succ
              (parameter * step)) jet‖ ≤ C * ‖jet‖ := by
      rw [← diracMatterSpacetimeCoordinatePoint_line]
      exact (fixedMatterCoefficientChangedReadCLM
          (diracMatterSpacetimeCoordinatePoint time
            (space + (parameter * step) • Pi.single spatialDirection 1))
          ).le_opNorm jet |>.trans
        (mul_le_mul_of_nonneg_right operatorBound (norm_nonneg jet))
    calc
      ‖step • fixedMatterCoefficientChangedReadCLM
          (diracMatterCoordinateLine point spatialDirection.succ
            (parameter * step)) jet spatialDirection.succ‖ =
          |step| *
            ‖fixedMatterCoefficientChangedReadCLM
              (diracMatterCoordinateLine point spatialDirection.succ
                (parameter * step)) jet spatialDirection.succ‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |step| *
          ‖fixedMatterCoefficientChangedReadCLM
            (diracMatterCoordinateLine point spatialDirection.succ
              (parameter * step)) jet‖ := by
        exact mul_le_mul_of_nonneg_left
          (PiLp.norm_apply_le _ spatialDirection.succ) (abs_nonneg step)
      _ ≤ |step| * (C * ‖jet‖) :=
        mul_le_mul_of_nonneg_left applyBound (abs_nonneg step)
      _ = |step| * C * ‖jet‖ := by ring
  have coefficientDifference :
      ‖fixedMatterFirstJetActionCLM
          (diracMatterSpacetimeCoordinatePoint time
            (space + step • Pi.single spatialDirection 1)) jet -
        fixedMatterFirstJetActionCLM
          (diracMatterSpacetimeCoordinatePoint time space) jet‖ ≤
        (|step| * C * ‖jet‖) * ‖(1 : ℝ) - 0‖ := by
    have pathBound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := Icc (0 : ℝ) 1) (x := (0 : ℝ)) (y := (1 : ℝ))
        (fun parameter parameterMem =>
          (pathDerivative parameter).hasDerivWithinAt)
        pathDerivativeBound (convex_Icc (0 : ℝ) 1)
        (left_mem_Icc.mpr zero_le_one)
        (right_mem_Icc.mpr zero_le_one)
    simpa [path, point] using pathBound
  rw [fixedMatterCoefficientFiniteDifferenceRead, norm_smul,
    Real.norm_eq_abs]
  calc
    |scale| *
        ‖(fixedMatterFirstJetActionCLM
          (diracMatterSpacetimeCoordinatePoint time
            (space + step • Pi.single spatialDirection 1)) -
          fixedMatterFirstJetActionCLM
            (diracMatterSpacetimeCoordinatePoint time space)) jet‖ =
        |scale| *
          ‖fixedMatterFirstJetActionCLM
              (diracMatterSpacetimeCoordinatePoint time
                (space + step • Pi.single spatialDirection 1)) jet -
            fixedMatterFirstJetActionCLM
              (diracMatterSpacetimeCoordinatePoint time space) jet‖ := by
      rfl
    _ ≤ |scale| * ((|step| * C * ‖jet‖) * ‖(1 : ℝ) - 0‖) :=
      mul_le_mul_of_nonneg_left coefficientDifference (abs_nonneg scale)
    _ = |scale| * (C * |step|) * ‖jet‖ := by
      norm_num
      ring

/-- With the canonical inverse step, the coefficient commutator is uniformly
bounded independently of the nonzero spatial difference scale. -/
theorem fixedMatterCoefficientDifferenceQuotientRead_norm_le_onBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (coefficientBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedMatterCoefficientChangedReadCLM
          (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (space : DiracMatterSpatialCoordinates)
    (spatialDirection : Fin 3)
    (step : ℝ)
    (stepNonzero : step ≠ 0)
    (spaceMem : space ∈ Icc a b)
    (shiftedSpaceMem :
      space + step • Pi.single spatialDirection 1 ∈ Icc a b)
    (jet : MatterCoordinateFirstJetCarrier) :
    ‖fixedMatterCoefficientFiniteDifferenceRead
        (diracMatterSpacetimeCoordinatePoint time space)
        (diracMatterSpacetimeCoordinatePoint time
          (space + step • Pi.single spatialDirection 1))
        step⁻¹ jet‖ ≤
      C * ‖jet‖ := by
  have raw := fixedMatterCoefficientFiniteDifferenceRead_norm_le_onBox
    timeStart timeEnd a b C coefficientBound time timeMem space
      spatialDirection step spaceMem shiftedSpaceMem step⁻¹ jet
  have absStepNonzero : |step| ≠ 0 := abs_ne_zero.mpr stepNonzero
  calc
    ‖fixedMatterCoefficientFiniteDifferenceRead
        (diracMatterSpacetimeCoordinatePoint time space)
        (diracMatterSpacetimeCoordinatePoint time
          (space + step • Pi.single spatialDirection 1))
        step⁻¹ jet‖ ≤
        |step⁻¹| * (C * |step|) * ‖jet‖ := raw
    _ = C * ‖jet‖ := by
      rw [abs_inv]
      field_simp

/-- One fixed source-owned constant controls every canonical spatial
coefficient difference quotient on the selected compact spacetime box. -/
theorem exists_fixedMatterCoefficientDifferenceQuotientBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ time ∈ Icc timeStart timeEnd,
        ∀ space : DiracMatterSpatialCoordinates,
          ∀ spatialDirection : Fin 3,
            ∀ step : ℝ, step ≠ 0 →
              space ∈ Icc a b →
              space + step • Pi.single spatialDirection 1 ∈ Icc a b →
              ∀ jet : MatterCoordinateFirstJetCarrier,
                ‖fixedMatterCoefficientFiniteDifferenceRead
                    (diracMatterSpacetimeCoordinatePoint time space)
                    (diracMatterSpacetimeCoordinatePoint time
                      (space + step • Pi.single spatialDirection 1))
                    step⁻¹ jet‖ ≤
                  C * ‖jet‖ := by
  obtain ⟨C, CNonnegative, coefficientBound⟩ :=
    exists_fixedMatterCoefficientChangedReadBoundOnBox
      timeStart timeEnd a b
  refine ⟨C, CNonnegative, ?_⟩
  intro time timeMem space spatialDirection step stepNonzero spaceMem
    shiftedSpaceMem jet
  exact fixedMatterCoefficientDifferenceQuotientRead_norm_le_onBox
    timeStart timeEnd a b C coefficientBound time timeMem space
      spatialDirection step stepNonzero spaceMem shiftedSpaceMem jet

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientCommutator
