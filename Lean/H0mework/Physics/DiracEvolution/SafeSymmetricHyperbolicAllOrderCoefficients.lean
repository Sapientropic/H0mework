import H0mework.Physics.DiracEvolution.SafeCanonicalAffineSpatialDifferenceQuotientCommutator

/-!
# Fixed P506/L0 all-order symmetric-hyperbolic coefficient budget

The post-EC source current makes the complete first-order matter action smooth
to every order.  Compactness then generates, in one source-owned object, the
coefficient and initial-slice derivative bounds consumed by the high-order
energy induction.  No solution, residual, Sobolev budget, or derivative bound
is accepted as constructor input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCoefficients

open Set
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeHolonomicRegularity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCauchySafeMatterVolterraLocalRegularity
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientCommutator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

private abbrev Safe : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeGlobalActual

local instance allOrderP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance allOrderP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance allOrderP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

local instance allOrderMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance allOrderFullDerivativeNormedAddCommGroup :
    NormedAddCommGroup
      (WithLp 2 (LorentzianIndex → MatterCoordinateCarrier)) :=
  PiLp.normedAddCommGroup 2
    (fun _ : LorentzianIndex => MatterCoordinateCarrier)

local instance allOrderFullDerivativeNormedSpace :
    NormedSpace ℝ
      (WithLp 2 (LorentzianIndex → MatterCoordinateCarrier)) :=
  PiLp.normedSpace 2 ℝ
    (fun _ : LorentzianIndex => MatterCoordinateCarrier)

theorem fixedEvolutionPrincipalCoordinateCLM_contDiff_infty
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ (fixedEvolutionPrincipalCoordinateCLM direction) := by
  rw [contDiff_clm_apply_iff]
  intro coordinates
  change ContDiff ℝ ∞ (fun point =>
    diracMatrixMatterCoordinateCLM
      (fixedEvolutionPrincipal direction point) coordinates)
  exact diracMatrixMatterCoordinateCLM.contDiff.clm_apply contDiff_const
    |>.comp (by
      apply contDiff_pi'
      intro row
      apply contDiff_pi'
      intro column
      exact fixedEvolutionPrincipal_entry_contDiff direction row column)

private theorem current_nondegenerate (point : BasePoint) :
    Matrix.det (Current.coframe point) ≠ 0 := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact fixedP506L0CartanECConstraintCauchySafeGlobalActual_nondegenerate point

private theorem current_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (Current.coframe point) ≠ 0 := by
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact fixedP506L0CartanECConstraintCauchySafeGlobalActual_noncharacteristic point

private theorem fixedConstantCoordinateVelocityCLM_apply_contDiff_infty
    (coordinates : MatterCoordinateCarrier) :
    ContDiff ℝ ∞ (fun point =>
      fixedConstantCoordinateVelocityCLM point coordinates) := by
  rw [contDiff_infty]
  intro order
  rw [contDiff_iff_contDiffAt]
  intro point
  let candidate : BasePoint → DiracExteriorMatterCarrier :=
    fun _ => matterCoordinateEquiv.symm coordinates
  have read : (fun target =>
      fixedConstantCoordinateVelocityCLM target coordinates) =
      cauchySafeMatterVolterraVelocity Current candidate := by
    funext target
    have applyEq :=
      fixedConstantCoordinateVelocityCLM_apply target coordinates
    change fixedConstantCoordinateVelocityCLM target coordinates =
      cauchySafeMatterVolterraVelocity Current candidate target at applyEq
    exact applyEq
  rw [read]
  apply cauchySafeMatterVolterraVelocity_contDiffAt_of_local
      (order := order) Current candidate point
  · exact current_nondegenerate point
  · exact current_noncharacteristic point
  · apply contDiffAt_pi'
    intro row
    apply contDiffAt_pi'
    intro column
    exact
      (fixedP506L0CauchySafeMatterGalerkinInputActual_smooth.1 row column
        ).contDiffAt.of_le (by exact_mod_cast le_top)
  · intro direction internalOut internalIn
    exact
      (fixedP506L0CauchySafeMatterGalerkinInputActual_smooth.2.1
        direction internalOut internalIn).contDiffAt.of_le
        (by exact_mod_cast le_top)
  · exact
      fixedP506L0CauchySafeMatterGalerkinInputActual_smooth.2.2.2.2.2.2.1
        |>.contDiffAt.of_le (by exact_mod_cast le_top)
  · rw [show (fun target => matterCoordinateEquiv (candidate target)) =
        (fun _ : BasePoint => coordinates) by
      funext target
      simp [candidate]]
    exact contDiffAt_const
  · intro direction
    exact
      (fixedP506L0CauchySafeMatterGalerkinInputActual_smooth.2.2.2.2.1
        direction).contDiffAt.of_le (by exact_mod_cast le_top)

theorem fixedConstantCoordinateVelocityCLM_contDiff_infty :
    ContDiff ℝ ∞ fixedConstantCoordinateVelocityCLM := by
  rw [contDiff_clm_apply_iff]
  exact fixedConstantCoordinateVelocityCLM_apply_contDiff_infty

theorem fixedMatterLowerCoefficient_contDiff_infty :
    ContDiff ℝ ∞ fixedMatterLowerCoefficient := by
  rw [contDiff_clm_apply_iff]
  intro coordinates
  change ContDiff ℝ ∞ (fun point =>
    -fixedEvolutionPrincipalCoordinateCLM 0 point
      (fixedConstantCoordinateVelocityCLM point coordinates))
  exact ((fixedEvolutionPrincipalCoordinateCLM_contDiff_infty 0).clm_apply
    (fixedConstantCoordinateVelocityCLM_contDiff_infty.clm_apply
      contDiff_const)).neg

theorem fixedMatterFirstJetActionCLM_contDiff_infty :
    ContDiff ℝ ∞ fixedMatterFirstJetActionCLM := by
  rw [contDiff_clm_apply_iff]
  intro jet
  have principalRegular : ContDiff ℝ ∞ (fun point =>
      ∑ direction : LorentzianIndex,
        fixedEvolutionPrincipalCoordinateCLM direction point
          (jet.2 direction)) :=
    ContDiff.sum fun direction _ =>
      (fixedEvolutionPrincipalCoordinateCLM_contDiff_infty direction
        ).clm_apply contDiff_const
  exact principalRegular.add
    (fixedMatterLowerCoefficient_contDiff_infty.clm_apply contDiff_const)

def fixedMatterFirstJetActionCoefficientDerivative
    (order : ℕ)
    (point : BasePoint) :=
  iteratedFDeriv ℝ order fixedMatterFirstJetActionCLM point

/-- Every spatial derivative order of the source-owned initial matter slice
is a canonical field, rather than an externally supplied Sobolev datum. -/
def fixedMatterCanonicalSourceInitialDerivative
    (order : ℕ)
    (initialTime : ℝ)
    (space : DiracMatterSpatialCoordinates) :=
  iteratedFDeriv ℝ order
    (fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates initialTime)
    space

theorem exists_fixedMatterCanonicalSourceInitialDerivativeBoundOnBox
    (order : ℕ)
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ space ∈ Icc a b,
        ‖fixedMatterCanonicalSourceInitialDerivative order initialTime space‖ ≤ C := by
  let derivative := iteratedFDeriv ℝ order
    (fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates initialTime)
  have derivativeContinuous : Continuous derivative := by
    exact
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_contDiff
        initialTime).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, bound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    derivativeContinuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro space spaceMem
  exact (bound space spaceMem).trans (le_max_left _ _)

theorem exists_fixedMatterFirstJetActionCoefficientDerivativeBoundOnBox
    (order : ℕ)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ time ∈ Icc timeStart timeEnd,
        ∀ space ∈ Icc a b,
          ‖fixedMatterFirstJetActionCoefficientDerivative order
            (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C := by
  let coefficientDerivative :=
    iteratedFDeriv ℝ order fixedMatterFirstJetActionCLM
  have derivativeContinuous : Continuous coefficientDerivative := by
    rw [continuous_iff_continuousAt]
    intro point
    exact fixedMatterFirstJetActionCLM_contDiff_infty.contDiffAt
      |>.continuousAt_iteratedFDeriv (by exact_mod_cast le_top)
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have restrictedContinuous : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates =>
      coefficientDerivative
        (diracMatterSpacetimeCoordinatePoint point.1 point.2)) :=
    derivativeContinuous.comp
      diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous
  obtain ⟨C, bound⟩ := carrierCompact.exists_bound_of_continuousOn
    restrictedContinuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro time timeMem space spaceMem
  exact (bound (time, space) ⟨timeMem, spaceMem⟩).trans
    (le_max_left _ _)

/-- One source-generated budget contains every derivative order needed by the
high-order symmetric-hyperbolic energy induction.  Neither the derivative
bounds nor a target solution enter as constructor inputs. -/
structure FixedMatterSymmetricHyperbolicAllOrderCoefficientBudget
    (initialTime timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) where
  actionBound : ℕ → ℝ
  actionBound_nonnegative : ∀ order, 0 ≤ actionBound order
  actionBound_spec : ∀ order,
    ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedMatterFirstJetActionCoefficientDerivative order
          (diracMatterSpacetimeCoordinatePoint time space)‖ ≤
            actionBound order
  initialBound : ℕ → ℝ
  initialBound_nonnegative : ∀ order, 0 ≤ initialBound order
  initialBound_spec : ∀ order,
    ∀ space ∈ Icc a b,
      ‖fixedMatterCanonicalSourceInitialDerivative order initialTime space‖ ≤
        initialBound order

/-- The fixed source itself selects the complete coefficient/initial-data
budget for every regularity order. -/
def fixedMatterSymmetricHyperbolicAllOrderCoefficientBudget
    (initialTime timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    FixedMatterSymmetricHyperbolicAllOrderCoefficientBudget
      initialTime timeStart timeEnd a b where
  actionBound := fun order => Classical.choose
    (exists_fixedMatterFirstJetActionCoefficientDerivativeBoundOnBox
      order timeStart timeEnd a b)
  actionBound_nonnegative := fun order =>
    (Classical.choose_spec
      (exists_fixedMatterFirstJetActionCoefficientDerivativeBoundOnBox
        order timeStart timeEnd a b)).1
  actionBound_spec := fun order =>
    (Classical.choose_spec
      (exists_fixedMatterFirstJetActionCoefficientDerivativeBoundOnBox
        order timeStart timeEnd a b)).2
  initialBound := fun order => Classical.choose
    (exists_fixedMatterCanonicalSourceInitialDerivativeBoundOnBox
      order initialTime a b)
  initialBound_nonnegative := fun order =>
    (Classical.choose_spec
      (exists_fixedMatterCanonicalSourceInitialDerivativeBoundOnBox
        order initialTime a b)).1
  initialBound_spec := fun order =>
    (Classical.choose_spec
      (exists_fixedMatterCanonicalSourceInitialDerivativeBoundOnBox
        order initialTime a b)).2

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCoefficients
