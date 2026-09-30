import H0mework.Arithmetic.RiemannSource.ThetaEulerOverlap
import H0mework.Arithmetic.PoleOrbit.GlobalGermArithmeticCounterterm
import H0mework.Arithmetic.MuntzAction.GaussianCoPoissonRelation
import H0mework.Arithmetic.RiemannSpectral.AdditiveFourierFixedSourceState

/-!
# One theta--Burnol action receipt

The global-germ owner generates one linear arithmetic counterterm.  Its
Gaussian evaluation is the exact theta pair already stored by the analytic
occurrence, through that pair's cofinal-fold equation.  Its reciprocal
annulus evaluation generates the additive co-sum and hence the nonzero
physical state.  Fourier symmetrization then gives the fixed state.

Thus theta and Burnol are sibling tests of one action, not two values attached
to a shared owner.  No zero, spectral coordinate, eigenvector, or kernel event
is stored here.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open RootedAccountedUnfolding ClozelEndpointSourceEffect
open scoped SchwartzMap

namespace ClozelGeneralizedDual.BurnolPhysicalState

open AllPlaceOriginDefect MeasureTheory Set

noncomputable section

/-- The owner action on a scaled Schwartz test is the existing Müntz scale
remainder.  This is the common evaluation gate used by both tests below. -/
theorem ownerArithmeticCounterterm_scaled_eq_scaleRemainder
    (owner : GlobalGermOwner) (test : SchwartzMap ℝ ℂ)
    {scale : ℝ} (positive : 0 < scale) :
    ownerArithmeticCounterterm owner
        (scaledSchwartzTest scale positive.ne' test) =
      coPoissonMuntzScaleRemainder test scale := by
  rw [ownerArithmeticCounterterm_eq_remainder]
  unfold coPoissonMuntzScaleRemainder
  rw [dif_pos positive]

/-- A weak FE pair commutes with an action when its positive Gaussian values
are exactly the action evaluations after the square-scale rechart. -/
def GaussianActionCommutingAt
    (action : SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ) (pair : WeakFEPair ℂ) : Prop :=
  ∀ (scale : ℝ) (positive : 0 < scale),
    action (scaledSchwartzTest scale positive.ne' clozelGaussianSchwartz) =
      pair.f (scale ^ 2) - 1 -
        ((scale ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))

/-- Exact receipt indexed by the analytic payload.  The additive state is
characterized almost everywhere by the same action whose Gaussian value is
the payload's cofinal theta fold. -/
structure GeneratedBurnolThetaCommonActionReceiptAt
    (analytic : AnalyticContinuationPayload) : Type 5 where
  private mk ::
  action : SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ
  action_eq : action = ownerArithmeticCounterterm analytic.1
  action_naturality : ∀ test, action test = clozelTemperedRemainder test
  thetaFoldRead : ∀ (t : ℝ), 0 < t →
    analytic.2.thetaPair.pair.f t =
      ((∑' stage,
        generatedRiemannThetaTerm analytic.1 t stage : ℝ) : ℂ)
  gaussianActionRead : GaussianActionCommutingAt action
    analytic.2.thetaPair.pair
  annulusActionRead : ∀ (t : ℝ) (positive : 0 < t),
    action (scaledSchwartzTest t⁻¹ (inv_ne_zero positive.ne')
        burnolEvenAnnulusSchwartz) =
      (((2 * t : ℝ) : ℂ) * burnolAdditiveCoSum t)
  additiveState :
    EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
  additiveState_ne_zero : (additiveState : BurnolL2) ≠ 0
  additiveStateActionRead :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ nonzero : t ≠ 0,
      (additiveState : BurnolL2) t =
        (((2 * |t| : ℝ) : ℂ)⁻¹ *
          action (scaledSchwartzTest |t|⁻¹
            (inv_ne_zero (abs_ne_zero.mpr nonzero))
            burnolEvenAnnulusSchwartz))
  fixedState :
    EvenBurnolFourierFixedCarrier burnolUnscaledCommonGapRadius
  fixedState_generated :
    fixedState.1 = (1 / 2 : ℂ) •
      (additiveState +
        evenFaceFourierEquiv burnolUnscaledCommonGapRadius additiveState)
  fixedState_ne_zero : fixedState ≠ 0

namespace GeneratedBurnolThetaCommonActionReceiptAt

def generate (analytic : AnalyticContinuationPayload) :
    GeneratedBurnolThetaCommonActionReceiptAt analytic where
  action := ownerArithmeticCounterterm analytic.1
  action_eq := rfl
  action_naturality := ownerArithmeticCounterterm_eq_remainder analytic.1
  thetaFoldRead := analytic.2.thetaPair.f_generated
  gaussianActionRead := by
    intro scale positive
    rw [ownerArithmeticCounterterm_scaled_eq_scaleRemainder
      analytic.1 clozelGaussianSchwartz positive]
    rw [coPoissonMuntzScaleRemainder_clozelGaussian analytic.1 positive]
    unfold generatedClozelGaussianRemainderKernel
    have generatedFold :=
      (GeneratedRiemannWeakFEPairAt.generate analytic.1).f_generated
        (scale ^ 2) (sq_pos_of_pos positive)
    have analyticFold := analytic.2.thetaPair.f_generated
      (scale ^ 2) (sq_pos_of_pos positive)
    rw [generatedFold, ← analyticFold]
  annulusActionRead := by
    intro t positive
    rw [ownerArithmeticCounterterm_scaled_eq_scaleRemainder
      analytic.1 burnolEvenAnnulusSchwartz (inv_pos.mpr positive)]
    exact coPoissonMuntzScaleRemainder_reciprocal_eq_additiveCoSum positive
  additiveState := burnolAdditiveEvenPhysicalState
  additiveState_ne_zero := burnolAdditiveActualNonzeroPhysicalState.2
  additiveStateActionRead := by
    filter_upwards [burnolAdditiveFullEvenL2_coeFn] with t stateRead
    intro nonzero
    have positive : 0 < |t| := abs_pos.mpr nonzero
    have additiveAbs : burnolAdditiveCoSum |t| = burnolAdditiveCoSum t := by
      rcases lt_or_ge t 0 with negative | nonnegative
      · rw [abs_of_neg negative, burnolAdditiveCoSum_even]
      · rw [abs_of_nonneg nonnegative]
    change burnolAdditiveFullEvenL2 t = _
    rw [stateRead]
    rw [ownerArithmeticCounterterm_scaled_eq_scaleRemainder
      analytic.1 burnolEvenAnnulusSchwartz (inv_pos.mpr positive)]
    rw [coPoissonMuntzScaleRemainder_reciprocal_eq_additiveCoSum positive,
      additiveAbs]
    have coefficientNe : (((2 * |t| : ℝ) : ℂ)) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (by norm_num) positive.ne')
    rw [← mul_assoc, inv_mul_cancel₀ coefficientNe, one_mul]
  fixedState := burnolAdditiveFourierFixedPhysicalState
  fixedState_generated := rfl
  fixedState_ne_zero := burnolAdditiveFourierFixedPhysicalState_ne_zero

/-- The action read determines the additive physical state almost everywhere;
an owner-dependent constant attachment cannot choose another state. -/
theorem additiveState_eq_of_actionRead
    {analytic : AnalyticContinuationPayload}
    (generated : GeneratedBurnolThetaCommonActionReceiptAt analytic)
    (candidate : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (candidateRead :
      ∀ᵐ t ∂(volume : Measure ℝ), ∀ nonzero : t ≠ 0,
        (candidate : BurnolL2) t =
          (((2 * |t| : ℝ) : ℂ)⁻¹ *
            generated.action (scaledSchwartzTest |t|⁻¹
              (inv_ne_zero (abs_ne_zero.mpr nonzero))
              burnolEvenAnnulusSchwartz))) :
    candidate = generated.additiveState := by
  apply Subtype.ext
  apply Lp.ext
  have almostEverywhereNeZero : ∀ᵐ t : ℝ ∂volume, t ≠ 0 :=
    compl_mem_ae_iff.mpr
      (Subsingleton.measure_zero (s := ({0} : Set ℝ)) (by simp) volume)
  filter_upwards [candidateRead, generated.additiveStateActionRead,
    almostEverywhereNeZero] with t left right nonzero
  exact (left nonzero).trans (right nonzero).symm

/-- Any replacement theta pair commuting with this action has the same
positive Gaussian coordinate as the analytic pair. -/
theorem replacementPair_f_eq_of_gaussianActionCommuting
    {analytic : AnalyticContinuationPayload}
    (generated : GeneratedBurnolThetaCommonActionReceiptAt analytic)
    (replacement : WeakFEPair ℂ)
    (commuting : GaussianActionCommutingAt generated.action replacement)
    {t : ℝ} (positive : 0 < t) :
    replacement.f t = analytic.2.thetaPair.pair.f t := by
  have sqrtPositive : 0 < Real.sqrt t := Real.sqrt_pos.2 positive
  have replacementRead := commuting (Real.sqrt t) sqrtPositive
  have sourceRead := generated.gaussianActionRead (Real.sqrt t) sqrtPositive
  rw [Real.sq_sqrt positive.le] at replacementRead sourceRead
  have equality := replacementRead.symm.trans sourceRead
  linear_combination equality

/-- Hostile: keeping the owner while changing one positive theta value cannot
preserve the common-action square. -/
theorem changedThetaPair_cannot_commute
    {analytic : AnalyticContinuationPayload}
    (generated : GeneratedBurnolThetaCommonActionReceiptAt analytic)
    (replacement : WeakFEPair ℂ)
    {t : ℝ} (positive : 0 < t)
    (changed : replacement.f t ≠ analytic.2.thetaPair.pair.f t) :
    ¬ GaussianActionCommutingAt generated.action replacement := by
  intro commuting
  exact changed
    (replacementPair_f_eq_of_gaussianActionCommuting
      generated replacement commuting positive)

end GeneratedBurnolThetaCommonActionReceiptAt

abbrev BurnolThetaCommonActionReceiptPayload :=
  Σ analytic : AnalyticContinuationPayload,
    GeneratedBurnolThetaCommonActionReceiptAt analytic

/-- The common-action receipt is a dependent face of the literal analytic
occurrence. -/
def generatedBurnolThetaCommonActionReceiptOccurrence :
    RootedAccountedUnfolding BurnolThetaCommonActionReceiptPayload :=
  generatedRiemannAnalyticContinuationOccurrence.map fun analytic ↦
    ⟨analytic, GeneratedBurnolThetaCommonActionReceiptAt.generate analytic⟩

theorem generatedBurnolThetaCommonActionReceiptOccurrence_projects :
    generatedBurnolThetaCommonActionReceiptOccurrence.map Sigma.fst =
      generatedRiemannAnalyticContinuationOccurrence := by
  rw [generatedBurnolThetaCommonActionReceiptOccurrence,
    RootedAccountedUnfolding.map_map]
  change generatedRiemannAnalyticContinuationOccurrence.map id =
    generatedRiemannAnalyticContinuationOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem generatedBurnolThetaCommonActionReceiptOccurrence_projects_to_seed :
    ((generatedBurnolThetaCommonActionReceiptOccurrence.map Sigma.fst).map
        Sigma.fst).map Prod.fst =
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence := by
  rw [generatedBurnolThetaCommonActionReceiptOccurrence_projects,
    generatedRiemannAnalyticContinuationOccurrence_projects,
    globalGermOccurrence_projects]

end
end ClozelGeneralizedDual.BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
