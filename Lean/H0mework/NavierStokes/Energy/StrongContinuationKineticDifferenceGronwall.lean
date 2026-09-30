import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.Order.Floor
import H0mework.NavierStokes.Energy.StrongContinuationDifferenceKineticWork
import H0mework.NavierStokes.Energy.WholeKineticMassSeparation
import H0mework.NavierStokes.Energy.WholeKineticDifferenceCancellation
import H0mework.NavierStokes.ShellSources.WholeReceiptSquareContinuation

/-!
# Whole kinetic-difference Grönwall and same-horizon uniqueness

This module closes the actual strong-continuation uniqueness consumer on the
complete three-dimensional Fourier carrier.  Its proof chain is:

* the source-generated whole negative-one tangent update;
* exact kinetic weighting of the complete nonzero-frequency difference;
* whole incompressible nonlinear cancellation and viscous absorption;
* the generated critical `L¹_t` velocity-majorant coefficient;
* exact coordinate energy transport and factorial integral Grönwall;
* equality of the two continuous whole vorticity paths on the common horizon.

The main theorem is
`strongContinuationReceipt_wholePath_unique`.  Its mouth contains two actual
receipts generated from the same lineage and physical horizon; it contains no
target equality, finite-frequency cutoff, tail-silence witness, continuation
endpoint, or caller-supplied Grönwall coefficient.

The module is deliberately kept as one long consumer because the real/complex
`ℓ²` bridge, the whole viscous pairing, the actual time-update identity, and
the final Grönwall inequality share dependent summability and representative
proofs.  Splitting those proofs before this API stabilizes would duplicate the
same provenance boundary across several modules.  This is a consumer theorem,
not a new Navier--Stokes source producer or a claim of global regularity.
-/

open Set Filter MeasureTheory Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall

open SaturationMonoid.NavierStokes
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger

private theorem commonTimeMeasure_eq_comap_volume
    (requestedTime : ℝ) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ)
        volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

theorem commonTimeZeroExtension_intervalIntegrable_of_integrable
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (value : Icc (0 : ℝ) requestedTime → E)
    (valueIntegrable :
      Integrable value (commonTimeMeasure requestedTime)) :
    IntervalIntegrable
      (commonTimeZeroExtension requestedTime value)
      volume 0 requestedTime := by
  rw [
    intervalIntegrable_iff_integrableOn_Icc_of_le
      requestedTimeNonneg,
    integrableOn_iff_comap_subtypeVal measurableSet_Icc]
  have measureEq :
      commonTimeMeasure requestedTime =
        Measure.comap
          (Subtype.val :
            Icc (0 : ℝ) requestedTime → ℝ)
          volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  rw [← measureEq]
  apply valueIntegrable.congr
  filter_upwards with time
  simp only [Function.comp_apply]
  rw [commonTimeZeroExtension_of_mem
    requestedTime value time.1 time.property]

private def primitive (coefficient : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  fun t => ∫ s in a..t, coefficient s

private theorem primitive_pow_absolutelyContinuousOnInterval
    {coefficient : ℝ → ℝ} {a b : ℝ}
    (coefficientIntegrable :
      IntervalIntegrable coefficient volume a b) :
    ∀ n : ℕ,
      AbsolutelyContinuousOnInterval
        (fun t => primitive coefficient a t ^ n) a b := by
  intro n
  induction n with
  | zero =>
      simpa using
        (LipschitzWith.const
          (α := ℝ) (β := ℝ) (1 : ℝ))
          |>.lipschitzOnWith
          |>.absolutelyContinuousOnInterval
  | succ n inductionHypothesis =>
      have productAC :=
        inductionHypothesis.mul
          (coefficientIntegrable
            |>.absolutelyContinuousOnInterval_intervalIntegral
              (c := a) (by simp))
      change
        AbsolutelyContinuousOnInterval
          (fun t =>
            primitive coefficient a t ^ n *
              primitive coefficient a t) a b at productAC
      simpa only [pow_succ] using productAC

private theorem integral_coefficient_mul_primitive_pow
    {coefficient : ℝ → ℝ} {a b t : ℝ}
    (ab : a ≤ b)
    (timeMem : t ∈ Icc a b)
    (coefficientIntegrable :
      IntervalIntegrable coefficient volume a b)
    (n : ℕ) :
    (∫ s in a..t,
        coefficient s * primitive coefficient a s ^ n) =
      primitive coefficient a t ^ (n + 1) / (n + 1) := by
  have intervalSubset :
      uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le timeMem.1, uIcc_of_le ab]
    exact Icc_subset_Icc le_rfl timeMem.2
  have coefficientIntegrableAt :
      IntervalIntegrable coefficient volume a t :=
    coefficientIntegrable.mono_set intervalSubset
  have primitiveDerivative :
      ∀ᵐ s : ℝ,
        s ∈ uIcc a t →
          HasDerivAt
            (primitive coefficient a)
            (coefficient s) s := by
    filter_upwards [
      coefficientIntegrableAt.ae_hasDerivAt_integral] with
        s derivative timeMembership
    exact derivative timeMembership a (by simp)
  have powerDerivative :
      ∀ᵐ s : ℝ,
        s ∈ uIcc a t →
          HasDerivAt
            (fun actual =>
              primitive coefficient a actual ^ (n + 1))
            (((n : ℝ) + 1) *
              primitive coefficient a s ^ n *
              coefficient s) s := by
    filter_upwards [primitiveDerivative] with
        s derivative timeMembership
    simpa only [Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel] using
      (derivative timeMembership).fun_pow (n + 1)
  have powerAC :
      AbsolutelyContinuousOnInterval
        (fun actual =>
          primitive coefficient a actual ^ (n + 1)) a t :=
    (primitive_pow_absolutelyContinuousOnInterval
      coefficientIntegrableAt (n + 1))
  have derivativeIntegral :=
    powerAC.integral_deriv_eq_sub
  have exactDerivativeIntegral :
      (∫ s in a..t,
          ((n : ℝ) + 1) *
            primitive coefficient a s ^ n *
            coefficient s) =
        primitive coefficient a t ^ (n + 1) := by
    calc
      (∫ s in a..t,
          ((n : ℝ) + 1) *
            primitive coefficient a s ^ n *
            coefficient s) =
          ∫ s in a..t,
            deriv
              (fun actual =>
                primitive coefficient a actual ^ (n + 1)) s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [powerDerivative] with
            s derivative timeMembership
        exact
          (derivative
            (uIoc_subset_uIcc timeMembership)).deriv.symm
      _ =
          primitive coefficient a t ^ (n + 1) -
            primitive coefficient a a ^ (n + 1) :=
        derivativeIntegral
      _ = primitive coefficient a t ^ (n + 1) := by
        simp [primitive]
  have castPos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc
    (∫ s in a..t,
        coefficient s * primitive coefficient a s ^ n) =
        (((n : ℝ) + 1) *
          ∫ s in a..t,
            coefficient s * primitive coefficient a s ^ n) /
          ((n : ℝ) + 1) := by
      field_simp [ne_of_gt castPos]
    _ =
        (∫ s in a..t,
          ((n : ℝ) + 1) *
            (coefficient s *
              primitive coefficient a s ^ n)) /
          ((n : ℝ) + 1) := by
      rw [intervalIntegral.integral_const_mul]
    _ =
        primitive coefficient a t ^ (n + 1) /
          ((n : ℝ) + 1) := by
      rw [show
        (fun s =>
          ((n : ℝ) + 1) *
            (coefficient s *
              primitive coefficient a s ^ n)) =
          fun s =>
            ((n : ℝ) + 1) *
              primitive coefficient a s ^ n *
              coefficient s by
        funext s
        ring,
        exactDerivativeIntegral]

/--
Zero-initial integral Grönwall for a merely integrable nonnegative
coefficient.  No continuous or essentially bounded coefficient is needed.
-/
theorem eq_zero_of_nonneg_le_integral_mul
    {coefficient value : ℝ → ℝ}
    {a b bound : ℝ}
    (ab : a ≤ b)
    (coefficientIntegrable :
      IntervalIntegrable coefficient volume a b)
    (coefficientNonneg :
      ∀ t ∈ Icc a b, 0 ≤ coefficient t)
    (valueContinuous : ContinuousOn value (Icc a b))
    (valueNonneg : ∀ t ∈ Icc a b, 0 ≤ value t)
    (valueLeBound : ∀ t ∈ Icc a b, value t ≤ bound)
    (evolution :
      ∀ t ∈ Icc a b,
        value t ≤
          ∫ s in a..t, coefficient s * value s) :
    ∀ t ∈ Icc a b, value t = 0 := by
  intro t timeMem
  have boundNonneg : 0 ≤ bound :=
    (valueNonneg a ⟨le_rfl, ab⟩).trans
      (valueLeBound a ⟨le_rfl, ab⟩)
  let cumulative := primitive coefficient a
  have cumulativeNonneg :
      ∀ s ∈ Icc a b, 0 ≤ cumulative s := by
    intro s sMem
    exact intervalIntegral.integral_nonneg sMem.1
      (fun u uMem => coefficientNonneg u
        ⟨uMem.1, uMem.2.trans sMem.2⟩)
  have factorialBound :
      ∀ n : ℕ, ∀ s ∈ Icc a b,
        value s ≤
          bound * cumulative s ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
        intro s sMem
        simpa using valueLeBound s sMem
    | succ n inductionHypothesis =>
        intro s sMem
        have subintervalSubset :
            uIcc a s ⊆ uIcc a b := by
          rw [uIcc_of_le sMem.1, uIcc_of_le ab]
          exact Icc_subset_Icc le_rfl sMem.2
        have integrableProduct :
            IntervalIntegrable
              (fun u => coefficient u * value u)
              volume a s := by
          exact
            (coefficientIntegrable.mono_set
              subintervalSubset)
              |>.mul_continuousOn <| by
                rw [uIcc_of_le sMem.1]
                exact
                  valueContinuous.mono
                    (Icc_subset_Icc le_rfl sMem.2)
        calc
          value s ≤
              ∫ u in a..s, coefficient u * value u :=
            evolution s sMem
          _ ≤
              ∫ u in a..s,
                coefficient u *
                  (bound * cumulative u ^ n /
                    (n.factorial : ℝ)) := by
            apply intervalIntegral.integral_mono_on
            · exact sMem.1
            · exact integrableProduct
            · exact
                (coefficientIntegrable.mono_set
                  subintervalSubset)
                  |>.mul_continuousOn <| by
                    have primitiveContinuous :
                        ContinuousOn cumulative (uIcc a s) := by
                      change
                        ContinuousOn
                          (fun x =>
                            ∫ v in a..x, coefficient v)
                          (uIcc a s)
                      exact
                        (coefficientIntegrable.mono_set
                          subintervalSubset)
                          |>.absolutelyContinuousOnInterval_intervalIntegral
                            (c := a) (by simp)
                          |>.continuousOn
                    exact
                      (continuousOn_const.mul
                        (primitiveContinuous.pow n))
                        |>.div_const _
            · intro u uMem
              exact mul_le_mul_of_nonneg_left
                (inductionHypothesis u
                  ⟨uMem.1, uMem.2.trans sMem.2⟩)
                (coefficientNonneg u
                  ⟨uMem.1, uMem.2.trans sMem.2⟩)
          _ =
              bound / (n.factorial : ℝ) *
                ∫ u in a..s,
                  coefficient u * cumulative u ^ n := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro u uMem
            ring
          _ =
              bound / (n.factorial : ℝ) *
                (cumulative s ^ (n + 1) /
                  ((n : ℝ) + 1)) := by
            simpa only [cumulative, Nat.cast_add,
              Nat.cast_one] using congrArg
                (fun value =>
                  bound / (n.factorial : ℝ) * value)
                (integral_coefficient_mul_primitive_pow
                  ab sMem coefficientIntegrable n)
          _ =
              bound * cumulative s ^ (n + 1) /
                ((n + 1).factorial : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            field_simp
  have tendsZero :
      Tendsto
        (fun n : ℕ =>
          bound * cumulative t ^ n / (n.factorial : ℝ))
        atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero, mul_div_assoc] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop
        (cumulative t)).const_mul bound
  have valueLeZero :
      value t ≤ 0 :=
    ge_of_tendsto tendsZero
      (Filter.Eventually.of_forall fun n =>
        factorialBound n t timeMem)
  exact le_antisymm valueLeZero (valueNonneg t timeMem)

/--
Nonzero-initial integral Grönwall for a merely integrable nonnegative
coefficient.  This is the inhomogeneous companion to
`eq_zero_of_nonneg_le_integral_mul`; it uses the same factorial iteration and
does not replace the actual coefficient by a supplied uniform ceiling.
-/
theorem le_initial_mul_exp_of_nonneg_le_initial_add_integral_mul
    {coefficient value : ℝ → ℝ}
    {a b initial bound : ℝ}
    (ab : a ≤ b)
    (coefficientIntegrable :
      IntervalIntegrable coefficient volume a b)
    (coefficientNonneg :
      ∀ t ∈ Icc a b, 0 ≤ coefficient t)
    (valueContinuous : ContinuousOn value (Icc a b))
    (valueLeBound : ∀ t ∈ Icc a b, value t ≤ bound)
    (evolution :
      ∀ t ∈ Icc a b,
        value t ≤ initial +
          ∫ s in a..t, coefficient s * value s) :
    ∀ t ∈ Icc a b,
      value t ≤
        initial * Real.exp (∫ s in a..t, coefficient s) := by
  intro t timeMem
  let cumulative := primitive coefficient a
  have cumulativeNonneg :
      ∀ s ∈ Icc a b, 0 ≤ cumulative s := by
    intro s sMem
    exact intervalIntegral.integral_nonneg sMem.1
      (fun u uMem => coefficientNonneg u
        ⟨uMem.1, uMem.2.trans sMem.2⟩)
  have partialIntegral :
      ∀ n : ℕ, ∀ s ∈ Icc a b,
        (∫ u in a..s,
            coefficient u *
              (∑ k ∈ Finset.range n,
                cumulative u ^ k / (k.factorial : ℝ))) =
          ∑ k ∈ Finset.range n,
            cumulative s ^ (k + 1) /
              ((k + 1).factorial : ℝ) := by
    intro n s sMem
    have subintervalSubset :
        uIcc a s ⊆ uIcc a b := by
      rw [uIcc_of_le sMem.1, uIcc_of_le ab]
      exact Icc_subset_Icc le_rfl sMem.2
    have coefficientIntegrableAt :
        IntervalIntegrable coefficient volume a s :=
      coefficientIntegrable.mono_set subintervalSubset
    have primitiveContinuous :
        ContinuousOn cumulative (uIcc a s) := by
      change ContinuousOn
        (fun x => ∫ v in a..x, coefficient v) (uIcc a s)
      exact
        coefficientIntegrableAt
          |>.absolutelyContinuousOnInterval_intervalIntegral
            (c := a) (by simp)
          |>.continuousOn
    rw [show
      (fun u =>
        coefficient u *
          (∑ k ∈ Finset.range n,
            cumulative u ^ k / (k.factorial : ℝ))) =
        fun u =>
          ∑ k ∈ Finset.range n,
            coefficient u *
              (cumulative u ^ k / (k.factorial : ℝ)) by
      funext u
      rw [Finset.mul_sum]]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k _kMem
      calc
        (∫ u in a..s,
            coefficient u *
              (cumulative u ^ k / (k.factorial : ℝ))) =
            (1 / (k.factorial : ℝ)) *
              ∫ u in a..s,
                coefficient u * cumulative u ^ k := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro u _uMem
          ring
        _ = (1 / (k.factorial : ℝ)) *
              (cumulative s ^ (k + 1) / ((k : ℝ) + 1)) := by
          rw [integral_coefficient_mul_primitive_pow
            ab sMem coefficientIntegrable k]
        _ = cumulative s ^ (k + 1) /
              ((k + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp
    · intro k _kMem
      exact coefficientIntegrableAt.mul_continuousOn
        ((primitiveContinuous.pow k).div_const _)
  have factorialBound :
      ∀ n : ℕ, ∀ s ∈ Icc a b,
        value s ≤
          initial *
              (∑ k ∈ Finset.range n,
                cumulative s ^ k / (k.factorial : ℝ)) +
            bound * cumulative s ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
        intro s sMem
        simpa using valueLeBound s sMem
    | succ n inductionHypothesis =>
        intro s sMem
        have subintervalSubset :
            uIcc a s ⊆ uIcc a b := by
          rw [uIcc_of_le sMem.1, uIcc_of_le ab]
          exact Icc_subset_Icc le_rfl sMem.2
        have coefficientIntegrableAt :
            IntervalIntegrable coefficient volume a s :=
          coefficientIntegrable.mono_set subintervalSubset
        have integrableProduct :
            IntervalIntegrable
              (fun u => coefficient u * value u)
              volume a s := by
          exact coefficientIntegrableAt.mul_continuousOn <| by
            rw [uIcc_of_le sMem.1]
            exact valueContinuous.mono
              (Icc_subset_Icc le_rfl sMem.2)
        have primitiveContinuous :
            ContinuousOn cumulative (uIcc a s) := by
          change ContinuousOn
            (fun x => ∫ v in a..x, coefficient v) (uIcc a s)
          exact
            coefficientIntegrableAt
              |>.absolutelyContinuousOnInterval_intervalIntegral
                (c := a) (by simp)
              |>.continuousOn
        have partialContinuous :
            ContinuousOn
              (fun u =>
                ∑ k ∈ Finset.range n,
                  cumulative u ^ k / (k.factorial : ℝ))
              (uIcc a s) := by
          apply continuousOn_finsetSum
          intro k _kMem
          exact (primitiveContinuous.pow k).div_const _
        have upperContinuous :
            ContinuousOn
              (fun u =>
                initial *
                    (∑ k ∈ Finset.range n,
                      cumulative u ^ k / (k.factorial : ℝ)) +
                  bound * cumulative u ^ n / (n.factorial : ℝ))
              (uIcc a s) := by
          exact
            (continuousOn_const.mul partialContinuous).add
              ((continuousOn_const.mul (primitiveContinuous.pow n)).div_const _)
        have upperProductIntegrable :
            IntervalIntegrable
              (fun u =>
                coefficient u *
                  (initial *
                      (∑ k ∈ Finset.range n,
                        cumulative u ^ k / (k.factorial : ℝ)) +
                    bound * cumulative u ^ n / (n.factorial : ℝ)))
              volume a s :=
          coefficientIntegrableAt.mul_continuousOn upperContinuous
        have tailIntegral :
            (∫ u in a..s,
                coefficient u *
                  (bound * cumulative u ^ n /
                    (n.factorial : ℝ))) =
              bound * cumulative s ^ (n + 1) /
                ((n + 1).factorial : ℝ) := by
          calc
            (∫ u in a..s,
                coefficient u *
                  (bound * cumulative u ^ n /
                    (n.factorial : ℝ))) =
                (bound / (n.factorial : ℝ)) *
                  ∫ u in a..s,
                    coefficient u * cumulative u ^ n := by
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro u _uMem
              ring
            _ = (bound / (n.factorial : ℝ)) *
                  (cumulative s ^ (n + 1) / ((n : ℝ) + 1)) := by
              rw [integral_coefficient_mul_primitive_pow
                ab sMem coefficientIntegrable n]
            _ = bound * cumulative s ^ (n + 1) /
                  ((n + 1).factorial : ℝ) := by
              rw [Nat.factorial_succ]
              push_cast
              field_simp
        calc
          value s ≤
              initial +
                ∫ u in a..s, coefficient u * value u :=
            evolution s sMem
          _ ≤ initial +
                ∫ u in a..s,
                  coefficient u *
                    (initial *
                        (∑ k ∈ Finset.range n,
                          cumulative u ^ k / (k.factorial : ℝ)) +
                      bound * cumulative u ^ n /
                        (n.factorial : ℝ)) := by
            exact add_le_add le_rfl <|
              intervalIntegral.integral_mono_on sMem.1
                integrableProduct upperProductIntegrable
                (fun u uMem =>
                  mul_le_mul_of_nonneg_left
                    (inductionHypothesis u
                      ⟨uMem.1, uMem.2.trans sMem.2⟩)
                    (coefficientNonneg u
                      ⟨uMem.1, uMem.2.trans sMem.2⟩))
          _ = initial *
                  (∑ k ∈ Finset.range (n + 1),
                    cumulative s ^ k / (k.factorial : ℝ)) +
                bound * cumulative s ^ (n + 1) /
                  ((n + 1).factorial : ℝ) := by
            rw [show
              (fun u =>
                coefficient u *
                  (initial *
                      (∑ k ∈ Finset.range n,
                        cumulative u ^ k / (k.factorial : ℝ)) +
                    bound * cumulative u ^ n /
                      (n.factorial : ℝ))) =
                fun u =>
                  initial *
                      (coefficient u *
                        (∑ k ∈ Finset.range n,
                          cumulative u ^ k / (k.factorial : ℝ))) +
                    coefficient u *
                      (bound * cumulative u ^ n /
                        (n.factorial : ℝ)) by
              funext u
              ring]
            rw [intervalIntegral.integral_add]
            · rw [intervalIntegral.integral_const_mul,
                partialIntegral n s sMem, tailIntegral,
                Finset.sum_range_succ']
              simp only [Nat.factorial_zero, Nat.cast_one, pow_zero,
                div_one]
              ring
            · exact coefficientIntegrableAt.mul_continuousOn
                partialContinuous |>.const_mul initial
            · exact coefficientIntegrableAt.mul_continuousOn
                ((continuousOn_const.mul
                    (primitiveContinuous.pow n)).div_const _)
  have partialTends :
      Tendsto
        (fun n : ℕ =>
          ∑ k ∈ Finset.range n,
            cumulative t ^ k / (k.factorial : ℝ))
        atTop (𝓝 (Real.exp (cumulative t))) := by
    rw [Real.exp_eq_exp_ℝ]
    have radiusMem :
        cumulative t ∈ Metric.eball (0 : ℝ)
          (NormedSpace.expSeries ℚ ℝ).radius := by
      rw [NormedSpace.expSeries_radius_eq_top]
      exact edist_lt_top _ _
    exact
      (NormedSpace.expSeries_div_hasSum_exp_of_mem_ball
        (𝕂 := ℚ) (cumulative t) radiusMem).tendsto_sum_nat
  have tailTends :
      Tendsto
        (fun n : ℕ =>
          bound * cumulative t ^ n / (n.factorial : ℝ))
        atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero, mul_div_assoc] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop
        (cumulative t)).const_mul bound
  have totalTends :
      Tendsto
        (fun n : ℕ =>
          initial *
              (∑ k ∈ Finset.range n,
                cumulative t ^ k / (k.factorial : ℝ)) +
            bound * cumulative t ^ n / (n.factorial : ℝ))
        atTop (𝓝 (initial * Real.exp (cumulative t))) := by
    simpa using (partialTends.const_mul initial).add tailTends
  exact ge_of_tendsto totalTends
    (Filter.Eventually.of_forall fun n =>
      factorialBound n t timeMem)

theorem
    absolutelyContinuousOnInterval_real_inner
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    {left right : ℝ → H}
    {a b : ℝ}
    (leftAC : AbsolutelyContinuousOnInterval left a b)
    (rightAC : AbsolutelyContinuousOnInterval right a b) :
    AbsolutelyContinuousOnInterval
      (fun time => ⟪left time, right time⟫_ℝ) a b := by
  obtain ⟨leftBound, leftLe⟩ := leftAC.exists_bound
  obtain ⟨rightBound, rightLe⟩ := rightAC.exists_bound
  rw [absolutelyContinuousOnInterval_iff] at leftAC rightAC ⊢
  intro ε εPos
  have denominatorPos :
      0 < |leftBound| + |rightBound| + 1 := by positivity
  have twoDenominatorPos :
      0 < 2 * (|leftBound| + |rightBound| + 1) :=
    mul_pos (by norm_num) denominatorPos
  obtain ⟨leftDelta, leftDeltaPos, leftControl⟩ :=
    leftAC
      (ε / (2 * (|leftBound| + |rightBound| + 1)))
      (div_pos εPos twoDenominatorPos)
  obtain ⟨rightDelta, rightDeltaPos, rightControl⟩ :=
    rightAC
      (ε / (2 * (|leftBound| + |rightBound| + 1)))
      (div_pos εPos twoDenominatorPos)
  refine
    ⟨min leftDelta rightDelta,
      lt_min leftDeltaPos rightDeltaPos,
      fun intervals intervalsWithin totalLengthLt => ?_⟩
  have leftTotalLt :
      ∑ index ∈ Finset.range intervals.1,
          dist (intervals.2 index).1 (intervals.2 index).2 <
        leftDelta :=
    totalLengthLt.trans_le (min_le_left _ _)
  have rightTotalLt :
      ∑ index ∈ Finset.range intervals.1,
          dist (intervals.2 index).1 (intervals.2 index).2 <
        rightDelta :=
    totalLengthLt.trans_le (min_le_right _ _)
  have leftVariation :=
    leftControl intervals intervalsWithin leftTotalLt
  have rightVariation :=
    rightControl intervals intervalsWithin rightTotalLt
  have leftBoundNonneg :
      0 ≤ |leftBound| := abs_nonneg _
  have rightBoundNonneg :
      0 ≤ |rightBound| := abs_nonneg _
  calc
    ∑ index ∈ Finset.range intervals.1,
        dist
          ⟪left (intervals.2 index).1,
            right (intervals.2 index).1⟫_ℝ
          ⟪left (intervals.2 index).2,
            right (intervals.2 index).2⟫_ℝ ≤
        ∑ index ∈ Finset.range intervals.1,
          (|leftBound| *
              dist
                (right (intervals.2 index).1)
                (right (intervals.2 index).2) +
            |rightBound| *
              dist
                (left (intervals.2 index).1)
                (left (intervals.2 index).2)) := by
      apply Finset.sum_le_sum
      intro index indexMem
      have firstMem := (intervalsWithin.1 index indexMem).1
      have secondMem := (intervalsWithin.1 index indexMem).2
      rw [Real.dist_eq]
      have split :
          ⟪left (intervals.2 index).1,
              right (intervals.2 index).1⟫_ℝ -
              ⟪left (intervals.2 index).2,
                right (intervals.2 index).2⟫_ℝ =
            ⟪left (intervals.2 index).1,
              right (intervals.2 index).1 -
                right (intervals.2 index).2⟫_ℝ +
            ⟪left (intervals.2 index).1 -
                left (intervals.2 index).2,
              right (intervals.2 index).2⟫_ℝ := by
        rw [inner_sub_right, inner_sub_left]
        ring
      rw [split]
      calc
        |⟪left (intervals.2 index).1,
              right (intervals.2 index).1 -
                right (intervals.2 index).2⟫_ℝ +
            ⟪left (intervals.2 index).1 -
                left (intervals.2 index).2,
              right (intervals.2 index).2⟫_ℝ| ≤
            |⟪left (intervals.2 index).1,
              right (intervals.2 index).1 -
                right (intervals.2 index).2⟫_ℝ| +
            |⟪left (intervals.2 index).1 -
                left (intervals.2 index).2,
              right (intervals.2 index).2⟫_ℝ| :=
          abs_add_le _ _
        _ ≤
            ‖left (intervals.2 index).1‖ *
                ‖right (intervals.2 index).1 -
                  right (intervals.2 index).2‖ +
              ‖left (intervals.2 index).1 -
                  left (intervals.2 index).2‖ *
                ‖right (intervals.2 index).2‖ :=
          add_le_add
            (abs_real_inner_le_norm _ _)
            (abs_real_inner_le_norm _ _)
        _ ≤
            |leftBound| *
                dist
                  (right (intervals.2 index).1)
                  (right (intervals.2 index).2) +
              |rightBound| *
                dist
                  (left (intervals.2 index).1)
                  (left (intervals.2 index).2) := by
          rw [dist_eq_norm, dist_eq_norm]
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              ((leftLe _ firstMem).trans
                (le_abs_self leftBound))
              (norm_nonneg _))
            (by
              rw [mul_comm]
              exact
                mul_le_mul_of_nonneg_right
                  ((rightLe _ secondMem).trans
                    (le_abs_self rightBound))
                  (norm_nonneg _))
    _ =
        |leftBound| *
            (∑ index ∈ Finset.range intervals.1,
              dist
                (right (intervals.2 index).1)
                (right (intervals.2 index).2)) +
          |rightBound| *
            (∑ index ∈ Finset.range intervals.1,
              dist
                (left (intervals.2 index).1)
                (left (intervals.2 index).2)) := by
      rw [Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum]
    _ ≤
        |leftBound| *
            (ε / (2 * (|leftBound| + |rightBound| + 1))) +
          |rightBound| *
            (ε / (2 * (|leftBound| + |rightBound| + 1))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left rightVariation.le
          leftBoundNonneg)
        (mul_le_mul_of_nonneg_left leftVariation.le
          rightBoundNonneg)
    _ < ε := by
      have boundSumLt :
          |leftBound| + |rightBound| <
            |leftBound| + |rightBound| + 1 := by linarith
      calc
          |leftBound| *
              (ε / (2 * (|leftBound| + |rightBound| + 1))) +
            |rightBound| *
              (ε / (2 * (|leftBound| + |rightBound| + 1))) =
          (|leftBound| + |rightBound|) *
            (ε /
              (2 * (|leftBound| + |rightBound| + 1))) := by ring
        _ <
            (|leftBound| + |rightBound| + 1) *
              (ε /
                (2 * (|leftBound| + |rightBound| + 1))) :=
          mul_lt_mul_of_pos_right boundSumLt
            (div_pos εPos
              twoDenominatorPos)
        _ = ε / 2 := by field_simp
        _ < ε := by linarith

theorem
    AbsolutelyContinuousOnInterval.norm_sq_energy_identity
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    {path tangent : ℝ → H}
    {a b : ℝ}
    (pathAC : AbsolutelyContinuousOnInterval path a b)
    (pathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ uIcc a b →
          HasDerivAt path (tangent time) time) :
    (∫ time in a..b,
        2 * ⟪path time, tangent time⟫_ℝ) =
      ‖path b‖ ^ 2 - ‖path a‖ ^ 2 := by
  have energyAC :
      AbsolutelyContinuousOnInterval
        (fun time => ‖path time‖ ^ 2) a b := by
    simpa only [real_inner_self_eq_norm_sq] using
      absolutelyContinuousOnInterval_real_inner pathAC pathAC
  calc
    (∫ time in a..b,
        2 * ⟪path time, tangent time⟫_ℝ) =
        ∫ time in a..b,
          deriv (fun actual => ‖path actual‖ ^ 2) time := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [pathDerivative] with
          time derivative timeMem
      exact
        ((derivative
          (uIoc_subset_uIcc timeMem)).norm_sq).deriv.symm
    _ = ‖path b‖ ^ 2 - ‖path a‖ ^ 2 :=
      energyAC.integral_deriv_eq_sub

open SaturationMonoid.NavierStokes.ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open SaturationMonoid.NavierStokes.ThreeDimensionalPeriodicCoarseFilterCore
open SaturationMonoid.NavierStokes.ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open SaturationMonoid.NavierStokes.ThreeDimensionalIntegerLatticeCriticalKernel
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientRawSourceCore
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildPhysicalLimit
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEnergy
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEquation
open SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory

section ActualCoefficient

variable
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}

/-- The actual source-generated critical coefficient in the difference
energy inequality, extended by zero only outside the physical horizon. -/
def actualDifferenceSerrinCoefficient
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ℝ → ℝ :=
  commonTimeZeroExtension requestedTime fun time =>
    ν.coeff⁻¹ *
      wholeStateVelocityMajorant
        ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ
          receipt.wholePath) time) ^ 2

theorem actualDifferenceSerrinCoefficient_intervalIntegrable
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    IntervalIntegrable
      (actualDifferenceSerrinCoefficient receipt)
      volume 0 requestedTime := by
  apply commonTimeZeroExtension_intervalIntegrable_of_integrable
    requestedTime requestedTimePos.le
  exact
    receipt.wholePath_velocityMajorantSq_integrable.const_mul
      ν.coeff⁻¹

theorem actualDifferenceSerrinCoefficient_nonneg
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    0 ≤ actualDifferenceSerrinCoefficient receipt time := by
  rw [actualDifferenceSerrinCoefficient,
    commonTimeZeroExtension_of_mem
      requestedTime _ time timeMem]
  exact
    mul_nonneg
      (inv_nonneg.mpr ν.coeff_pos.le)
      (sq_nonneg _)

/--
The coefficient's complete time occupation is paid by the source-generated
critical Serrin budget, with the kinetic difference equation contributing
exactly one inverse viscosity.
-/
theorem actualDifferenceSerrinCoefficient_integral_le_generated
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    (∫ time in (0 : ℝ)..requestedTime,
        actualDifferenceSerrinCoefficient receipt time) ≤
      ν.coeff⁻¹ *
        (3 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          (((1 / 2 : ℝ) *
              criticalCoefficientEnstrophyCeiling ν θ) /
            criticalEnstrophyAbsorptionCoefficient θ ν)) := by
  calc
    (∫ time in (0 : ℝ)..requestedTime,
        actualDifferenceSerrinCoefficient receipt time) =
        ∫ time : Icc (0 : ℝ) requestedTime,
          actualDifferenceSerrinCoefficient receipt time.1
          ∂(commonTimeMeasure requestedTime) := by
      symm
      exact
        commonTime_integral_eq_intervalIntegral
          requestedTime requestedTimePos.le
          (actualDifferenceSerrinCoefficient receipt)
    _ =
        ν.coeff⁻¹ *
          ∫ time : Icc (0 : ℝ) requestedTime,
            wholeStateVelocityMajorant
              ((BoundedContinuousFunction.toLp 2
                (commonTimeMeasure requestedTime) ℂ
                receipt.wholePath) time) ^ 2
            ∂(commonTimeMeasure requestedTime) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with time
      rw [actualDifferenceSerrinCoefficient,
        commonTimeZeroExtension_of_mem
          requestedTime _ time.1 time.property]
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        receipt.wholePath_velocityMajorantSq_integral_le_generated
        (inv_nonneg.mpr ν.coeff_pos.le)

/--
The complete kinetic mass of the two actual paths, extended by zero only
outside their physical time horizon.
-/
def actualDifferenceKineticMass
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ℝ → ℝ :=
  commonTimeZeroExtension requestedTime fun time =>
    puncturedWholeVorticityKineticMass
      (left.wholePath time - right.wholePath time)

@[simp] theorem actualDifferenceKineticMass_of_mem
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    actualDifferenceKineticMass left right time =
      puncturedWholeVorticityKineticMass
        (left.wholePath ⟨time, timeMem⟩ -
          right.wholePath ⟨time, timeMem⟩) := by
  rw [actualDifferenceKineticMass,
    commonTimeZeroExtension_of_mem
      requestedTime _ time timeMem]

theorem actualDifferenceKineticMass_nonneg
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    0 ≤ actualDifferenceKineticMass left right time := by
  rw [actualDifferenceKineticMass_of_mem
    left right time timeMem]
  exact puncturedWholeVorticityKineticMass_nonneg _

theorem actualDifferenceKineticMass_continuousOn
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ContinuousOn
      (actualDifferenceKineticMass left right)
      (Icc (0 : ℝ) requestedTime) := by
  rw [continuousOn_iff_continuous_restrict]
  have pathContinuous :
      Continuous fun time : Icc (0 : ℝ) requestedTime =>
        left.wholePath time - right.wholePath time :=
    left.wholePath.continuous.sub right.wholePath.continuous
  have massContinuous :
      Continuous fun time : Icc (0 : ℝ) requestedTime =>
        puncturedWholeVorticityKineticMass
          (left.wholePath time - right.wholePath time) :=
    continuous_puncturedWholeVorticityKineticMass.comp
      pathContinuous
  convert massContinuous using 1
  funext time
  exact actualDifferenceKineticMass_of_mem
    left right time.1 time.2

/--
Continuity on the compact physical interval generates the uniform bound
needed by the factorial Grönwall iteration; it is not supplied as a
certificate.
-/
theorem actualDifferenceKineticMass_bounded
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∃ bound : ℝ,
      ∀ time ∈ Icc (0 : ℝ) requestedTime,
        actualDifferenceKineticMass left right time ≤ bound := by
  obtain ⟨bound, boundUpper⟩ :=
    isCompact_Icc.bddAbove_image
      (actualDifferenceKineticMass_continuousOn left right)
  exact ⟨bound, fun time timeMem =>
    boundUpper (mem_image_of_mem _ timeMem)⟩

/--
The continuous actual path and the source-owned transverse weak state are
the same common-time representative almost everywhere.
-/
theorem wholePath_eq_transverseLimit_ae
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      receipt.wholePath time =
        (receipt.transverseLimit time).1 := by
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ receipt.wholePath
  have inclusionAE :=
    transverseSpaceTimeInclusion_coeFn
      requestedTime receipt.transverseLimit
  filter_upwards [pathAE, inclusionAE] with
      time pathEq inclusionEq
  calc
    receipt.wholePath time =
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ
          receipt.wholePath) time :=
      pathEq.symm
    _ = receipt.stateLimit time := by
      rw [receipt.wholePath_toLp_eq_stateLimit]
    _ =
        (transverseSpaceTimeInclusion requestedTime
          receipt.transverseLimit) time := by
      rw [receipt.inclusion_eq]
    _ = (receipt.transverseLimit time).1 :=
      inclusionEq

/--
Every actual nonlinear extension row is the whole-lattice nonlinear row of
that same source-owned transverse state almost everywhere.
-/
theorem actualWaveNonlinearExtension_eq_wholeRow_ae
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      WholeContinuousMildReceipt.actualWaveNonlinearExtension
          receipt.toWholeContinuousMildReceipt wave time.1 =
        wholeStateVorticityNonlinearCoefficientAt
          (receipt.transverseLimit time).1 wave := by
  filter_upwards [
    transverseSpaceTimeNonlinearRow_coeFn
      receipt.transverseLimit wave] with time rowEq
  rw [
    WholeContinuousMildReceipt.actualWaveNonlinearExtension,
    commonTimeZeroExtension_of_mem
      requestedTime _ time.1 time.property,
    rowEq]
  rfl

/--
The actual real-line difference row and the whole transverse-state
difference are the same event almost everywhere.
-/
theorem actualWaveDifferencePath_eq_transverseLimit_ae
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualWaveDifferencePath left right wave time.1 =
        (left.transverseLimit time).1 wave.1 -
          (right.transverseLimit time).1 wave.1 := by
  filter_upwards [
    wholePath_eq_transverseLimit_ae left,
    wholePath_eq_transverseLimit_ae right] with
      time leftEq rightEq
  rw [actualWaveDifferencePath_eq_wholePath_sub
    left right wave time, leftEq, rightEq]

theorem actualDifferenceSerrinCoefficient_eq_transverseLimit_ae
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualDifferenceSerrinCoefficient receipt time.1 =
        ν.coeff⁻¹ *
          wholeStateVelocityMajorant
            (receipt.transverseLimit time).1 ^ 2 := by
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ receipt.wholePath
  have transverseAE :=
    wholePath_eq_transverseLimit_ae receipt
  filter_upwards [pathAE, transverseAE] with
      time pathEq transverseEq
  rw [actualDifferenceSerrinCoefficient,
    commonTimeZeroExtension_of_mem
      requestedTime _ time.1 time.2,
    pathEq, transverseEq]

theorem actualDifferenceKineticMass_eq_transverseLimit_ae
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualDifferenceKineticMass left right time.1 =
        puncturedWholeVorticityKineticMass
          ((left.transverseLimit time).1 -
            (right.transverseLimit time).1) := by
  filter_upwards [
    wholePath_eq_transverseLimit_ae left,
    wholePath_eq_transverseLimit_ae right] with
      time leftEq rightEq
  rw [actualDifferenceKineticMass_of_mem
    left right time.1 time.2, leftEq, rightEq]

/-- The source-generated transverse state has its zero row almost
everywhere; no pointwise zero-mode certificate is added to the receipt. -/
theorem transverseLimit_zeroRow_ae
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (receipt.transverseLimit time).1 0 = 0 := by
  have inclusionAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        receipt.stateLimit time =
          (receipt.transverseLimit time).1 := by
    simpa only [receipt.inclusion_eq] using
      transverseSpaceTimeInclusion_coeFn
        requestedTime receipt.transverseLimit
  have rowAE :=
    fixedWaveSpaceTimeRestriction_coeFn
      requestedTime 0 receipt.stateLimit
  have zeroAE :=
    MeasureTheory.Lp.coeFn_zero
      ComplexCoordinateVector 2
      (commonTimeMeasure requestedTime)
  filter_upwards [inclusionAE, rowAE, zeroAE] with
      time inclusionEq rowEq zeroEq
  calc
    (receipt.transverseLimit time).1 0 =
        receipt.stateLimit time 0 := by rw [inclusionEq]
    _ =
        fixedWaveSpaceTimeRestriction
          requestedTime 0 receipt.stateLimit time :=
      rowEq.symm
    _ =
        (0 : FixedWaveSpaceTimeState requestedTime) time := by
      rw [
        InfiniteMildDuhamelForcingReceipt.stateLimit_zero_row
          receipt.toInfiniteMildDuhamelForcingReceipt]
    _ = 0 := zeroEq

/--
Fourier reality of the actual transverse state is generated almost
everywhere from the same inherited whole space-time receipt.
-/
theorem transverseLimit_fourierReality_ae
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      FiniteStateFourierReality
        (receipt.transverseLimit time).1 := by
  have inclusionAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        receipt.stateLimit time =
          (receipt.transverseLimit time).1 := by
    simpa only [receipt.inclusion_eq] using
      transverseSpaceTimeInclusion_coeFn
        requestedTime receipt.transverseLimit
  have realityAE :
      ∀ wave : IntegerWavevector,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          receipt.stateLimit time (waveNeg wave) =
            vectorConj (receipt.stateLimit time wave) := by
    intro wave
    have negRowAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime (waveNeg wave) receipt.stateLimit
    have rowAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.stateLimit
    have conjugationAE :=
      fixedWaveSpaceTimeConjugation_coeFn
        requestedTime
        (fixedWaveSpaceTimeRestriction
          requestedTime wave receipt.stateLimit)
    filter_upwards [negRowAE, rowAE, conjugationAE] with
        time negRowEq rowEq conjugationEq
    calc
      receipt.stateLimit time (waveNeg wave) =
          fixedWaveSpaceTimeRestriction
            requestedTime (waveNeg wave)
            receipt.stateLimit time :=
        negRowEq.symm
      _ =
          fixedWaveSpaceTimeConjugation requestedTime
            (fixedWaveSpaceTimeRestriction
              requestedTime wave receipt.stateLimit) time := by
        rw [
          InfiniteMildDuhamelForcingReceipt.stateLimit_fourierReality
            receipt.toInfiniteMildDuhamelForcingReceipt wave]
      _ =
          vectorConj
            (fixedWaveSpaceTimeRestriction
              requestedTime wave receipt.stateLimit time) :=
        conjugationEq
      _ = vectorConj (receipt.stateLimit time wave) := by
        rw [rowEq]
  filter_upwards [
    inclusionAE,
    eventually_countable_forall.2 realityAE] with
      time inclusionEq timeReality
  intro wave
  rw [← inclusionEq]
  exact timeReality wave

/--
The source-owned space-time gradient budget produces the pointwise
whole-lattice summability required by the kinetic cancellation almost
everywhere.
-/
theorem transverseLimit_gradient_ae_summable
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            ((receipt.transverseLimit time).1 wave) := by
  have inclusionAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        receipt.stateLimit time =
          (receipt.transverseLimit time).1 := by
    simpa only [receipt.inclusion_eq] using
      transverseSpaceTimeInclusion_coeFn
        requestedTime receipt.transverseLimit
  filter_upwards [
    receipt.pointwiseGradient_ae_summable,
    inclusionAE] with time gradientSummable inclusionEq
  simpa only [inclusionEq] using gradientSummable

/--
The actual whole tangent difference has a pointwise source representation
by the pre-existing nonlinear and viscous negative-one functions.
-/
theorem wholeNegativeOneTangentDifference_eq_pointwise_functions_ae
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      StrongContinuationReceipt.wholeNegativeOneTangentDifference
          left right time =
        (wholeSpaceTimeNonlinearNegativeOneFunction
            left.transverseLimit time -
          wholeSpaceTimeNonlinearNegativeOneFunction
            right.transverseLimit time) -
        (wholeSpaceTimeViscousNegativeOneFunction
            ν.coeff left.stateLimit time -
          wholeSpaceTimeViscousNegativeOneFunction
            ν.coeff right.stateLimit time) := by
  let leftForcing :=
    left.toInfiniteMildDuhamelForcingReceipt
      |>.toNonlinearNegativeOneForcingReceipt
  let rightForcing :=
    right.toInfiniteMildDuhamelForcingReceipt
      |>.toNonlinearNegativeOneForcingReceipt
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
        leftForcing)
      (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
        rightForcing),
    MeasureTheory.Lp.coeFn_sub
      leftForcing.negativeOneForcing
      (NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
        leftForcing),
    MeasureTheory.Lp.coeFn_sub
      rightForcing.negativeOneForcing
      (NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
        rightForcing),
    leftForcing.negativeOneForcing_coeFn,
    rightForcing.negativeOneForcing_coeFn,
    wholeSpaceTimeViscousNegativeOneState_coeFn
      ν.coeff leftForcing.stateLimit
      leftForcing.gradient_summable
      leftForcing.pointwiseGradient_ae_summable,
    wholeSpaceTimeViscousNegativeOneState_coeFn
      ν.coeff rightForcing.stateLimit
      rightForcing.gradient_summable
      rightForcing.pointwiseGradient_ae_summable] with
      time tangentDifferenceEq leftTangentEq rightTangentEq
      leftNonlinearEq rightNonlinearEq leftViscousEq rightViscousEq
  change
    ((NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
          leftForcing -
        NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
          rightForcing) time) = _
  rw [tangentDifferenceEq]
  change
    ((leftForcing.negativeOneForcing -
        NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
          leftForcing) time) -
      ((rightForcing.negativeOneForcing -
        NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
          rightForcing) time) = _
  rw [leftTangentEq, rightTangentEq]
  change
    (leftForcing.negativeOneForcing time -
          NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
            leftForcing time) -
        (rightForcing.negativeOneForcing time -
          NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
            rightForcing time) = _
  rw [leftNonlinearEq, rightNonlinearEq]
  change
    (wholeSpaceTimeNonlinearNegativeOneFunction
          left.transverseLimit time -
        wholeSpaceTimeViscousNegativeOneState
          ν.coeff left.stateLimit
          leftForcing.gradient_summable
          leftForcing.pointwiseGradient_ae_summable time) -
      (wholeSpaceTimeNonlinearNegativeOneFunction
          right.transverseLimit time -
        wholeSpaceTimeViscousNegativeOneState
          ν.coeff right.stateLimit
          rightForcing.gradient_summable
          rightForcing.pointwiseGradient_ae_summable time) = _
  rw [leftViscousEq, rightViscousEq]
  abel

/-! ## Whole kinetic coordinate update -/

/--
Coordinate observation on the punctured whole lattice.  The zero row is
erased by the operator itself; no zero-row fact about a chosen
representative is needed to define the tangent carrier.
-/
def wholePuncturedCoordinateSliceCLM
    (coordinate : Coordinate) :
    ComplexVorticityHilbertState →L[ℂ]
      lp (fun _ : IntegerWavevector => ℂ) 2 :=
  lp.mapCLM 2
    (fun wave =>
      if _waveZero : wave = 0 then
        (0 :
          ComplexCoordinateVector →L[ℂ] ℂ)
      else
        (ContinuousLinearMap.proj coordinate :
          ComplexCoordinateVector →L[ℂ] ℂ))
    zero_le_one
    (fun wave => by
      split_ifs
      · simp
      · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro vector
        exact
          (norm_le_pi_norm vector coordinate).trans_eq
            (one_mul ‖vector‖).symm)

@[simp] theorem wholePuncturedCoordinateSliceCLM_apply_of_ne
    (coordinate : Coordinate)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    wholePuncturedCoordinateSliceCLM coordinate state wave =
      state wave coordinate := by
  simp [wholePuncturedCoordinateSliceCLM, waveNe]

@[simp] theorem wholePuncturedCoordinateSliceCLM_apply_zero
    (coordinate : Coordinate)
    (state : ComplexVorticityHilbertState) :
    wholePuncturedCoordinateSliceCLM coordinate state 0 = 0 := by
  simp [wholePuncturedCoordinateSliceCLM]

private theorem
    wholePuncturedCoordinateSliceCLM_eq_wholeCoordinateSliceCLM_of_zero_row
    (coordinate : Coordinate)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    wholePuncturedCoordinateSliceCLM coordinate state =
      wholeCoordinateSliceCLM coordinate state := by
  apply lp.ext
  funext wave
  by_cases waveNe : wave ≠ 0
  · rw [wholePuncturedCoordinateSliceCLM_apply_of_ne
      coordinate state wave waveNe,
    wholeCoordinateSliceCLM_apply]
  · have waveZero : wave = 0 := not_ne_iff.mp waveNe
    subst wave
    rw [wholePuncturedCoordinateSliceCLM_apply_zero,
      wholeCoordinateSliceCLM_apply, zeroRow]
    simp

private theorem wholeStateVorticityViscousNegativeOneState_sub
    (ν : ℝ)
    (left right : ComplexVorticityHilbertState)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave)) :
    wholeStateVorticityViscousNegativeOneState
          ν left leftGradientSummable -
        wholeStateVorticityViscousNegativeOneState
          ν right rightGradientSummable =
      wholeStateVorticityViscousNegativeOneState
        ν (left - right)
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) := by
  apply lp.ext
  funext wave
  change
    wholeStateVorticityViscousNegativeOneState
          ν left leftGradientSummable wave -
        wholeStateVorticityViscousNegativeOneState
          ν right rightGradientSummable wave =
      wholeStateVorticityViscousNegativeOneState
        ν (left - right)
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) wave
  simp only [
    wholeStateVorticityViscousNegativeOneState_apply,
    wholeStateVorticityViscousNegativeOneWeightedCoefficient]
  change
    (ν * Real.sqrt (integerWaveViscousMultiplier wave)) • left wave -
        (ν * Real.sqrt (integerWaveViscousMultiplier wave)) • right wave =
      (ν * Real.sqrt (integerWaveViscousMultiplier wave)) •
        (left wave - right wave)
  exact (smul_sub _ _ _).symm

private theorem wholeStateVorticityNonlinearNegativeOneState_sub
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave)) :
    ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
          left leftTransverse leftGradientSummable -
        ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
          right rightTransverse rightGradientSummable =
      wholeStateVorticityNonlinearDifferenceNegativeOneState
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) := by
  apply lp.ext
  funext wave
  change
    ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
          left leftTransverse leftGradientSummable wave -
        ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
          right rightTransverse rightGradientSummable wave =
      wholeStateVorticityNonlinearDifferenceNegativeOneState
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) wave
  simp only [
    ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState_apply,
    wholeStateVorticityNonlinearDifferenceNegativeOneState_apply]
  by_cases waveZero : wave = 0
  · simp [
      ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
      wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient,
      waveZero]
  · simp only [
      ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
      wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient,
      if_neg waveZero]
    rw [smul_sub]

private theorem weightedCoordinateInnerSum_viscous_eq
    (ν : ℝ)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (vector : ComplexCoordinateVector) :
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticFourierWeight wave * vector coordinate)
        (((ν * Real.sqrt
            (integerWaveViscousMultiplier wave) : ℝ) : ℂ) *
          vector coordinate)).re) =
      ν * complexCoordinateAmplitudeSq vector := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave :=
    integerWaveViscousMultiplier_pos ⟨wave, waveNe⟩
  have sqrtPos :
      0 < Real.sqrt (integerWaveViscousMultiplier wave) :=
    Real.sqrt_pos.2 multiplierPos
  have weighted :=
    weightedCoordinateInnerSum_eq_realInner_div
      wave waveNe vector
        ((ν * integerWaveViscousMultiplier wave) • vector)
  calc
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticFourierWeight wave * vector coordinate)
        (((ν * Real.sqrt
            (integerWaveViscousMultiplier wave) : ℝ) : ℂ) *
          vector coordinate)).re) =
        ∑ coordinate : Coordinate,
          (inner ℂ
            (wholeKineticFourierWeight wave * vector coordinate)
            (((Real.sqrt
                (integerWaveViscousMultiplier wave))⁻¹ : ℝ) *
              ((ν * integerWaveViscousMultiplier wave) •
                vector) coordinate)).re := by
      apply Finset.sum_congr rfl
      intro coordinate coordinateMem
      congr 2
      simp only [Pi.smul_apply, Complex.real_smul]
      rw [Complex.ofReal_mul, Complex.ofReal_mul,
        Complex.ofReal_inv]
      rw [show
          (integerWaveViscousMultiplier wave : ℂ) =
            (Real.sqrt
                (integerWaveViscousMultiplier wave) : ℂ) *
              Real.sqrt
                (integerWaveViscousMultiplier wave) by
        exact_mod_cast
          (Real.mul_self_sqrt multiplierPos.le).symm]
      field_simp [sqrtPos.ne']
    _ =
        complexCoordinateRealInner vector
            ((ν * integerWaveViscousMultiplier wave) • vector) /
          integerWaveViscousMultiplier wave :=
      weighted
    _ = ν * complexCoordinateAmplitudeSq vector := by
      rw [complexCoordinateRealInner_real_smul_right,
        complexCoordinateRealInner_self,
        ←
          complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      field_simp [ne_of_gt multiplierPos]

private theorem wholeStateVorticityViscousDifferenceKineticPairing_eq
    (ν : ℝ)
    (left right : ComplexVorticityHilbertState)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave)) :
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticCoordinateSliceCLM coordinate (left - right))
        (wholeCoordinateSliceCLM coordinate
          (wholeStateVorticityViscousNegativeOneState
                ν left leftGradientSummable -
            wholeStateVorticityViscousNegativeOneState
                ν right rightGradientSummable))).re) =
      ν * puncturedWholeVorticityEuclideanMass (left - right) := by
  rw [wholeStateVorticityViscousNegativeOneState_sub
    ν left right leftGradientSummable rightGradientSummable]
  let difference := left - right
  let differenceGradientSummable :=
    summable_wholeStateVorticityGradientDensity_sub
      left right leftGradientSummable rightGradientSummable
  let viscousState :=
    wholeStateVorticityViscousNegativeOneState
      ν difference differenceGradientSummable
  change
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticCoordinateSliceCLM coordinate difference)
        (wholeCoordinateSliceCLM coordinate viscousState)).re) =
      ν * puncturedWholeVorticityEuclideanMass difference
  simp_rw [lp.inner_eq_tsum]
  have innerSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate difference wave)
            (wholeCoordinateSliceCLM
              coordinate viscousState wave) :=
    fun coordinate =>
      (lp.hasSum_inner
        (wholeKineticCoordinateSliceCLM coordinate difference)
        (wholeCoordinateSliceCLM coordinate viscousState)).summable
  simp_rw [Complex.re_tsum (innerSummable _)]
  have reSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate difference wave)
            (wholeCoordinateSliceCLM
              coordinate viscousState wave)).re := by
    intro coordinate
    simpa [Function.comp_def] using
      (innerSummable coordinate).map
        Complex.reCLM Complex.continuous_re
  rw [← Summable.tsum_finsetSum
    (fun coordinate _ => reSummable coordinate)]
  have fullSummable :
      Summable fun wave : IntegerWavevector =>
        ∑ coordinate : Coordinate,
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate difference wave)
            (wholeCoordinateSliceCLM
              coordinate viscousState wave)).re := by
    exact summable_sum (s := Finset.univ) fun coordinate _ =>
      reSummable coordinate
  have complementZero :
      (∑' wave :
          ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
            Set IntegerWavevector),
        ∑ coordinate : Coordinate,
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate difference wave.1)
            (wholeCoordinateSliceCLM
              coordinate viscousState wave.1)).re) = 0 := by
    rw [show
        (fun wave :
            ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
              Set IntegerWavevector) =>
          ∑ coordinate : Coordinate,
            (inner ℂ
              (wholeKineticCoordinateSliceCLM
                coordinate difference wave.1)
              (wholeCoordinateSliceCLM
                coordinate viscousState wave.1)).re) =
          0 by
      funext wave
      have waveZero : wave.1 = 0 := by simpa using wave.2
      simp [wholeKineticCoordinateSliceCLM_apply,
        wholeKineticFourierWeight, waveZero]]
    exact tsum_zero
  have split :=
    fullSummable.tsum_subtype_add_tsum_subtype_compl
      { wave : IntegerWavevector | wave ≠ 0 }
  rw [← split, complementZero, add_zero]
  unfold puncturedWholeVorticityEuclideanMass
  rw [← tsum_mul_left]
  apply tsum_congr
  intro wave
  simp only [wholeKineticCoordinateSliceCLM_apply,
    wholeCoordinateSliceCLM_apply]
  change
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticFourierWeight wave.1 *
          difference wave.1 coordinate)
        (((ν * Real.sqrt
            (integerWaveViscousMultiplier wave.1) : ℝ) : ℂ) *
          difference wave.1 coordinate)).re) =
      ν * complexCoordinateAmplitudeSq (difference wave.1)
  exact weightedCoordinateInnerSum_viscous_eq
    ν wave.1 wave.2 (difference wave.1)

private theorem
    wholeStateVorticityNonlinearDifferenceNegativeOneState_zero_row
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave)) :
    wholeStateVorticityNonlinearDifferenceNegativeOneState
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) 0 = 0 := by
  simp [wholeStateVorticityNonlinearDifferenceNegativeOneState_apply,
    wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient]

private theorem wholeStateVorticityViscousNegativeOneState_zero_row
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeStateVorticityViscousNegativeOneState
        ν state gradientSummable 0 = 0 := by
  simp [wholeStateVorticityViscousNegativeOneState_apply,
    wholeStateVorticityViscousNegativeOneWeightedCoefficient,
    integerWaveViscousMultiplier, integerWaveNormSq]

/-- The actual weighted whole tangent, observed at one physical coordinate
and with its source-owned zero mode erased. -/
def actualDifferenceKineticCoordinateTangentLp
    (coordinate : Coordinate)
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    Lp (lp (fun _ : IntegerWavevector => ℂ) 2) 2
      (commonTimeMeasure requestedTime) :=
  (wholePuncturedCoordinateSliceCLM coordinate).compLpL 2
    (commonTimeMeasure requestedTime)
    (StrongContinuationReceipt.wholeNegativeOneTangentDifference
      left right)

/-- Real-line representative of the actual punctured weighted tangent. -/
def actualDifferenceKineticCoordinateTangent
    (coordinate : Coordinate)
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ℝ → lp (fun _ : IntegerWavevector => ℂ) 2 :=
  commonTimeZeroExtension requestedTime fun time =>
    actualDifferenceKineticCoordinateTangentLp
      coordinate left right time

theorem actualDifferenceKineticCoordinateTangent_intervalIntegrable
    (coordinate : Coordinate)
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    IntervalIntegrable
      (actualDifferenceKineticCoordinateTangent
        coordinate left right)
      volume 0 requestedTime := by
  apply commonTimeZeroExtension_intervalIntegrable_of_integrable
    requestedTime requestedTimePos.le
  have onUniv :=
    integrableOn_Lp_of_measure_ne_top
      (actualDifferenceKineticCoordinateTangentLp
        coordinate left right)
      fact_one_le_two_ennreal.elim
      (measure_ne_top
        (commonTimeMeasure requestedTime) Set.univ)
  simpa only [integrableOn_univ] using onUniv

theorem actualDifferenceKineticCoordinateTangentLp_apply_ae
    (coordinate : Coordinate)
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualDifferenceKineticCoordinateTangentLp
          coordinate left right time wave.1 =
        ((Real.sqrt
            (integerWaveViscousMultiplier wave.1) : ℂ)⁻¹ *
          actualWaveDifferenceTangent
            left right wave time.1 coordinate) := by
  let wholeTangent :=
    StrongContinuationReceipt.wholeNegativeOneTangentDifference
      left right
  let leftFixed :=
    NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
      (left.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt)
      wave.1
  let rightFixed :=
    NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
      (right.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt)
      wave.1
  have projectedAE :=
    (wholePuncturedCoordinateSliceCLM coordinate).coeFn_compLpL
      wholeTangent
  have restrictionAE :=
    fixedWaveSpaceTimeRestriction_coeFn
      requestedTime wave.1 wholeTangent
  have smulAE :=
    MeasureTheory.Lp.coeFn_smul
      (Real.sqrt
        (integerWaveViscousMultiplier wave.1) : ℂ)
      (fixedWaveSpaceTimeRestriction
        requestedTime wave.1 wholeTangent)
  have fixedDifferenceAE :=
    MeasureTheory.Lp.coeFn_sub leftFixed rightFixed
  have leftActualAE :=
    fixedWaveNegativeOneTangentL2_ae_actual
      left wave.1 wave.2
  have rightActualAE :=
    fixedWaveNegativeOneTangentL2_ae_actual
      right wave.1 wave.2
  have fixedWholeEq :
      (Real.sqrt
          (integerWaveViscousMultiplier wave.1) : ℂ) •
          fixedWaveSpaceTimeRestriction
            requestedTime wave.1 wholeTangent =
        leftFixed - rightFixed := by
    exact
      SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEquation.StrongContinuationReceipt.fixedWave_wholeNegativeOneTangentDifference
        left right wave.1
  filter_upwards [
    projectedAE, restrictionAE, smulAE,
    fixedDifferenceAE, leftActualAE, rightActualAE] with
      time projectedEq restrictionEq smulEq
      fixedDifferenceEq leftActualEq rightActualEq
  have unweightedEq :
      (Real.sqrt
          (integerWaveViscousMultiplier wave.1) : ℂ) •
          (wholeTangent time) wave.1 =
        actualWaveDifferenceTangent
          left right wave time.1 := by
    calc
      (Real.sqrt
          (integerWaveViscousMultiplier wave.1) : ℂ) •
          (wholeTangent time) wave.1 =
          (Real.sqrt
              (integerWaveViscousMultiplier wave.1) : ℂ) •
            (fixedWaveSpaceTimeRestriction
              requestedTime wave.1 wholeTangent) time := by
        rw [restrictionEq]
      _ =
          ((Real.sqrt
              (integerWaveViscousMultiplier wave.1) : ℂ) •
            fixedWaveSpaceTimeRestriction
              requestedTime wave.1 wholeTangent) time :=
        smulEq.symm
      _ = (leftFixed - rightFixed) time := by
        rw [fixedWholeEq]
      _ = leftFixed time - rightFixed time :=
        fixedDifferenceEq
      _ =
          actualWaveTangent left wave.1 time.1 -
            actualWaveTangent right wave.1 time.1 := by
        rw [leftActualEq, rightActualEq]
      _ =
          actualWaveDifferenceTangent
            left right wave time.1 := by
        rfl
  have sqrtNe :
      (Real.sqrt
          (integerWaveViscousMultiplier wave.1) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Real.sqrt_pos.2
        (integerWaveViscousMultiplier_pos wave)).ne'
  rw [actualDifferenceKineticCoordinateTangentLp,
    projectedEq,
    wholePuncturedCoordinateSliceCLM_apply_of_ne
      coordinate (wholeTangent time) wave.1 wave.2]
  have coordinateEq :=
    congrFun unweightedEq coordinate
  simp only [Pi.smul_apply, smul_eq_mul] at coordinateEq
  rw [← coordinateEq]
  field_simp

private theorem actualWaveDifferenceTangent_intervalIntegrable
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    IntervalIntegrable
      (actualWaveDifferenceTangent left right wave)
      volume 0 requestedTime := by
  have leftIntegrable :=
    actualWaveTangent_intervalIntegrable left wave.1
  have rightIntegrable :=
    actualWaveTangent_intervalIntegrable right wave.1
  have tangentEq :
      actualWaveDifferenceTangent left right wave =
        fun time =>
          actualWaveTangent left wave.1 time -
            actualWaveTangent right wave.1 time := by
    funext time
    rfl
  rw [tangentEq]
  exact leftIntegrable.sub rightIntegrable

theorem actualWaveDifferencePath_eq_intervalIntegral
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    actualWaveDifferencePath left right wave time =
      ∫ earlier in (0 : ℝ)..time,
        actualWaveDifferenceTangent left right wave earlier := by
  have update :=
    path_sub_eq_intervalIntegral
      (actualWaveDifferencePath_absolutelyContinuousOnInterval
        left right wave)
      (actualWaveDifferenceTangent_intervalIntegrable
        left right wave)
      (actualWaveDifferencePath_ae_hasDerivAt
        left right wave)
      time
      (by simpa [uIcc_of_le requestedTimePos.le] using timeMem)
  rw [actualWaveDifferencePath_zero left right wave,
    sub_zero] at update
  exact update

/-- Bochner primitive of one punctured kinetic coordinate of the actual
whole tangent difference. -/
def actualDifferenceKineticCoordinateIntegralPath
    (coordinate : Coordinate)
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ℝ → lp (fun _ : IntegerWavevector => ℂ) 2 :=
  fun time =>
    ∫ earlier in (0 : ℝ)..time,
      actualDifferenceKineticCoordinateTangent
        coordinate left right earlier

/-- Complete kinetic power of the actual whole difference tangent. -/
def actualDifferenceKineticPower
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ℝ → ℝ :=
  fun time =>
    ∑ coordinate : Coordinate,
      2 * ⟪
        actualDifferenceKineticCoordinateIntegralPath
          coordinate left right time,
        actualDifferenceKineticCoordinateTangent
          coordinate left right time⟫_ℝ

/--
The Bochner primitive of the actual whole tangent is exactly the canonical
kinetic weighting of the difference path at every physical time.
-/
theorem actualDifferenceKineticCoordinateIntegralPath_eq
    (coordinate : Coordinate)
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime) :
    actualDifferenceKineticCoordinateIntegralPath
        coordinate left right time.1 =
      wholeKineticCoordinateSliceCLM coordinate
        (left.wholePath time - right.wholePath time) := by
  apply lp.ext
  funext wave
  have tangentIntegrableAt :
      IntervalIntegrable
        (actualDifferenceKineticCoordinateTangent
          coordinate left right)
        volume 0 time.1 :=
    (actualDifferenceKineticCoordinateTangent_intervalIntegrable
      coordinate left right).mono_set <| by
        rw [uIcc_of_le time.property.1,
          uIcc_of_le requestedTimePos.le]
        exact Icc_subset_Icc le_rfl time.property.2
  have evaluatedIntegral :=
    (lp.evalCLM ℂ (fun _ : IntegerWavevector => ℂ) 2 wave)
      |>.intervalIntegral_comp_comm
        tangentIntegrableAt
  change
    (lp.evalCLM ℂ (fun _ : IntegerWavevector => ℂ) 2 wave)
        (actualDifferenceKineticCoordinateIntegralPath
          coordinate left right time.1) =
      _
  rw [actualDifferenceKineticCoordinateIntegralPath,
    ← evaluatedIntegral]
  change
    (∫ earlier in (0 : ℝ)..time.1,
        actualDifferenceKineticCoordinateTangent
          coordinate left right earlier wave) =
      _
  by_cases waveNe : wave ≠ 0
  · let indexedWave : NonzeroIntegerWavevector := ⟨wave, waveNe⟩
    have converted :=
      commonTime_integral_Iic_eq_intervalIntegral
        requestedTime requestedTimePos.le time
        (fun earlier =>
          actualDifferenceKineticCoordinateTangent
            coordinate left right earlier wave)
    have tangentAE :=
      actualDifferenceKineticCoordinateTangentLp_apply_ae
        coordinate left right indexedWave
    have setIntegralEq :
        (∫ actual in Iic time,
            actualDifferenceKineticCoordinateTangent
              coordinate left right actual.1 wave
            ∂(commonTimeMeasure requestedTime)) =
          ∫ actual in Iic time,
            ((Real.sqrt
                (integerWaveViscousMultiplier wave) : ℂ)⁻¹ *
              actualWaveDifferenceTangent
                left right indexedWave actual.1 coordinate)
            ∂(commonTimeMeasure requestedTime) := by
      apply MeasureTheory.integral_congr_ae
      have restricted :
          ∀ᵐ actual ∂
              (commonTimeMeasure requestedTime).restrict (Iic time),
            actualDifferenceKineticCoordinateTangentLp
                coordinate left right actual wave =
              ((Real.sqrt
                  (integerWaveViscousMultiplier wave) : ℂ)⁻¹ *
                actualWaveDifferenceTangent
                  left right indexedWave actual.1 coordinate) :=
        MeasureTheory.ae_restrict_le tangentAE
      filter_upwards [restricted] with actual equality
      rw [actualDifferenceKineticCoordinateTangent,
        commonTimeZeroExtension_of_mem
          requestedTime _ actual.1 actual.property]
      exact equality
    have convertedTangent :=
      commonTime_integral_Iic_eq_intervalIntegral
        requestedTime requestedTimePos.le time
        (fun earlier =>
          ((Real.sqrt
              (integerWaveViscousMultiplier wave) : ℂ)⁻¹ *
            actualWaveDifferenceTangent
              left right indexedWave earlier coordinate))
    have coordinateIntegral :=
      (ContinuousLinearMap.proj coordinate :
        ComplexCoordinateVector →L[ℂ] ℂ)
        |>.intervalIntegral_comp_comm
          (actualWaveDifferenceTangent_intervalIntegrable
            left right indexedWave
              |>.mono_set <| by
                rw [uIcc_of_le time.property.1,
                  uIcc_of_le requestedTimePos.le]
                exact Icc_subset_Icc le_rfl time.property.2)
    have coordinateIntegral' :
        (∫ earlier in (0 : ℝ)..time.1,
            actualWaveDifferenceTangent
              left right indexedWave earlier coordinate) =
          (∫ earlier in (0 : ℝ)..time.1,
            actualWaveDifferenceTangent
              left right indexedWave earlier) coordinate := by
      exact coordinateIntegral
    rw [← converted, setIntegralEq, convertedTangent,
      intervalIntegral.integral_const_mul,
      coordinateIntegral',
      ← actualWaveDifferencePath_eq_intervalIntegral
        left right indexedWave time.1 time.property,
      actualWaveDifferencePath_eq_wholePath_sub
        left right indexedWave time]
    simp [wholeKineticCoordinateSliceCLM_apply,
      wholeKineticFourierWeight, waveNe]
    ring
  · have waveZero : wave = 0 := not_ne_iff.mp waveNe
    subst wave
    let wholeTangent :=
      StrongContinuationReceipt.wholeNegativeOneTangentDifference
        left right
    have projectedAE :=
      (wholePuncturedCoordinateSliceCLM coordinate).coeFn_compLpL
        wholeTangent
    have converted :=
      commonTime_integral_Iic_eq_intervalIntegral
        requestedTime requestedTimePos.le time
        (fun earlier =>
          actualDifferenceKineticCoordinateTangent
            coordinate left right earlier 0)
    have setIntegralZero :
        (∫ actual in Iic time,
            actualDifferenceKineticCoordinateTangent
              coordinate left right actual.1 0
            ∂(commonTimeMeasure requestedTime)) = 0 := by
      calc
        (∫ actual in Iic time,
            actualDifferenceKineticCoordinateTangent
              coordinate left right actual.1 0
            ∂(commonTimeMeasure requestedTime)) =
            ∫ actual in Iic time, (0 : ℂ)
              ∂(commonTimeMeasure requestedTime) := by
          apply MeasureTheory.integral_congr_ae
          have restricted :
              ∀ᵐ actual ∂
                  (commonTimeMeasure requestedTime).restrict (Iic time),
                actualDifferenceKineticCoordinateTangentLp
                    coordinate left right actual =
                  wholePuncturedCoordinateSliceCLM coordinate
                    (wholeTangent actual) :=
            MeasureTheory.ae_restrict_le projectedAE
          filter_upwards [restricted] with actual equality
          rw [actualDifferenceKineticCoordinateTangent,
            commonTimeZeroExtension_of_mem
              requestedTime _ actual.1 actual.property,
            equality,
            wholePuncturedCoordinateSliceCLM_apply_zero]
        _ = 0 := by simp
    rw [← converted, setIntegralZero]
    simp [wholeKineticCoordinateSliceCLM_apply,
      wholeKineticFourierWeight]

/--
The real `ℓ²` inner product on scalar complex rows is the real part of the
complex `ℓ²` inner product.  The two structures are not definitionally equal
because `lp` builds its real instance coordinatewise.
-/
private theorem scalarLp_real_inner_eq_re_inner
    (left right : lp (fun _ : IntegerWavevector => ℂ) 2) :
    ⟪left, right⟫_ℝ = (inner ℂ left right).re := by
  have innerSummable :
      Summable fun wave : IntegerWavevector =>
        inner ℂ (left wave) (right wave) :=
    (lp.hasSum_inner left right).summable
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    Complex.re_tsum innerSummable]
  apply tsum_congr
  intro wave
  rfl

/--
Almost everywhere, incompressibility and viscosity absorb the complete
kinetic power into the actual source-generated Serrin coefficient.
-/
theorem actualDifferenceKineticPower_ae_le
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualDifferenceKineticPower left right time.1 ≤
        actualDifferenceSerrinCoefficient left time.1 *
          actualDifferenceKineticMass left right time.1 := by
  let wholeTangent :=
    StrongContinuationReceipt.wholeNegativeOneTangentDifference
      left right
  have coordinateProjectionAE :
      ∀ coordinate : Coordinate,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          actualDifferenceKineticCoordinateTangentLp
              coordinate left right time =
            wholePuncturedCoordinateSliceCLM coordinate
              (wholeTangent time) :=
    fun coordinate =>
      (wholePuncturedCoordinateSliceCLM coordinate).coeFn_compLpL
        wholeTangent
  have leftStateAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        left.stateLimit time =
          (left.transverseLimit time).1 := by
    simpa only [left.inclusion_eq] using
      transverseSpaceTimeInclusion_coeFn
        requestedTime left.transverseLimit
  have rightStateAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        right.stateLimit time =
          (right.transverseLimit time).1 := by
    simpa only [right.inclusion_eq] using
      transverseSpaceTimeInclusion_coeFn
        requestedTime right.transverseLimit
  filter_upwards [
    eventually_countable_forall.2 coordinateProjectionAE,
    wholeNegativeOneTangentDifference_eq_pointwise_functions_ae
      left right,
    wholePath_eq_transverseLimit_ae left,
    wholePath_eq_transverseLimit_ae right,
    left.pointwiseGradient_ae_summable,
    right.pointwiseGradient_ae_summable,
    transverseLimit_gradient_ae_summable left,
    transverseLimit_gradient_ae_summable right,
    transverseLimit_zeroRow_ae left,
    transverseLimit_zeroRow_ae right,
    transverseLimit_fourierReality_ae left,
    transverseLimit_fourierReality_ae right,
    actualDifferenceSerrinCoefficient_eq_transverseLimit_ae left,
    actualDifferenceKineticMass_eq_transverseLimit_ae left right,
    leftStateAE, rightStateAE] with
      time coordinateProjection tangentFunctionEq
      leftPathEq rightPathEq
      leftStateGradient rightStateGradient
      leftGradient rightGradient
      leftZeroRow rightZeroRow
      leftReality rightReality
      coefficientEq kineticMassEq
      leftStateEq rightStateEq
  let leftState := (left.transverseLimit time).1
  let rightState := (right.transverseLimit time).1
  let difference := leftState - rightState
  have leftTransverse : WholeStateTransverse leftState := by
    have membership := (left.transverseLimit time).2
    change WholeStateTransverse
      ((left.transverseLimit time).1 : ComplexVorticityHilbertState) at membership
    exact membership
  have rightTransverse : WholeStateTransverse rightState := by
    have membership := (right.transverseLimit time).2
    change WholeStateTransverse
      ((right.transverseLimit time).1 : ComplexVorticityHilbertState) at membership
    exact membership
  let differenceGradient :=
    summable_wholeStateVorticityGradientDensity_sub
      leftState rightState leftGradient rightGradient
  let nonlinearDifference :=
    wholeStateVorticityNonlinearDifferenceNegativeOneState
      leftState rightState
      leftTransverse rightTransverse
      leftGradient rightGradient differenceGradient
  let viscousDifference :=
    wholeStateVorticityViscousNegativeOneState
      ν.coeff difference differenceGradient
  have tangentPointwise :
      wholeTangent time =
        nonlinearDifference - viscousDifference := by
    rw [tangentFunctionEq,
      wholeSpaceTimeNonlinearNegativeOneFunction_of_summable
        left.transverseLimit time leftGradient,
      wholeSpaceTimeNonlinearNegativeOneFunction_of_summable
        right.transverseLimit time rightGradient,
      wholeSpaceTimeViscousNegativeOneFunction_of_summable
        ν.coeff left.stateLimit time leftStateGradient,
      wholeSpaceTimeViscousNegativeOneFunction_of_summable
        ν.coeff right.stateLimit time rightStateGradient]
    simp only [leftStateEq, rightStateEq]
    change
      (ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
            leftState leftTransverse leftGradient -
          ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
            rightState rightTransverse rightGradient) -
        (wholeStateVorticityViscousNegativeOneState
            ν.coeff leftState leftGradient -
          wholeStateVorticityViscousNegativeOneState
            ν.coeff rightState rightGradient) =
          nonlinearDifference - viscousDifference
    rw [
      wholeStateVorticityNonlinearNegativeOneState_sub
        leftState rightState leftTransverse rightTransverse
          leftGradient rightGradient,
      wholeStateVorticityViscousNegativeOneState_sub
        ν.coeff leftState rightState leftGradient rightGradient]
  have nonlinearZero :
      nonlinearDifference 0 = 0 := by
    exact
      wholeStateVorticityNonlinearDifferenceNegativeOneState_zero_row
        leftState rightState
        leftTransverse rightTransverse
        leftGradient rightGradient
  have viscousZero :
      viscousDifference 0 = 0 := by
    exact
      wholeStateVorticityViscousNegativeOneState_zero_row
        ν.coeff difference differenceGradient
  have pathCoordinateEq :
      ∀ coordinate : Coordinate,
        actualDifferenceKineticCoordinateIntegralPath
            coordinate left right time.1 =
          wholeKineticCoordinateSliceCLM
            coordinate difference := by
    intro coordinate
    rw [actualDifferenceKineticCoordinateIntegralPath_eq
      coordinate left right time, leftPathEq, rightPathEq]
  have tangentCoordinateEq :
      ∀ coordinate : Coordinate,
        actualDifferenceKineticCoordinateTangent
            coordinate left right time.1 =
          wholeCoordinateSliceCLM coordinate nonlinearDifference -
            wholeCoordinateSliceCLM coordinate viscousDifference := by
    intro coordinate
    rw [actualDifferenceKineticCoordinateTangent,
      commonTimeZeroExtension_of_mem
        requestedTime _ time.1 time.property,
      coordinateProjection coordinate,
      tangentPointwise, map_sub,
      wholePuncturedCoordinateSliceCLM_eq_wholeCoordinateSliceCLM_of_zero_row
        coordinate nonlinearDifference nonlinearZero,
      wholePuncturedCoordinateSliceCLM_eq_wholeCoordinateSliceCLM_of_zero_row
        coordinate viscousDifference viscousZero]
  have nonlinearPairingEq :
      (∑ coordinate : Coordinate,
        ⟪wholeKineticCoordinateSliceCLM coordinate difference,
          wholeCoordinateSliceCLM coordinate nonlinearDifference⟫_ℝ) =
        wholeStateVorticityNonlinearDifferenceKineticPairing
          leftState rightState
          leftTransverse rightTransverse
          leftGradient rightGradient differenceGradient := by
    unfold
      ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation.wholeStateVorticityNonlinearDifferenceKineticPairing
    simp_rw [scalarLp_real_inner_eq_re_inner]
    rfl
  have viscousPairingEq :
      (∑ coordinate : Coordinate,
        ⟪wholeKineticCoordinateSliceCLM coordinate difference,
          wholeCoordinateSliceCLM coordinate viscousDifference⟫_ℝ) =
        ν.coeff *
          puncturedWholeVorticityEuclideanMass difference := by
    have viscousDifferenceEq :
        viscousDifference =
          wholeStateVorticityViscousNegativeOneState
              ν.coeff leftState leftGradient -
            wholeStateVorticityViscousNegativeOneState
              ν.coeff rightState rightGradient := by
      exact
        (wholeStateVorticityViscousNegativeOneState_sub
          ν.coeff leftState rightState leftGradient rightGradient).symm
    rw [viscousDifferenceEq]
    simp_rw [scalarLp_real_inner_eq_re_inner]
    simpa only [difference] using
      wholeStateVorticityViscousDifferenceKineticPairing_eq
        ν.coeff leftState rightState leftGradient rightGradient
  have powerEq :
      actualDifferenceKineticPower left right time.1 =
        2 *
            wholeStateVorticityNonlinearDifferenceKineticPairing
              leftState rightState
              leftTransverse rightTransverse
              leftGradient rightGradient differenceGradient -
          2 * ν.coeff *
            puncturedWholeVorticityEuclideanMass difference := by
    unfold actualDifferenceKineticPower
    simp_rw [pathCoordinateEq, tangentCoordinateEq, inner_sub_right]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      nonlinearPairingEq, viscousPairingEq]
    ring
  have young :=
    wholeStateVorticityNonlinearDifferenceKineticPairing_le_young
      leftState rightState leftZeroRow rightZeroRow
      leftTransverse rightTransverse
      leftReality rightReality leftGradient rightGradient
      ν.coeff ν.coeff_pos
  have euclideanNonneg :
      0 ≤ puncturedWholeVorticityEuclideanMass difference := by
    unfold puncturedWholeVorticityEuclideanMass
    exact tsum_nonneg fun wave =>
      complexCoordinateAmplitudeSq_nonneg _
  rw [powerEq, coefficientEq, kineticMassEq]
  dsimp [leftState, rightState, difference] at young ⊢
  nlinarith [mul_nonneg ν.coeff_pos.le euclideanNonneg]

/--
Exact kinetic energy transport for one coordinate of the complete
nonzero-frequency carrier.
-/
theorem actualDifferenceKineticCoordinate_energy_identity
    (coordinate : Coordinate)
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime) :
    (∫ time in (0 : ℝ)..terminal.1,
        2 * ⟪
          actualDifferenceKineticCoordinateIntegralPath
            coordinate left right time,
          actualDifferenceKineticCoordinateTangent
            coordinate left right time⟫_ℝ) =
      ‖wholeKineticCoordinateSliceCLM coordinate
          (left.wholePath terminal - right.wholePath terminal)‖ ^ 2 := by
  have tangentIntegrableAt :
      IntervalIntegrable
        (actualDifferenceKineticCoordinateTangent
          coordinate left right)
        volume 0 terminal.1 :=
    (actualDifferenceKineticCoordinateTangent_intervalIntegrable
      coordinate left right).mono_set <| by
        rw [uIcc_of_le terminal.property.1,
          uIcc_of_le requestedTimePos.le]
        exact Icc_subset_Icc le_rfl terminal.property.2
  have pathAC :
      AbsolutelyContinuousOnInterval
        (actualDifferenceKineticCoordinateIntegralPath
          coordinate left right)
        0 terminal.1 := by
    exact
      IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
        tangentIntegrableAt
        (by
          rw [uIcc_of_le terminal.property.1]
          exact ⟨le_rfl, terminal.property.1⟩)
  have pathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ uIcc (0 : ℝ) terminal.1 →
          HasDerivAt
            (actualDifferenceKineticCoordinateIntegralPath
              coordinate left right)
            (actualDifferenceKineticCoordinateTangent
              coordinate left right time)
            time := by
    filter_upwards [
      tangentIntegrableAt.ae_hasDerivAt_integral] with
        time integralDerivative
    intro timeMem
    exact integralDerivative timeMem 0 (by simp)
  have energyIdentity :=
    AbsolutelyContinuousOnInterval.norm_sq_energy_identity
      pathAC pathDerivative
  have initialPath :
      actualDifferenceKineticCoordinateIntegralPath
          coordinate left right 0 = 0 := by
    simp [actualDifferenceKineticCoordinateIntegralPath]
  rw [actualDifferenceKineticCoordinateIntegralPath_eq
      coordinate left right terminal,
    initialPath, norm_zero] at energyIdentity
  norm_num at energyIdentity
  simpa only [intervalIntegral.integral_const_mul, map_sub] using
    energyIdentity

private theorem
    actualDifferenceKineticCoordinatePower_intervalIntegrable
    (coordinate : Coordinate)
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    IntervalIntegrable
      (fun time =>
        2 * ⟪
          actualDifferenceKineticCoordinateIntegralPath
            coordinate left right time,
          actualDifferenceKineticCoordinateTangent
            coordinate left right time⟫_ℝ)
      volume 0 requestedTime := by
  have tangentIntegrable :=
    actualDifferenceKineticCoordinateTangent_intervalIntegrable
      coordinate left right
  have pathAC :
      AbsolutelyContinuousOnInterval
        (actualDifferenceKineticCoordinateIntegralPath
          coordinate left right)
        0 requestedTime := by
    exact
      IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
        tangentIntegrable
        (by
          rw [uIcc_of_le requestedTimePos.le]
          exact ⟨le_rfl, requestedTimePos.le⟩)
  have pathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ uIcc (0 : ℝ) requestedTime →
          HasDerivAt
            (actualDifferenceKineticCoordinateIntegralPath
              coordinate left right)
            (actualDifferenceKineticCoordinateTangent
              coordinate left right time)
            time := by
    filter_upwards [
      tangentIntegrable.ae_hasDerivAt_integral] with
        time integralDerivative
    intro timeMem
    exact integralDerivative timeMem 0 (by simp)
  have energyAC :
      AbsolutelyContinuousOnInterval
        (fun time =>
          ‖actualDifferenceKineticCoordinateIntegralPath
            coordinate left right time‖ ^ 2)
        0 requestedTime := by
    simpa only [real_inner_self_eq_norm_sq] using
      absolutelyContinuousOnInterval_real_inner pathAC pathAC
  apply energyAC.intervalIntegrable_deriv.congr_ae
  filter_upwards [
    ae_restrict_mem measurableSet_uIoc,
    ae_mono Measure.restrict_le_self pathDerivative] with
      time timeMem derivative
  exact
    ((derivative (uIoc_subset_uIcc timeMem)).norm_sq).deriv

theorem actualDifferenceKineticPower_intervalIntegrable
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    IntervalIntegrable
      (actualDifferenceKineticPower left right)
      volume 0 requestedTime := by
  unfold actualDifferenceKineticPower
  exact IntervalIntegrable.sum Finset.univ fun coordinate _ =>
    actualDifferenceKineticCoordinatePower_intervalIntegrable
      coordinate left right

private theorem
    actualDifferenceCoefficientMulKineticMass_intervalIntegrable
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    IntervalIntegrable
      (fun time =>
        actualDifferenceSerrinCoefficient left time *
          actualDifferenceKineticMass left right time)
      volume 0 requestedTime :=
  (actualDifferenceSerrinCoefficient_intervalIntegrable left)
    |>.mul_continuousOn
      (by
        rw [uIcc_of_le requestedTimePos.le]
        exact actualDifferenceKineticMass_continuousOn left right)

theorem actualDifferenceKineticMass_eq_integral_power
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime) :
    actualDifferenceKineticMass left right terminal.1 =
      ∫ time in (0 : ℝ)..terminal.1,
        actualDifferenceKineticPower left right time := by
  rw [actualDifferenceKineticMass_of_mem
      left right terminal.1 terminal.property,
    puncturedWholeVorticityKineticMass_eq_coordinateSlices]
  simp only [actualDifferenceKineticPower]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro coordinate coordinateMem
    exact
      (actualDifferenceKineticCoordinate_energy_identity
        coordinate left right terminal).symm
  · intro coordinate coordinateMem
    exact
      (actualDifferenceKineticCoordinatePower_intervalIntegrable
        coordinate left right).mono_set <| by
          rw [uIcc_of_le terminal.property.1,
            uIcc_of_le requestedTimePos.le]
          exact Icc_subset_Icc le_rfl terminal.property.2

private theorem actualDifferenceKineticPower_ae_le_volume_restrict
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂volume.restrict (Icc (0 : ℝ) requestedTime),
      actualDifferenceKineticPower left right time ≤
        actualDifferenceSerrinCoefficient left time *
          actualDifferenceKineticMass left right time := by
  apply (ae_restrict_iff_subtype measurableSet_Icc).2
  have inequality :=
    actualDifferenceKineticPower_ae_le left right
  rw [commonTimeMeasure_eq_comap_volume] at inequality
  exact inequality

theorem actualDifferenceKineticMass_le_integral
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime) :
    actualDifferenceKineticMass left right terminal.1 ≤
      ∫ time in (0 : ℝ)..terminal.1,
        actualDifferenceSerrinCoefficient left time *
          actualDifferenceKineticMass left right time := by
  rw [actualDifferenceKineticMass_eq_integral_power left right terminal]
  apply intervalIntegral.integral_mono_ae_restrict terminal.property.1
  · exact
      (actualDifferenceKineticPower_intervalIntegrable left right)
        |>.mono_set <| by
          rw [uIcc_of_le terminal.property.1,
            uIcc_of_le requestedTimePos.le]
          exact Icc_subset_Icc le_rfl terminal.property.2
  · exact
      (actualDifferenceCoefficientMulKineticMass_intervalIntegrable
        left right)
        |>.mono_set <| by
          rw [uIcc_of_le terminal.property.1,
            uIcc_of_le requestedTimePos.le]
          exact Icc_subset_Icc le_rfl terminal.property.2
  · exact ae_mono
      (Measure.restrict_mono
        (Icc_subset_Icc le_rfl terminal.property.2) le_rfl)
      (actualDifferenceKineticPower_ae_le_volume_restrict
        left right)

theorem actualDifferenceKineticMass_eq_zero
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ time ∈ Icc (0 : ℝ) requestedTime,
      actualDifferenceKineticMass left right time = 0 := by
  obtain ⟨bound, boundUpper⟩ :=
    actualDifferenceKineticMass_bounded left right
  apply eq_zero_of_nonneg_le_integral_mul
    requestedTimePos.le
    (actualDifferenceSerrinCoefficient_intervalIntegrable left)
    (actualDifferenceSerrinCoefficient_nonneg left)
    (actualDifferenceKineticMass_continuousOn left right)
    (actualDifferenceKineticMass_nonneg left right)
    boundUpper
  intro time timeMem
  exact
    actualDifferenceKineticMass_le_integral
      left right ⟨time, timeMem⟩

/--
Every actual strong-continuation path retains the source-owned zero
vorticity mode at every time, not merely almost everywhere.  The upgrade is
forced by the continuous whole path and the positive-volume physical
interval.
-/
theorem strongContinuationReceipt_wholePath_zero_row
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime) :
    receipt.wholePath time 0 = 0 := by
  let extendedZeroRow : ℝ → ComplexCoordinateVector :=
    fun actual =>
      receipt.wholePath
        (Set.projIcc
          (0 : ℝ) requestedTime requestedTimePos.le actual) 0
  have extensionContinuous : Continuous extendedZeroRow := by
    exact
      (lp.evalCLM ℂ
          (fun _ : IntegerWavevector =>
            ComplexCoordinateVector)
          2 0).continuous.comp
        (receipt.wholePath.continuous.comp
          continuous_projIcc)
  have zeroRowSubtype :
      ∀ᵐ actual ∂(commonTimeMeasure requestedTime),
        receipt.wholePath actual 0 = 0 := by
    filter_upwards [
      wholePath_eq_transverseLimit_ae receipt,
      transverseLimit_zeroRow_ae receipt] with
        actual pathEq zeroRow
    rw [pathEq, zeroRow]
  rw [commonTimeMeasure_eq_comap_volume] at zeroRowSubtype
  have extensionZeroAE :
      ∀ᵐ actual ∂volume.restrict
          (Icc (0 : ℝ) requestedTime),
        extendedZeroRow actual = 0 := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [zeroRowSubtype] with actual zeroRow
    simpa only [extendedZeroRow,
      Set.projIcc_of_mem requestedTimePos.le
        actual.property] using zeroRow
  have extensionZeroOn :=
    Measure.eqOn_Icc_of_ae_eq
      (μ := volume)
      requestedTimePos.ne
      extensionZeroAE
      extensionContinuous.continuousOn
      continuousOn_const
  have atTime := extensionZeroOn time.property
  simpa only [extendedZeroRow,
    Set.projIcc_of_mem requestedTimePos.le
      time.property] using atTime

/--
Two actual strong-continuation receipts generated from the same lineage and
physical horizon carry the same whole vorticity path.  This is the
same-horizon strong uniqueness consumer of the complete nonlinear
cancellation and the source-generated critical `L¹_t` coefficient.
-/
theorem strongContinuationReceipt_wholePath_unique
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    left.wholePath = right.wholePath := by
  apply DFunLike.ext _ _
  intro time
  have massZero :=
    actualDifferenceKineticMass_eq_zero
      left right time.1 time.property
  rw [actualDifferenceKineticMass_of_mem
    left right time.1 time.property] at massZero
  have differenceZeroRow :
      (left.wholePath time - right.wholePath time) 0 = 0 := by
    rw [lp.coeFn_sub, Pi.sub_apply,
      strongContinuationReceipt_wholePath_zero_row left time,
      strongContinuationReceipt_wholePath_zero_row right time,
      sub_zero]
  have differenceZero :
      left.wholePath time - right.wholePath time = 0 :=
    (puncturedWholeVorticityKineticMass_eq_zero_iff_of_zero_row
      (left.wholePath time - right.wholePath time)
      differenceZeroRow).1 massZero
  exact sub_eq_zero.mp differenceZero

end ActualCoefficient

end ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall
end NavierStokes
end SaturationMonoid
