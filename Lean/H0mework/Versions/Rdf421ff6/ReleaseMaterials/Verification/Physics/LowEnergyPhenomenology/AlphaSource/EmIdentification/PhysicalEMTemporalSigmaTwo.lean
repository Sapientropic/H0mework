import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMTemporalPrice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFiniteStaticRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPoleRead
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! The source EM static row: the original weighted Pi row is a finite sum of the unchanged
per-coordinate static polarization, so the linear-age price integrates to an exact
`sigma^2` Laplace price and the original leading coefficient cancels for every pole
order strictly above one. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMTemporal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumPhysicalGradeZeroRead
open PreparationVacuumPhysicalHalfAxis
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace Interval
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedConstraintRead
open ActualDressedNumberZero ActualDressedNumberField ActualDressedLeftFreeJet
open ActualDressedSourcePreparation ActualDressedFiniteStaticRead ActualDressedStaticPole
open ActualDressedSylvester
attribute [local irreducible] noetherReaderContact jointResolvent
  jointCResolvent physicalTime gradeZeroProjection dressedEulerObserver freeCompressionCurrent
  dressedStaticPolarization dressedStaticPoleOrder dressedStaticPoleLeading laplaceWeight

/-- The original weighted EM Pi row keeps every source column and each independent
Laplace frequency; no global all-289 matrix claim is made. -/
def emTemporalPi (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (j : Fin 289) : ℂ :=
  ∑i : Fin 289,((sourcePhaseGaugeField 0) i:ℂ)*dressedStaticPolarization event transfer lambda i j

/-- The weighted EM leading coefficient is the same finite sum of the original entries. -/
def emTemporalLeading (event : DressedEvent) (j : Fin 289) : ℂ :=
  ∑i : Fin 289,((sourcePhaseGaugeField 0) i:ℂ)*dressedStaticPoleLeading event i j

/-- The weighted EM row is the original `Ioi 0` Laplace transform of the EM temporal jet. -/
private theorem em_pi_laplace (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (j : Fin 289) :
    emTemporalPi event transfer lambda j=
      ∫t : ℝ in Ioi 0,laplaceWeight lambda t*
        emTemporalJet event transfer (fieldUnit j) t := by
  have eachPi (i : Fin 289) : dressedStaticPolarization event transfer lambda i j=
      ∫t : ℝ in Ioi 0,laplaceWeight lambda t*
        finiteConstantFieldSlope event transfer (fieldUnit j) t i :=
    dressed_static_polarization_finite event transfer lambda positive i j
  have eachInt (i : Fin 289) : IntegrableOn
      (fun t=>((sourcePhaseGaugeField 0) i:ℂ)*
        (laplaceWeight lambda t*finiteConstantFieldSlope event transfer (fieldUnit j) t i))
      (Ioi (0:ℝ)) :=
    (finite_static_integrand_integrable event transfer (fieldUnit j) lambda positive i).const_mul _
  have pointwise (t : ℝ) : laplaceWeight lambda t*emTemporalJet event transfer (fieldUnit j) t=
      ∑i : Fin 289,((sourcePhaseGaugeField 0) i:ℂ)*
        (laplaceWeight lambda t*finiteConstantFieldSlope event transfer (fieldUnit j) t i) := by
    unfold emTemporalJet
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [←finite_constant_field_slope_actual]
    ring
  unfold emTemporalPi
  rw [show (∫t : ℝ in Ioi 0,laplaceWeight lambda t*emTemporalJet event transfer (fieldUnit j) t)=
      ∫t : ℝ in Ioi 0,∑i : Fin 289,((sourcePhaseGaugeField 0) i:ℂ)*
        (laplaceWeight lambda t*finiteConstantFieldSlope event transfer (fieldUnit j) t i) from
      integral_congr_ae (ae_of_all _ fun t=>pointwise t)]
  rw [MeasureTheory.integral_finsetSum _ (fun i _=>eachInt i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [eachPi i]
  exact (integral_const_mul _ _).symm

private theorem em_moment_integral (n : ℕ) (sigma : ℝ) (positive : 0<sigma) :
    (∫t : ℝ in Ioi 0,t^n*Real.exp (-(sigma*t)))=
      (1/sigma)^(n+1)*(n.factorial:ℝ) := by
  have source:=Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a:=(n:ℝ)+1) (r:=sigma) (by positivity) positive
  have cast : (n:ℝ)+1=((n+1:ℕ):ℝ) := by norm_cast
  rw [cast,Real.rpow_natCast] at source
  simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] using source

private theorem em_moment_integrable (n : ℕ) (sigma : ℝ) (positive : 0<sigma) :
    IntegrableOn (fun t : ℝ=>t^n*Real.exp (-(sigma*t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [em_moment_integral n sigma positive]
  positivity

private theorem em_linear_integrable (sigma : ℝ) (positive : 0<sigma) :
    IntegrableOn (fun t : ℝ=>Real.exp (-(sigma*t))*(1+t)) (Ioi 0) := by
  have zeroth : IntegrableOn (fun t : ℝ=>Real.exp (-(sigma*t))) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using em_moment_integrable 0 sigma positive
  have first : IntegrableOn (fun t : ℝ=>t*Real.exp (-(sigma*t))) (Ioi 0) := by
    simpa only [pow_one] using em_moment_integrable 1 sigma positive
  have rewrite : (fun t : ℝ=>Real.exp (-(sigma*t))*(1+t))=
      fun t : ℝ=>Real.exp (-(sigma*t))+t*Real.exp (-(sigma*t)) := by
    funext t;ring
  rw [rewrite]
  exact zeroth.add first

private theorem em_linear_integral (sigma : ℝ) (positive : 0<sigma) :
    (∫t : ℝ in Ioi 0,Real.exp (-(sigma*t))*(1+t))=1/sigma+1/sigma^2 := by
  have zeroth : IntegrableOn (fun t : ℝ=>Real.exp (-(sigma*t))) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using em_moment_integrable 0 sigma positive
  have first : IntegrableOn (fun t : ℝ=>t*Real.exp (-(sigma*t))) (Ioi 0) := by
    simpa only [pow_one] using em_moment_integrable 1 sigma positive
  have rewrite : (fun t : ℝ=>Real.exp (-(sigma*t))*(1+t))=
      fun t : ℝ=>Real.exp (-(sigma*t))+t*Real.exp (-(sigma*t)) := by
    funext t;ring
  rw [rewrite,integral_add zeroth first]
  have zero:=em_moment_integral 0 sigma positive
  have one:=em_moment_integral 1 sigma positive
  simp only [pow_zero,one_mul,pow_one,pow_succ,Nat.factorial_zero,Nat.factorial_one,
    Nat.cast_one,mul_one] at zero one
  rw [zero,one]
  field_simp [positive.ne']

/-- The unchanged source price is nonnegative. -/
private theorem em_temporal_price_nonneg (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) : 0≤emTemporalPrice event transfer force := by
  unfold emTemporalPrice
  positivity

/-- The weighted EM static row is Laplace-bounded by the exact source `1/σ+1/σ²` moment. -/
private theorem em_pi_norm (event : DressedEvent) (transfer : PhysicalMomentum)
    (sigma : ℝ) (positive : 0<sigma) (j : Fin 289) :
    ‖emTemporalPi event transfer (sigma:ℂ) j‖≤
      emTemporalPrice event transfer (fieldUnit j)*(1/sigma+1/sigma^2) := by
  have re : (sigma:ℂ).re=sigma := Complex.ofReal_re sigma
  have realPositive : 0<(sigma:ℂ).re := by rwa [re]
  rw [em_pi_laplace event transfer (sigma:ℂ) realPositive j]
  have paid : IntegrableOn
      (fun t=>laplaceWeight (sigma:ℂ) t*emTemporalJet event transfer (fieldUnit j) t)
      (Ioi (0:ℝ)) := by
    have rewrite : (fun t=>laplaceWeight (sigma:ℂ) t*emTemporalJet event transfer (fieldUnit j) t)=
        fun t=>∑i : Fin 289,((sourcePhaseGaugeField 0) i:ℂ)*
          (laplaceWeight (sigma:ℂ) t*finiteConstantFieldSlope event transfer (fieldUnit j) t i) := by
      funext t
      unfold emTemporalJet
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [←finite_constant_field_slope_actual]
      ring
    rw [rewrite]
    apply integrable_finsetSum
    intro i _
    exact (finite_static_integrand_integrable event transfer (fieldUnit j) (sigma:ℂ)
      realPositive i).const_mul _
  have majorant : IntegrableOn
      (fun t=>emTemporalPrice event transfer (fieldUnit j)*(Real.exp (-(sigma*t))*(1+t)))
      (Ioi (0:ℝ)) :=
    (em_linear_integrable sigma positive).const_mul _
  calc ‖∫t : ℝ in Ioi 0,laplaceWeight (sigma:ℂ) t*emTemporalJet event transfer (fieldUnit j) t‖
      ≤∫t : ℝ in Ioi 0,‖laplaceWeight (sigma:ℂ) t*
          emTemporalJet event transfer (fieldUnit j) t‖ :=
        norm_integral_le_integral_norm _
    _ ≤∫t : ℝ in Ioi 0,emTemporalPrice event transfer (fieldUnit j)*
          (Real.exp (-(sigma*t))*(1+t)) := by
        apply integral_mono_ae paid.norm majorant
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t future
        rw [norm_mul,laplace_norm,re]
        have source:=actual_em_temporal_jet_linear_price event transfer (fieldUnit j) t
        rw [abs_of_pos future] at source
        exact (mul_le_mul_of_nonneg_left source (Real.exp_nonneg _)).trans_eq (by ring)
    _ =emTemporalPrice event transfer (fieldUnit j)*
          (∫t : ℝ in Ioi 0,Real.exp (-(sigma*t))*(1+t)) :=
        integral_const_mul _ _
    _ =emTemporalPrice event transfer (fieldUnit j)*(1/sigma+1/sigma^2) := by
        rw [em_linear_integral sigma positive]

/-- The source-native `σ²` price on the unchanged weighted EM row: the exact
`(1+t)` Laplace moment gives `σ+1`, bounded by the factor two when `σ≤1`. -/
theorem actual_em_temporal_pi_sigma_two_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (sigma : ℝ) (positive : 0<sigma) (small : sigma≤1) (j : Fin 289) :
    sigma^2*‖emTemporalPi event transfer (sigma:ℂ) j‖≤
      2*emTemporalPrice event transfer (fieldUnit j) := by
  have bound:=em_pi_norm event transfer sigma positive j
  have nonneg:=em_temporal_price_nonneg event transfer (fieldUnit j)
  calc sigma^2*‖emTemporalPi event transfer (sigma:ℂ) j‖
      ≤ sigma^2*(emTemporalPrice event transfer (fieldUnit j)*(1/sigma+1/sigma^2)) :=
        mul_le_mul_of_nonneg_left bound (pow_nonneg positive.le 2)
    _ =emTemporalPrice event transfer (fieldUnit j)*(sigma+1) := by
        field_simp [positive.ne']
    _ ≤emTemporalPrice event transfer (fieldUnit j)*2 :=
        mul_le_mul_of_nonneg_left (by linarith) nonneg
    _ =2*emTemporalPrice event transfer (fieldUnit j) := by ring

/-- Pole order strictly above one kills the unchanged weighted EM leading coefficient:
the source-native linear price gives `σ²` damping, so `σ^(2m)` times the EM row is
squeezed to zero whenever `2m-2>0`. No order-one claim is made. -/
theorem actual_em_temporal_leading_zero_of_order_gt_one (event : DressedEvent)
    (high : 1<dressedStaticPoleOrder event) (j : Fin 289) :
    emTemporalLeading event j=0 := by
  let order:=2*dressedStaticPoleOrder event
  let sourcePrice:=2*emTemporalPrice event 0 (fieldUnit j)
  have gap : 0<order-2 := by dsimp only [order];omega
  have power : Tendsto (fun sigma : ℝ=>sigma^(order-2)*sourcePrice)
      (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 0) := by
    have identity : Tendsto (fun sigma : ℝ=>sigma) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℝ)) :=
      tendsto_id.mono_left inf_le_left
    simpa only [zero_pow gap.ne',zero_mul] using
      (identity.pow (order-2)).mul_const sourcePrice
  have small : ∀ᶠsigma : ℝ in nhdsWithin 0 (Ioi (0:ℝ)),sigma<1 :=
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono inf_le_left
  have zero : Tendsto (fun sigma : ℝ=>(sigma:ℂ)^order*emTemporalPi event 0 (sigma:ℂ) j)
      (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 0) := by
    apply squeeze_zero_norm' _ power
    filter_upwards [self_mem_nhdsWithin,small] with sigma positive near
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    have split : order=(order-2)+2 := by omega
    rw [split,pow_add,mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (actual_em_temporal_pi_sigma_two_price event 0 sigma positive near.le j)
      (pow_nonneg positive.le _)
  have each (i : Fin 289) : Tendsto
      (fun sigma : ℝ=>((sourcePhaseGaugeField 0) i:ℂ)*((sigma:ℂ)^order*
        dressedStaticPolarization event 0 (sigma:ℂ) i j))
      (nhdsWithin 0 (Ioi (0:ℝ)))
      (𝓝 (((sourcePhaseGaugeField 0) i:ℂ)*dressedStaticPoleLeading event i j)) :=
    (dressed_static_pole_leading_limit event i j).const_mul _
  have sum : Tendsto
      (fun sigma : ℝ=>∑i : Fin 289,((sourcePhaseGaugeField 0) i:ℂ)*((sigma:ℂ)^order*
        dressedStaticPolarization event 0 (sigma:ℂ) i j))
      (nhdsWithin 0 (Ioi (0:ℝ)))
      (𝓝 (emTemporalLeading event j)) := by
    unfold emTemporalLeading
    exact tendsto_finsetSum Finset.univ (fun i _=>each i)
  have limit : Tendsto (fun sigma : ℝ=>(sigma:ℂ)^order*emTemporalPi event 0 (sigma:ℂ) j)
      (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (emTemporalLeading event j)) :=
    sum.congr' (by
      filter_upwards with sigma
      unfold emTemporalPi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
  exact tendsto_nhds_unique limit zero

end LowEnergy.GaussComposite.ActualDressedEMTemporal
