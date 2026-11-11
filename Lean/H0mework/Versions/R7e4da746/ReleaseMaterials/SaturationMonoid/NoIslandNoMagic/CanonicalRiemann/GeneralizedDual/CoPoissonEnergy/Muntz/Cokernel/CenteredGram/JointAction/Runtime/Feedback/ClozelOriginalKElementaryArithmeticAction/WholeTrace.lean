import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RieszEulerDomain

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.WholeTrace
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
open private dual_dilation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.Source
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "K"=>burnolCompletedMellinRieszVector
local notation "D"=>burnolMultiplicativeDilation
local notation "C"=>ConstantDual.seed

/-- The original jump law makes the corrected inside exactly the clamped outer source. -/
def raw (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
  burnolRieszStatePositiveOuterRaw c (max q |x|)+
    Kernel.beta c*burnolTruncatedFourierRaw (intervalConstant q) x

theorem raw_continuous (c:BurnolCompletedMellinCoordinate) : Continuous (raw c) := by
  have clamped:Continuous (fun x:ℝ=>max q |x|) := by fun_prop
  have powered:Continuous (fun x:ℝ=>((max q |x|:ℝ):ℂ)^(-star c.value)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have point:ContinuousAt (fun t:ℝ=>(t:ℂ)^(-star c.value)) (max q |x|) :=
      Complex.continuousAt_ofReal_cpow_const (max q |x|) (-star c.value)
        (Or.inr (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<q) (le_max_left _ _))))
    exact ContinuousAt.comp (f:=fun y:ℝ=>max q |y|)
      (g:=fun t:ℝ=>(t:ℂ)^(-star c.value)) point clamped.continuousAt
  have fourier:=burnolRadiusTruncatedFourierRaw_continuous
    (burnolRieszSingleFourierSource c:Hq)
  have unitFourier:=burnolTruncatedFourierRaw_continuous (intervalConstant q)
  unfold raw burnolRieszStatePositiveOuterRaw
  fun_prop

private theorem source_outside (c:BurnolCompletedMellinCoordinate) (x:ℝ) (outside:q< |x|) :
    burnolRieszStateRaw c x=burnolRieszStatePositiveOuterRaw c |x| := by
  rcases le_total 0 x with positive|negative
  · rw [abs_of_nonneg positive] at outside ⊢
    exact burnolRieszStateRaw_eq_positiveOuter c outside
  · rw [abs_of_nonpos negative] at outside ⊢
    rw [←burnolRieszStateRaw_even c x]
    exact burnolRieszStateRaw_eq_positiveOuter c outside

/-- This representative is read from the actual K, original unit and its Fourier face. -/
theorem raw_read (c:BurnolCompletedMellinCoordinate) :
    (RieszEulerDomain.value c:ℝ→ℂ)=ᵐ[volume] raw c := by
  filter_upwards [Lp.coeFn_add ((K c:BurnolL2)-Kernel.A c • C)
      (Kernel.beta c • fourierL2 C),Lp.coeFn_sub (K c:BurnolL2) (Kernel.A c • C),
    Lp.coeFn_smul (Kernel.A c) C,Lp.coeFn_smul (Kernel.beta c) (fourierL2 C),
    burnolRieszState_ae_raw c,ConstantDual.seed_coeFn,
    burnolFourierL2_zeroExtension_ae_eq_raw (intervalConstant q)]
      with x addition subtraction aScalar bScalar kernel unit fourier
  change ((K c:BurnolL2)-Kernel.A c • C+Kernel.beta c • fourierL2 C) x=raw c x
  rw [addition,Pi.add_apply,subtraction,Pi.sub_apply,aScalar,bScalar]
  change (K c:BurnolL2) x-Kernel.A c*C x+Kernel.beta c*fourierL2 C x=raw c x
  change fourierL2 C x=burnolTruncatedFourierRaw (intervalConstant q) x at fourier
  rw [kernel,unit,fourier]
  by_cases inside:|x|≤q
  · rw [ConstantDual.seedRaw,if_pos inside,raw,max_eq_left inside,
      burnolRieszStateRaw_eq_quarterInner_of_mem c (abs_le.mp inside)]
    have jump:=Kernel.position_jump c
    linear_combination -jump
  · rw [ConstantDual.seedRaw,if_neg inside,mul_zero,sub_zero,raw,max_eq_right (le_of_not_ge inside),
      source_outside c x (lt_of_not_ge inside)]

def value (c:BurnolCompletedMellinCoordinate) (N:ℕ) : BurnolL2 :=
  DualSource.source N (RieszEulerDomain.value c)
def velocity (c:BurnolCompletedMellinCoordinate) (N:ℕ) : BurnolL2 :=
  DualSource.source N (RieszEulerDomain.velocity c)

def countedRaw (c:BurnolCompletedMellinCoordinate) (N:ℕ) (x:ℝ) : ℂ :=
  (∑n∈Finset.Ico 1 N,raw c ((n:ℝ)*x))-
    ∫a:ℝ in Ioc 0 (N:ℝ),raw c (a*x)

theorem counted_continuous (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    Continuous (countedRaw c N) := by
  have joint:Continuous (fun p:ℝ×ℝ=>raw c (p.2*p.1)) := (raw_continuous c).comp (by fun_prop)
  have integral:Continuous (fun x:ℝ=>∫a:ℝ in Icc 0 (N:ℝ),raw c (a*x)) :=
    continuous_parametric_integral_of_continuous (μ:=volume) (f:=fun x a:ℝ=>raw c (a*x))
      joint isCompact_Icc
  simp only [integral_Icc_eq_integral_Ioc] at integral
  unfold countedRaw
  exact (continuous_finsetSum _ (fun n _=>(raw_continuous c).comp (by fun_prop))).sub integral

theorem counted_read (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    (value c N:ℝ→ℂ)=ᵐ[volume] countedRaw c N := by
  let X:=RieszEulerDomain.value c
  have normalization:((∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 a X:BurnolL2):ℝ→ℂ)=ᵐ[volume]
      fun x=>∫a:ℝ in Ioc 0 (N:ℝ),raw c (a*x) := by
    apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn
      (volume.restrict (Ioc 0 (N:ℝ))) _ (ContinuousChannels.channel_integrable 1 N X)
      (fun p:ℝ×ℝ=>raw c (p.1*p.2)) ((raw_continuous c).measurable.comp (by fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact DualSourceRaw.channel_coeFn X (raw c) (raw_read c) a ha.1
  have channels:∀ᵐx:ℝ ∂volume,∀n:{n:ℕ//n∈Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n:ℝ) X x=raw c ((n:ℝ)*x) := by
    apply ae_all_iff.mpr
    intro n
    exact DualSourceRaw.channel_coeFn X (raw c) (raw_read c) n
      (by exact_mod_cast (Finset.mem_Ico.mp n.property).1)
  filter_upwards [Lp.coeFn_sub (∑n∈Finset.Ico 1 N,ContinuousChannels.channel 1 n X)
      (∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 a X),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n=>ContinuousChannels.channel 1 n X),
    normalization,channels] with x subtraction sum integral channel
  change ((∑n∈Finset.Ico 1 N,ContinuousChannels.channel 1 n X)-
      ∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 a X:BurnolL2) x=countedRaw c N x
  rw [subtraction,Pi.sub_apply,sum,integral]
  unfold countedRaw
  congr 1
  exact Finset.sum_congr rfl (fun n hn=>channel ⟨n,hn⟩)

/-- The same actual finite action generates the graph before its unit trace is read. -/
theorem actual_derivative (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    HasDerivAt (fun t:ℝ=>D t (value c N)) (velocity c N) 0 := by
  have source:=(((CountingDual.sourceCLM N).adjoint).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (RieszEulerDomain.strong_derivative c)
  have actual:HasDerivAt (fun t:ℝ=>DualSource.source N (D t (RieszEulerDomain.value c)))
      (velocity c N) 0 := by
    convert! source using 1
    · funext t
      exact CountingDual.dual_eq_adjoint N (D t (RieszEulerDomain.value c))
    · exact CountingDual.dual_eq_adjoint N (RieszEulerDomain.velocity c)
  convert! actual using 1
  funext t
  exact (dual_dilation N t (RieszEulerDomain.value c)).symm

end OriginalKElementaryArithmeticAction.WholeTrace
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
