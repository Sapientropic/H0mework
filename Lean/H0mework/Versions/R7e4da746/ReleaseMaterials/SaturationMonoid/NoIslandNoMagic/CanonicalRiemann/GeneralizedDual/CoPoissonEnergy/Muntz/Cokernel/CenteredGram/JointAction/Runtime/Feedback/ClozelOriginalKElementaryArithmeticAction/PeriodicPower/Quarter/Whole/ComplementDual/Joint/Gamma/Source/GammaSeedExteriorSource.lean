import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.Order.Floor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CompactConductorExterior
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CompactConductorTailReadback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FirstConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.HermitianGammaTauSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.JointLogConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorStrongSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaSeedExterior
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma
open OriginalGamma.Source.CompactConductorTailReadback
noncomputable section
local notation "q" => (1/4:ℝ)
local notation "C" => ConstantDual.seed

macro "gammaSeedExteriorPaid% " field:ident : term => do
  let owner:=Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CompactConductorExterior 0
  let scope:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.CompactConductorExterior
  return Lean.mkIdent (owner.append (scope.append field.getId))
macro "gammaSeedReadPaid% " field:ident : term => do
  let owner:=Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CompactConductorTailReadback 0
  let scope:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.CompactConductorTailReadback
  return Lean.mkIdent (owner.append (scope.append field.getId))

theorem actual_gamma_seed_even : reflectL2 actualGammaSeed=actualGammaSeed := by
  exact (gammaSeedReadPaid% gamma_even_from_actual_logs) C _ _
    (tailGammaPaid% seed_even) (kGammaSeedPaid% seed_log_domain)
    (kGammaFourierPaid% seed_fourier_log_pair)

theorem actual_gamma_seed_stieltjes_exterior :
    ∀ᵐ x : ℝ ∂volume,q < |x| → actualGammaSeed x=-halfStieltjes (intervalConstant q) |x| := by
  apply gammaSeedReadPaid% gamma_field_absolute_exterior
  · exact actual_gamma_seed_even
  · apply gammaSeedReadPaid% gamma_field_positive_ae
    intro test support
    rw [←actual_gamma_seed_source]
    exact (gammaSeedExteriorPaid% compact_exterior_stieltjes) test (intervalConstant q)
      (reflectRestricted_intervalConstant q) support

private def primitive (x t : ℝ) : ℝ := (Real.log (x+t)-Real.log (x-t))/2
private theorem primitive_derivative (x : ℝ) (outside : q<x) (t : ℝ)
    (inside : t∈Icc (0:ℝ) q) : HasDerivAt (primitive x) (x/(x^2-t^2)) t := by
  have firstPositive : 0<x+t := by linarith [inside.1]
  have secondPositive : 0<x-t := by linarith [inside.2]
  have first := (Real.hasDerivAt_log firstPositive.ne').comp t
    ((hasDerivAt_const t x).add (hasDerivAt_id t))
  have second := (Real.hasDerivAt_log secondPositive.ne').comp t
    ((hasDerivAt_const t x).sub (hasDerivAt_id t))
  have actual := (first.sub second).div_const 2
  change HasDerivAt (primitive x) (((x+t)⁻¹*(0+1)-(x-t)⁻¹*(0-1))/2) t at actual
  convert actual using 1
  have denominator : x^2-t^2≠0 := by nlinarith [inside.1,inside.2]
  field_simp [firstPositive.ne',secondPositive.ne',denominator]
  ring

private theorem coefficient_continuous (x : ℝ) (outside : q<x) :
    ContinuousOn (fun t : ℝ=>x/(x^2-t^2)) (Icc (0:ℝ) q) := by
  intro t inside
  have denominator : x^2-t^2≠0 := by nlinarith [inside.1,inside.2]
  exact continuous_const.continuousAt.div
    ((continuous_const.sub (continuous_id.pow 2)).continuousAt) denominator |>.continuousWithinAt

theorem actual_constant_stieltjes_price (x : ℝ) (outside : q<x) :
    halfStieltjes (intervalConstant q) x=(((Real.log (x+q)-Real.log (x-q))/2:ℝ):ℂ) := by
  have continuous : ContinuousOn (fun t : ℝ=>x/(x^2-t^2)) (uIcc (0:ℝ) q) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤q)]
    exact coefficient_continuous x outside
  have legal : IntervalIntegrable (fun t : ℝ=>x/(x^2-t^2)) volume 0 q := continuous.intervalIntegrable
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t inside=>primitive_derivative x outside t (by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤q)] using inside)) legal
  have legalOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤q)).mp legal
  have constant := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (intervalConstant_coeFn q)
  have source : halfStieltjes (intervalConstant q) x=
      ∫ t : ℝ in Ioc 0 q,((x/(x^2-t^2):ℝ):ℂ) := by
    unfold halfStieltjes
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae constant,ae_restrict_mem measurableSet_Ioc] with t read inside
    rw [read ⟨by linarith [inside.1],inside.2⟩,mul_one]
  rw [source]
  change (∫ t : ℝ in Ioc 0 q,Complex.ofRealCLM (x/(x^2-t^2)))=_
  rw [Complex.ofRealCLM.integral_comp_comm legalOn,←intervalIntegral.integral_of_le
    (by norm_num : (0:ℝ)≤q),actual]
  simp only [primitive,add_zero,sub_zero,sub_self,zero_div,sub_zero,Complex.ofRealCLM_apply]

def actualGammaSeedExteriorRaw (x : ℝ) : ℂ :=
  -(((Real.log (|x|+q)-Real.log (|x|-q))/2:ℝ):ℂ)

theorem actual_original_gamma_seed_complete_exterior :
    ∀ᵐ x : ℝ ∂volume,q < |x| → actualGammaSeed x=actualGammaSeedExteriorRaw x := by
  filter_upwards [actual_gamma_seed_stieltjes_exterior] with x source
  intro outside
  rw [source outside,actual_constant_stieltjes_price |x| outside]
  rfl

end
end OriginalGamma.Source.GammaSeedExterior
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
