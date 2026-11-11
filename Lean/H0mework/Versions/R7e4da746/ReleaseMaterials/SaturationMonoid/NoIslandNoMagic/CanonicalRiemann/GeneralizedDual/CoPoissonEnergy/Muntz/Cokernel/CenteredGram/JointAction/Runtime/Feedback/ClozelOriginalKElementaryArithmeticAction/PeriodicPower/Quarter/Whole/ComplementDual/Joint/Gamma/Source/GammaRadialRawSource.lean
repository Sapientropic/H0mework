import Mathlib.MeasureTheory.Function.JacobianOneDim
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaSeedExteriorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.L2DirectDilation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Raw
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaRadialRaw
open Complex Filter FourierTransform MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalGamma.Source.CountingQuadraticLimit OriginalGamma.Source.CountingQuadratic
open OriginalGamma.Source.KGamma OriginalGamma.Source.GammaSeedExterior
noncomputable section
local notation "q" => (1/4:ℝ)
def gammaSeedRaw (x : ℝ) : ℂ :=
  if q < |x| then actualGammaSeedExteriorRaw x
  else (actualGammaSeed x+actualGammaSeed (-x))/2

theorem actual_gamma_seed_whole_raw :
    (actualGammaSeed:ℝ→ℂ)=ᵐ[volume] gammaSeedRaw := by
  have reflected := Lp.coeFn_compMeasurePreserving actualGammaSeed negMeasurePreserving
  change (reflectL2 actualGammaSeed:ℝ→ℂ)=ᵐ[volume] fun x=>actualGammaSeed (-x) at reflected
  rw [actual_gamma_seed_even] at reflected
  filter_upwards [reflected,actual_original_gamma_seed_complete_exterior] with x even exterior
  unfold gammaSeedRaw
  split_ifs with outside
  · exact exterior outside
  · rw [←even]
    ring

theorem gammaSeedRaw_even (x : ℝ) : gammaSeedRaw (-x)=gammaSeedRaw x := by
  unfold gammaSeedRaw actualGammaSeedExteriorRaw
  rw [abs_neg,neg_neg]
  split_ifs <;> ring

theorem gammaSeedRaw_measurable : Measurable gammaSeedRaw := by
  unfold gammaSeedRaw actualGammaSeedExteriorRaw
  exact Measurable.ite (by measurability)
    (by fun_prop) (((Lp.stronglyMeasurable actualGammaSeed).measurable.add
      ((Lp.stronglyMeasurable actualGammaSeed).measurable.comp measurable_neg)).div_const 2)

private theorem radial_raw (t : ℝ) (positive : 0<t) (value : BurnolL2)
    (raw : ℝ→ℂ) (source : (value:ℝ→ℂ)=ᵐ[volume] raw) :
    (radialOrbit t value:ℝ→ℂ)=ᵐ[volume] fun x=>raw (x/(4*t)) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ=>(4*t)⁻¹*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ:=(volume:Measure ℝ)) (r:=(4*t)⁻¹) (inv_ne_zero (by positivity : 4*t≠0))
  filter_upwards [Lp.coeFn_smul (Real.exp (Real.log (4*t)/2):ℂ)
      (burnolMultiplicativeDilation (-Real.log (4*t)) value),
    burnolMultiplicativeDilation_coeFn (-Real.log (4*t)) value,qmp.ae source] with x scalar dilation read
  unfold radialOrbit
  rw [scalar,Pi.smul_apply,smul_eq_mul,dilation]
  unfold burnolL2RawNormalizedDilation
  rw [Real.exp_neg,Real.exp_log (by positivity : 0<4*t),read,←mul_assoc,
    ←Complex.ofReal_mul,←Real.exp_add]
  rw [show Real.log (4*t)/2+(-Real.log (4*t))/2=0 by ring]
  simp only [Real.exp_zero,Complex.ofReal_one,one_mul]
  congr 1
  ring

private theorem radial_integrable (s : Set ℝ) (hs : MeasurableSet s) (positive : s⊆Ioi 0)
    (coefficient : ℝ→ℂ) (measured : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ=>Real.sqrt t*‖coefficient t‖) s)
    (value : BurnolL2) : IntegrableOn (fun t=>coefficient t • radialOrbit t value) s := by
  have regular : AEStronglyMeasurable (fun t=>coefficient t • radialOrbit t value)
      (volume.restrict s) := measured.aestronglyMeasurable.smul
    (((radialOrbit_continuous value).mono positive).aestronglyMeasurable hs)
  apply (integrable_norm_iff regular).mp
  apply (weighted.const_mul (2*‖value‖)).congr
  filter_upwards [ae_restrict_mem hs] with t inside
  rw [norm_smul,radialOrbit_norm t (positive inside) value]
  ring

private theorem radial_synthesis_raw (s : Set ℝ) (hs : MeasurableSet s) (positive : s⊆Ioi 0)
    (coefficient : ℝ→ℂ) (measured : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ=>Real.sqrt t*‖coefficient t‖) s)
    (value : BurnolL2) (raw : ℝ→ℂ) (rawMeasured : Measurable raw)
    (source : (value:ℝ→ℂ)=ᵐ[volume] raw) :
    (radialSynthesisCLM s hs positive coefficient measured weighted value:ℝ→ℂ)=ᵐ[volume]
      fun x=>∫ t : ℝ in s,coefficient t*raw (x/(4*t)) := by
  rw [radialSynthesisCLM_apply]
  apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn (volume.restrict s) _
    (radial_integrable s hs positive coefficient measured weighted value)
    (fun p : ℝ×ℝ=>coefficient p.1*raw (p.2/(4*p.1)))
    ((measured.comp measurable_fst).mul (rawMeasured.comp (by fun_prop)))
  filter_upwards [ae_restrict_mem hs] with t inside
  filter_upwards [Lp.coeFn_smul (coefficient t) (radialOrbit t value),
    radial_raw t (positive inside) value raw source] with x scalar read
  rw [scalar,Pi.smul_apply,smul_eq_mul,read]

end
end OriginalGamma.Source.GammaRadialRaw
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
