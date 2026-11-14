import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.UnitLog

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.LogMellin
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
open scoped Topology InnerProductSpace
open private constant_moment compact_mellin_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment
open private compact_memLp compact_origin from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
open private log_top_bound logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private mellin_source_ae from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "E"=>burnolQuarterZeroExtension
local notation "ell"=>CenteredCountingDual.logarithm

private def unitRaw:ℝ→ℂ:=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin.compactRaw (fun _:ℝ=>(1:ℂ))

private theorem unit_read (z:ℂ) (positive:0<z.re):mellin unitRaw z=(q:ℂ)^z/z:=by
  have source:=compact_mellin_read (fun _:ℝ=>(1:ℂ)) (1-z) 0
  rw [show 1-(1-z)=z by ring,logSource_zero,
    constant_moment (1-z) (by simp only [sub_re,one_re];linarith)] at source
  simpa only [unitRaw,show 1-(1-z)=z by ring] using source

private theorem unit_source (z:ℂ) (positive:0<z.re):HasMellin unitRaw z ((q:ℂ)^z/z):=
  ⟨actual_compact_mellin (fun _:ℝ=>(1:ℂ)) continuous_const z positive,unit_read z positive⟩

private theorem log_unit_source (z:ℂ) (positive:0<z.re):
    HasMellin (fun x:ℝ=>(Real.log x:ℂ)*unitRaw x) z
      (((q:ℂ)^z*(Real.log q:ℂ)*z-(q:ℂ)^z)/z^2):=by
  have outside:∀x:ℝ,q < |x| → unitRaw x=0:=by
    intro x beyond
    exact indicator_of_notMem (s:=symmetricInterval q) (fun inside=>not_le_of_gt beyond (abs_le.mpr inside)) (fun _:ℝ=>(1:ℂ))
  have tail:unitRaw=O[atTop](fun x:ℝ=>x^(-(z.re+1))):=by
    simpa only [logSource_zero] using log_top_bound _ q outside 0 (z.re+1)
  have native:=mellin_hasDerivAt_of_isBigO_rpow
    (((compact_memLp (fun _:ℝ=>(1:ℂ)) continuous_const).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    tail (by linarith:z.re<z.re+1) (compact_origin (fun _:ℝ=>(1:ℂ)) continuous_const) positive
  change MellinConvergent (fun t:ℝ=>Real.log t • unitRaw t) z ∧
    HasDerivAt (mellin unitRaw) (mellin (fun t:ℝ=>Real.log t • unitRaw t) z) z at native
  have nonzero:z≠0:=by intro h;rw [h] at positive;norm_num at positive
  have power:HasDerivAt (fun u:ℂ=>(q:ℂ)^u) ((q:ℂ)^z*Complex.log (q:ℂ)) z:=by
    simpa only [id_eq,mul_one] using (hasDerivAt_id z).const_cpow (Or.inl (by norm_num:(q:ℂ)≠0))
  have quotient:HasDerivAt (fun u:ℂ=>(q:ℂ)^u/u)
      (((q:ℂ)^z*Complex.log (q:ℂ)*z-(q:ℂ)^z)/z^2) z:=by
    simpa only [id_eq,mul_one] using! power.div (hasDerivAt_id z) nonzero
  have nearby:(mellin unitRaw)=ᶠ[𝓝 z](fun u:ℂ=>(q:ℂ)^u/u):=by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds positive] with u inside
    exact unit_read u inside
  have derivatives:=nearby.deriv_eq
  rw [native.2.deriv,quotient.deriv,←Complex.ofReal_log (by norm_num:(0:ℝ)≤q)] at derivatives
  have same:(fun x:ℝ=>(Real.log x:ℂ)*unitRaw x)=(fun x:ℝ=>Real.log x • unitRaw x):=by
    funext x
    simp only [Complex.real_smul]
  rw [same]
  refine ⟨native.1,?_⟩
  rw [derivatives]

/-- The original centered plain logarithm has its complete positive-axis Mellin source throughout Re(z)>0. -/
theorem actual_plain_log_hasMellin (z:ℂ) (positive:0<z.re):
    HasMellin (E (ell:Hq):ℝ→ℂ) z ((q:ℂ)^z*(z-1)/z^2):=by
  let raw:ℝ→ℂ:=fun x=>(Real.log x:ℂ)*unitRaw x+(1-(Real.log q:ℂ))*unitRaw x
  have logarithm:=log_unit_source z positive
  have constant:=unit_source z positive
  have combined:=hasMellin_add logarithm.1 (constant.1.const_smul (1-(Real.log q:ℂ)))
  rw [mellin_const_smul,logarithm.2,constant.2] at combined
  have nonzero:z≠0:=by intro h;rw [h] at positive;norm_num at positive
  have price:((q:ℂ)^z*(Real.log q:ℂ)*z-(q:ℂ)^z)/z^2+
      (1-(Real.log q:ℂ)) • ((q:ℂ)^z/z)=(q:ℂ)^z*(z-1)/z^2:=by
    simp only [smul_eq_mul]
    field_simp [nonzero]
    ring
  rw [price] at combined
  have rawSource:HasMellin raw z ((q:ℂ)^z*(z-1)/z^2):=combined
  have localRead:∀ᵐx:ℝ∂volume,x∈symmetricInterval q → (ell:Hq) x=((Real.log x-Real.log q+1:ℝ):ℂ):=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp ArithmeticLogGram.logarithm_coeFn
  apply mellin_source_ae _ raw z _ _ rawSource
  filter_upwards [ae_restrict_of_ae (burnolQuarterZeroExtension_coe (ell:Hq)),
    ae_restrict_of_ae localRead] with x extended source
  dsimp only [raw,unitRaw]
  rw [extended]
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin.compactRaw,
      indicator_of_mem inside,source inside,mul_one,mul_one]
    push_cast
    ring
  · rw [indicator_of_notMem inside,OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin.compactRaw,
      indicator_of_notMem inside,mul_zero,mul_zero,add_zero]

/-- The free Mellin source reads the actual reflected parameter with its exact half-contact. -/
theorem actual_plain_log_reflected_moment (c:BurnolCompletedMellinCoordinate):
    HasMellin (E (ell:Hq):ℝ→ℂ) (1-c.value)
      (-(c.value*(q:ℂ)^(1-c.value)/(1-c.value)^2)):=by
  have source:=actual_plain_log_hasMellin (1-c.value) (by simp only [sub_re,one_re];linarith [c.belowOne])
  convert source using 1
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.LogMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
