import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeLocalDiracJets
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeSignalGerm

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherEulerKernel
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory PreparationVacuumMixedFieldReturn
open Filter
open scoped Topology ContDiff BigOperators
attribute [local irreducible] nativeJetDensity nativeJetBasis nativeHessian

/-- The source spacetime momentum has both explicit position and holonomic jet inputs. -/
def nativePositionMomentum (field : Fin 289) (mu : Fin 4) (data : BasePoint×NativeFirstJet) : ℝ :=
  fderiv ℝ (nativeLocalAction data.1) data.2 (nativeJetBasis (some mu,field))

/-- Complete Euler on a holonomic two-jet, before any Fourier representation. -/
def nativePositionEuler (point : BasePoint) (jet : NativeSecondJet) (field : Fin 289) : ℝ :=
  fderiv ℝ (nativeLocalAction point) jet.1 (nativeJetBasis (none,field))-
    ∑ mu : Fin 4,fderiv ℝ (nativePositionMomentum field mu) (point,jet.1) (coordinateDirection mu,jet.2 mu)

def nativeEulerSourceDomain : Set NativeFirstJet := {jet | ContDiffAt ℝ 2 nativeJetDensity jet}

theorem nativeEulerSourceDomain_generated : nativeEulerSourceDomain∈𝓝 (0 : NativeFirstJet) := by
  have source : ContDiffAt ℝ 2 nativeJetDensity (0 : NativeFirstJet) := nativeJetDensity_smooth.of_le (by
    change ((2 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top)
  exact source.eventually (by simp)

private theorem sourceMomentum_differentiable (jet : NativeFirstJet) (inside : jet∈nativeEulerSourceDomain)
    (field : Fin 289) (mu : Fin 4) :
    DifferentiableAt ℝ (fun data : NativeFirstJet=>fderiv ℝ nativeJetDensity data (nativeJetBasis (some mu,field))) jet := by
  have regular : ContDiffAt ℝ 2 nativeJetDensity jet := inside
  have source : ContDiffAt ℝ 1 (fun data : NativeFirstJet=>fderiv ℝ nativeJetDensity data (nativeJetBasis (some mu,field))) jet :=
    (regular.fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const
  exact source.differentiableAt (by norm_num)

theorem nativePositionMomentum_fderiv (point : BasePoint) (jet : NativeFirstJet)
    (inside : jet∈nativeEulerSourceDomain) (field : Fin 289) (mu : Fin 4) (position : BasePoint) (direction : NativeFirstJet) :
    fderiv ℝ (nativePositionMomentum field mu) (point,jet) (position,direction)=
      fderiv ℝ (fun data : NativeFirstJet=>fderiv ℝ nativeJetDensity data (nativeJetBasis (some mu,field))) jet direction := by
  have value : nativePositionMomentum field mu=(fun data : BasePoint×NativeFirstJet=>
      fderiv ℝ nativeJetDensity data.2 (nativeJetBasis (some mu,field))) := by
    funext data
    simp only [nativePositionMomentum,nativeLocalAction_atPoint]
  rw [value]
  have outer:=(sourceMomentum_differentiable jet inside field mu).hasFDerivAt
  have generated:=outer.comp (point,jet) (ContinuousLinearMap.snd ℝ BasePoint NativeFirstJet).hasFDerivAt
  change HasFDerivAt (fun data : BasePoint×NativeFirstJet=>
    fderiv ℝ nativeJetDensity data.2 (nativeJetBasis (some mu,field))) _ (point,jet) at generated
  rw [generated.fderiv]
  rfl

theorem nativePositionEuler_original (point : BasePoint) (jet : NativeSecondJet)
    (inside : jet.1∈nativeEulerSourceDomain) (field : Fin 289) :
    nativePositionEuler point jet field=nativeEulerDensityJet jet field := by
  simp only [nativePositionEuler,nativeEulerDensityJet,nativeLocalAction_atPoint]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  exact nativePositionMomentum_fderiv point jet.1 inside field mu (coordinateDirection mu) (jet.2 mu)

theorem nativePositionEuler_ray_original (point : BasePoint) (jet : NativeSecondJet) (field : Fin 289) :
    (fun a : ℝ=>nativePositionEuler point (a • jet) field)=ᶠ[𝓝 0]
      fun a=>nativeEulerDensityJet (a • jet) field := by
  have rayContinuous : Continuous (fun a : ℝ=>a • jet.1) := continuous_id.smul continuous_const
  have near : ∀ᶠ a : ℝ in 𝓝 0,a • jet.1∈nativeEulerSourceDomain :=
    (rayContinuous.continuousAt (x:= (0 : ℝ))).eventually_mem
      (by simpa only [zero_smul] using nativeEulerSourceDomain_generated)
  filter_upwards [near] with a ha
  exact nativePositionEuler_original point (a • jet) ha field

theorem nativePositionEuler_source_linear (point : BasePoint) (jet : NativeSecondJet) (field : Fin 289) :
    HasDerivAt (fun a : ℝ=>nativePositionEuler point (a • jet) field) (nativeEulerLinearJet jet field) 0 :=
  (nativeEulerDensity_linear jet field).congr_of_eventuallyEq (nativePositionEuler_ray_original point jet field)

theorem nativeEulerDensity_source_smooth (field : Fin 289) :
    ContDiffAt ℝ ∞ (fun jet : NativeSecondJet=>nativeEulerDensityJet jet field) 0 := by
  have value : ContDiffAt ℝ ∞ (fun data : NativeFirstJet=>fderiv ℝ nativeJetDensity data (nativeJetBasis (none,field))) 0 :=
    (nativeJetDensity_smooth.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const
  have differential (mu : Fin 4) : ContDiffAt ℝ ∞ (fun jet : NativeSecondJet=>
      fderiv ℝ (fun data : NativeFirstJet=>fderiv ℝ nativeJetDensity data (nativeJetBasis (some mu,field))) jet.1 (jet.2 mu)) 0 := by
    have source := (nativeDensityMomentum_smooth field (some mu)).fderiv_right (m:=∞) (by simp)
    exact (source.comp (f:=fun jet : NativeSecondJet=>jet.1) 0 contDiffAt_fst).clm_apply (by fun_prop)
  unfold nativeEulerDensityJet
  exact (value.comp (f:=fun jet : NativeSecondJet=>jet.1) 0 contDiffAt_fst).sub
    (ContDiffAt.sum (fun mu _=>differential mu))

/-- The complete native ordinary remainder has the original identical-leg factor one half. -/
def nativeEulerQuadratic (jet : NativeSecondJet) (field : Fin 289) : ℝ :=
  (1/2)*fderiv ℝ (fun data : NativeSecondJet=>fderiv ℝ (fun state : NativeSecondJet=>nativeEulerDensityJet state field) data)
    0 jet jet

theorem nativeEulerQuadratic_generated (jet : NativeSecondJet) (field : Fin 289) :
    HasDerivAt (fun a : ℝ=>fderiv ℝ (fun state : NativeSecondJet=>nativeEulerDensityJet state field) (a • jet) jet)
      (2*nativeEulerQuadratic jet field) 0 := by
  have source := ((nativeEulerDensity_source_smooth field).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have ray : HasDerivAt (fun a : ℝ=>a • jet) jet 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const jet
  have generated := (source.comp_hasDerivAt_of_eq 0 ray (by simp)).clm_apply (hasDerivAt_const (0 : ℝ) jet)
  convert! generated using 1
  simp only [Function.comp_apply,zero_smul,map_zero,add_zero,nativeEulerQuadratic]
  ring

def signalSecondJet (signal : BasePoint→Field289) (point : BasePoint) : NativeSecondJet :=
  (signalFirstJet signal point,fun mu=>fieldDirectionalDerivative (signalFirstJet signal) point mu)

theorem signalFirstJet_source_smooth (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) : ContDiffAt ℝ 1 (signalFirstJet signal) point := by
  have differential := smooth.fderiv_right (m:=1) (by norm_num)
  have each (mu : Fin 4) : ContDiffAt ℝ 1 (fun position=>fieldDirectionalDerivative signal position mu) point :=
    differential.clm_apply contDiffAt_const
  exact (smooth.of_le (by norm_num)).prodMk (contDiffAt_pi.2 each)

/-- A genuine spacetime field reads its value and momentum divergence from the identical mother density. -/
def nativeHolonomicEuler (signal : BasePoint→Field289) (point : BasePoint) (field : Fin 289) : ℝ :=
  fderiv ℝ (nativeLocalAction point) (signalFirstJet signal point) (nativeJetBasis (none,field))-
    ∑ mu : Fin 4,fieldDirectionalDerivative
      (fun position=>fderiv ℝ (nativeLocalAction position) (signalFirstJet signal position) (nativeJetBasis (some mu,field))) point mu

theorem nativeHolonomicEuler_original (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (inside : signalFirstJet signal point∈nativeEulerSourceDomain)
    (field : Fin 289) :
    nativeHolonomicEuler signal point field=nativeEulerDensityJet (signalSecondJet signal point) field := by
  unfold nativeHolonomicEuler nativeEulerDensityJet signalSecondJet
  simp only [nativeLocalAction_atPoint]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  have differentiated := (sourceMomentum_differentiable (signalFirstJet signal point) inside field mu).hasFDerivAt.comp point
    ((signalFirstJet_source_smooth signal point smooth).differentiableAt (by norm_num) |>.hasFDerivAt)
  change HasFDerivAt (fun position=>fderiv ℝ nativeJetDensity (signalFirstJet signal position)
    (nativeJetBasis (some mu,field))) _ point at differentiated
  rw [fieldDirectionalDerivative,differentiated.fderiv,fieldDirectionalDerivative]
  rfl

theorem nativeHolonomicEuler_position (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (inside : signalFirstJet signal point∈nativeEulerSourceDomain)
    (field : Fin 289) :
    nativePositionEuler point (signalSecondJet signal point) field=nativeHolonomicEuler signal point field := by
  rw [nativePositionEuler_original point (signalSecondJet signal point) inside field,
    nativeHolonomicEuler_original signal point smooth inside field]

private theorem directionalDerivative_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : BasePoint→E) (point : BasePoint) (differentiable : DifferentiableAt ℝ f point) (a : ℝ) (mu : Fin 4) :
    fieldDirectionalDerivative (fun position=>a • f position) point mu=a • fieldDirectionalDerivative f point mu := by
  have generated:=differentiable.hasFDerivAt.const_smul a
  change HasFDerivAt (fun position=>a • f position) _ point at generated
  unfold fieldDirectionalDerivative
  rw [generated.fderiv]
  rfl

theorem signalFirstJet_smul (signal : BasePoint→Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) (a : ℝ) :
    signalFirstJet (fun position=>a • signal position) point=a • signalFirstJet signal point := by
  apply Prod.ext
  · rfl
  · funext mu
    exact directionalDerivative_smul signal point differentiable a mu

theorem signalSecondJet_smul (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (a : ℝ) :
    signalSecondJet (fun position=>a • signal position) point=a • signalSecondJet signal point := by
  have derivative:=(signalFirstJet_source_smooth signal point smooth).differentiableAt (by norm_num)
  have nearSmooth:=smooth.eventually (by norm_num)
  have values : (signalFirstJet (fun position=>a • signal position))=ᶠ[𝓝 point]
      fun position=>a • signalFirstJet signal position := by
    filter_upwards [nearSmooth] with position hs
    exact signalFirstJet_smul signal position (hs.differentiableAt (by norm_num)) a
  apply Prod.ext
  · exact signalFirstJet_smul signal point (smooth.differentiableAt (by norm_num)) a
  · funext mu
    change fieldDirectionalDerivative (signalFirstJet (fun position=>a • signal position)) point mu=_
    rw [fieldDirectionalDerivative,values.fderiv_eq]
    exact directionalDerivative_smul (signalFirstJet signal) point derivative a mu

theorem nativeHolonomicEuler_ray_original (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (field : Fin 289) :
    (fun a : ℝ=>nativeHolonomicEuler (fun position=>a • signal position) point field)=ᶠ[𝓝 0]
      fun a=>nativeEulerDensityJet (a • signalSecondJet signal point) field := by
  have rayContinuous : Continuous (fun a : ℝ=>a • signalFirstJet signal point) := continuous_id.smul continuous_const
  have near : ∀ᶠ a : ℝ in 𝓝 0,a • signalFirstJet signal point∈nativeEulerSourceDomain :=
    (rayContinuous.continuousAt (x:= (0 : ℝ))).eventually_mem
      (by simpa only [zero_smul] using nativeEulerSourceDomain_generated)
  filter_upwards [near] with a ha
  have regular := smooth.const_smul a
  have domain : signalFirstJet (fun position=>a • signal position) point∈nativeEulerSourceDomain := by
    rwa [signalFirstJet_smul signal point (smooth.differentiableAt (by norm_num)) a]
  rw [nativeHolonomicEuler_original _ point regular domain field,signalSecondJet_smul signal point smooth a]

theorem nativeHolonomicEuler_source_linear (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (field : Fin 289) :
    HasDerivAt (fun a : ℝ=>nativeHolonomicEuler (fun position=>a • signal position) point field)
      (nativeEulerLinearJet (signalSecondJet signal point) field) 0 :=
  (nativeEulerDensity_linear (signalSecondJet signal point) field).congr_of_eventuallyEq
    (nativeHolonomicEuler_ray_original signal point smooth field)

theorem nativeEulerDensity_ray_quadratic (jet : NativeSecondJet) (field : Fin 289) :
    HasDerivAt (deriv (fun a : ℝ=>nativeEulerDensityJet (a • jet) field)) (2*nativeEulerQuadratic jet field) 0 := by
  have smooth : ContDiffAt ℝ 1 (fun data : NativeSecondJet=>nativeEulerDensityJet data field) 0 :=
    (nativeEulerDensity_source_smooth field).of_le (by
      change ((1 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  have nearSmooth:=smooth.eventually (by norm_num)
  have rayContinuous : Continuous (fun a : ℝ=>a • jet) := continuous_id.smul continuous_const
  have near : ∀ᶠ a : ℝ in 𝓝 0,ContDiffAt ℝ 1 (fun data : NativeSecondJet=>nativeEulerDensityJet data field) (a • jet) :=
    (rayContinuous.tendsto (0 : ℝ)).eventually (by simpa only [zero_smul] using nearSmooth)
  have derivatives : deriv (fun a : ℝ=>nativeEulerDensityJet (a • jet) field)=ᶠ[𝓝 0]
      fun a=>fderiv ℝ (fun data : NativeSecondJet=>nativeEulerDensityJet data field) (a • jet) jet := by
    filter_upwards [near] with a ha
    have ray : HasDerivAt (fun r : ℝ=>r • jet) jet a := by simpa using (hasDerivAt_id a).smul_const jet
    exact ((ha.differentiableAt (by norm_num) |>.hasFDerivAt).comp_hasDerivAt a ray).deriv
  exact (nativeEulerQuadratic_generated jet field).congr_of_eventuallyEq derivatives

theorem nativeHolonomicEuler_source_quadratic (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (field : Fin 289) :
    HasDerivAt (deriv (fun a : ℝ=>nativeHolonomicEuler (fun position=>a • signal position) point field))
      (2*nativeEulerQuadratic (signalSecondJet signal point) field) 0 :=
  (nativeEulerDensity_ray_quadratic (signalSecondJet signal point) field).congr_of_eventuallyEq
    (nativeHolonomicEuler_ray_original signal point smooth field).deriv

end LowEnergy.SourcePropagationMotherEulerKernel
