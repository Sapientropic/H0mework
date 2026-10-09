import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationSectorEulerIdentification

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField
open StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open PreparationVacuumMixedFieldReturn
open scoped Topology ContDiff BigOperators
attribute [local irreducible] nativeDensity nativeConfiguration nativePoint nativeJetDensity nativeJetBasis

theorem signalFirstJet_add (first second : BasePoint→Field289) (point : BasePoint)
    (firstDifferentiable : DifferentiableAt ℝ first point)
    (secondDifferentiable : DifferentiableAt ℝ second point) :
    signalFirstJet (fun position=>first position+second position) point=
      signalFirstJet first point+signalFirstJet second point := by
  apply Prod.ext
  · rfl
  · funext mu
    have source:=firstDifferentiable.hasFDerivAt.add secondDifferentiable.hasFDerivAt
    change HasFDerivAt (fun position=>first position+second position) _ point at source
    change fieldDirectionalDerivative (fun position=>first position+second position) point mu=_
    rw [fieldDirectionalDerivative,source.fderiv]
    rfl

theorem signalFirstJet_variation (signal variation : BasePoint→Field289) (point : BasePoint)
    (smoothSignal : DifferentiableAt ℝ signal point)
    (smoothVariation : DifferentiableAt ℝ variation point) (a : ℝ) :
    signalFirstJet (fun position=>signal position+a • variation position) point=
      signalFirstJet signal point+a • signalFirstJet variation point := by
  have smulSmooth := smoothVariation.const_smul a
  change DifferentiableAt ℝ (fun position=>a • variation position) point at smulSmooth
  rw [signalFirstJet_add signal (fun position=>a • variation position) point smoothSignal smulSmooth,
    signalFirstJet_smul variation point smoothVariation a]

/-- The complete nine-group physical perturbation enters the identical mother density through its actual holonomic first germ. -/
theorem nativeDensity_variation_generated (signal variation : BasePoint→Field289) (point : BasePoint)
    (smoothSignal : DifferentiableAt ℝ signal point)
    (smoothVariation : DifferentiableAt ℝ variation point)
    (inside : signalFirstJet signal point∈nativeEulerSourceDomain) :
    HasDerivAt (fun a : ℝ=>nativeDensity (fun position=>signal position+a • variation position) point)
      (fderiv ℝ nativeJetDensity (signalFirstJet signal point) (signalFirstJet variation point)) 0 := by
  have regular : ContDiffAt ℝ 2 nativeJetDensity (signalFirstJet signal point) := inside
  have source:=(regular.differentiableAt (by norm_num)).hasFDerivAt
  have ray : HasDerivAt (fun a : ℝ=>signalFirstJet signal point+a • signalFirstJet variation point)
      (signalFirstJet variation point) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (signalFirstJet variation point)).const_add
      (signalFirstJet signal point)
  have generated:=source.comp_hasDerivAt_of_eq (0 : ℝ) ray (by simp)
  have identity : (fun a : ℝ=>nativeDensity (fun position=>signal position+a • variation position) point)=
      fun a=>nativeJetDensity (signalFirstJet signal point+a • signalFirstJet variation point) := by
    funext a
    have varied := smoothSignal.add (smoothVariation.const_smul a)
    change DifferentiableAt ℝ (fun position=>signal position+a • variation position) point at varied
    rw [nativeDensity_signalFirstJet _ point varied,
      signalFirstJet_variation signal variation point smoothSignal smoothVariation a]
  rw [identity]
  exact generated

theorem nativeDensity_variation_coefficients (signal variation : BasePoint→Field289) (point : BasePoint) :
    fderiv ℝ nativeJetDensity (signalFirstJet signal point) (signalFirstJet variation point)=
      ∑ index : NativeJetIndex,nativeJetCoefficient (signalFirstJet variation point) index*
        fderiv ℝ nativeJetDensity (signalFirstJet signal point) (nativeJetBasis index) := by
  conv_lhs => rw [nativeJet_reconstruction (signalFirstJet variation point)]
  simp only [map_sum,map_smul,smul_eq_mul]

def nativeSignalMomentum (signal : BasePoint→Field289) (mu : Fin 4) (field : Fin 289) (point : BasePoint) : ℝ :=
  fderiv ℝ nativeJetDensity (signalFirstJet signal point) (nativeJetBasis (some mu,field))

def nativeVariationFlux (signal variation : BasePoint→Field289) (mu : Fin 4) (point : BasePoint) : ℝ :=
  ∑ field : Fin 289,nativeSignalMomentum signal mu field point*variation point field

theorem nativeSignalMomentum_differentiable (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (inside : signalFirstJet signal point∈nativeEulerSourceDomain)
    (mu : Fin 4) (field : Fin 289) : DifferentiableAt ℝ (nativeSignalMomentum signal mu field) point := by
  have density : ContDiffAt ℝ 2 nativeJetDensity (signalFirstJet signal point) := inside
  have source : ContDiffAt ℝ 1 (fun jet : NativeFirstJet=>fderiv ℝ nativeJetDensity jet (nativeJetBasis (some mu,field)))
      (signalFirstJet signal point) := (density.fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const
  exact (source.comp point (signalFirstJet_source_smooth signal point smooth)).differentiableAt (by norm_num)

theorem nativeVariationFlux_derivative (signal variation : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (variationSmooth : DifferentiableAt ℝ variation point)
    (inside : signalFirstJet signal point∈nativeEulerSourceDomain) (mu : Fin 4) :
    fieldDirectionalDerivative (nativeVariationFlux signal variation mu) point mu=
      ∑ field : Fin 289,(fieldDirectionalDerivative (nativeSignalMomentum signal mu field) point mu*variation point field+
        nativeSignalMomentum signal mu field point*(fieldDirectionalDerivative variation point mu) field) := by
  have each (field : Fin 289) := ((nativeSignalMomentum_differentiable signal point smooth inside mu field).hasFDerivAt).mul
    ((ContinuousLinearMap.proj field : Field289→L[ℝ] ℝ).hasFDerivAt.comp point variationSmooth.hasFDerivAt)
  have source := HasFDerivAt.fun_sum (u:=Finset.univ) (fun field _=>each field)
  change HasFDerivAt (nativeVariationFlux signal variation mu) _ point at source
  rw [fieldDirectionalDerivative,source.fderiv]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro field _
  simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
    fieldDirectionalDerivative,Function.comp_apply]
  ring

theorem nativeDensity_variation_value_momentum (signal variation : BasePoint→Field289) (point : BasePoint) :
    fderiv ℝ nativeJetDensity (signalFirstJet signal point) (signalFirstJet variation point)=
      (∑ field : Fin 289,variation point field*fderiv ℝ nativeJetDensity (signalFirstJet signal point) (nativeJetBasis (none,field)))+
        ∑ mu : Fin 4,∑ field : Fin 289,(fieldDirectionalDerivative variation point mu) field*
          nativeSignalMomentum signal mu field point := by
  rw [nativeDensity_variation_coefficients]
  simp only [Fintype.sum_prod_type,Fintype.sum_option,nativeJetCoefficient,signalFirstJet,nativeSignalMomentum]

/-- The original mother perturbation returns its complete Euler coefficient and its actual source momentum flux. -/
theorem nativeDensity_variation_euler (signal variation : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiffAt ℝ 2 signal point) (variationSmooth : DifferentiableAt ℝ variation point)
    (inside : signalFirstJet signal point∈nativeEulerSourceDomain) :
    deriv (fun a : ℝ=>nativeDensity (fun position=>signal position+a • variation position) point) 0=
      (∑ field : Fin 289,variation point field*nativeHolonomicEuler signal point field)+
        ∑ mu : Fin 4,fieldDirectionalDerivative (nativeVariationFlux signal variation mu) point mu := by
  rw [(nativeDensity_variation_generated signal variation point (smooth.differentiableAt (by norm_num)) variationSmooth inside).deriv,
    nativeDensity_variation_value_momentum]
  have value (field : Fin 289) : nativeHolonomicEuler signal point field=
      fderiv ℝ nativeJetDensity (signalFirstJet signal point) (nativeJetBasis (none,field))-
        ∑ mu : Fin 4,fieldDirectionalDerivative (nativeSignalMomentum signal mu field) point mu := by
    simp only [nativeHolonomicEuler,nativeLocalAction_atPoint]
    rfl
  simp only [value,nativeVariationFlux_derivative signal variation point smooth variationSmooth inside,mul_sub,
    Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun mu field=>fieldDirectionalDerivative (nativeSignalMomentum signal mu field) point mu*variation point field)]
  simp only [mul_comm]
  ring

end LowEnergy.SourcePropagationMotherResidualDirections
