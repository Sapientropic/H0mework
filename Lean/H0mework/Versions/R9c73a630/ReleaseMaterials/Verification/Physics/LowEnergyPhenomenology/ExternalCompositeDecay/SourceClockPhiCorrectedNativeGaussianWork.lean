import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileNativeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileLocalNativeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedGaussianPair
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatHamiltonianSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCorrectedNativeGaussianWork
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarVirialBulk SourceClockPhiProfileNativeReturn SourceClockPhiProfileCoframeReturn SourceClockPhiProfileLocalNativeReturn
open ClockPhiHeatCorrectedCovarianceSource SourceClockPhiCorrectedGaussianPair SourceClockPhiHeatLocalNativeGaussian
open SourceClockPhiCompleteHeatGainPayment SourceClockPhiCompleteHeatHamiltonianSource
open MeasureTheory ProbabilityTheory
open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=gaussianReal 0 1
private abbrev centerValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*‖scalarField z‖^2
private abbrev vacLinValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*inner ℝ vacuum (scalarField z)
private abbrev vacConstValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*‖vacuum‖^2
private abbrev spatialValue(z:SourceCoordinateSlice):ℝ:=
  -(sourceTime 0*GaussNativeEnergy.volume z/2*∑i:Fin 3,∑j:Fin 3,inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j))
private theorem potential_decompose(z:SourceCoordinateSlice):
    potential z=centerValue z-2*vacLinValue z+vacConstValue z+spatialValue z+magneticPotential z:=by
  have hsub:scalarField z-vacuum=(z.2.1:Scalar):=by unfold scalarField;abel
  have hn:=norm_sub_sq_real (scalarField z) vacuum
  rw [hsub,real_inner_comm vacuum (scalarField z)] at hn
  unfold potential scalarPotential centerValue vacLinValue vacConstValue spatialValue
  rw [real_inner_self_eq_norm_sq,hn]
  ring
private theorem potential_action_decompose:
    multiply potential potential_smooth=centeredAction-(2:ℂ) • vacuumLinearAction+
      vacuumConstantAction+scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (potential z:ℂ) • f z=(centerValue z:ℂ) • f z-
    (2:ℂ) • ((vacLinValue z:ℂ) • f z)+(vacConstValue z:ℂ) • f z+
      (spatialValue z:ℂ) • f z+(magneticPotential z:ℂ) • f z
  rw [potential_decompose]
  push_cast
  simp only [add_smul,sub_smul,mul_smul]
private theorem coefficient_first(t ξ η:ℝ)(x y:SourceCoordinateSlice)(h:x.1=y.1):
    correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  have hx:correctedCoefficient t ξ η x=correctedCoefficient t ξ η (x.1,0):=rfl
  have hy:correctedCoefficient t ξ η y=correctedCoefficient t ξ η (y.1,0):=rfl
  rw [hx,hy,h]

private theorem scalar_paired(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (scalarKinetic (correctedCompleteCore t ht ξ η g))=
      sourcePair f (correctedProfileWeight t ht (-2/3) 2 ξ η (scalarKinetic g)):=by
  exact actual_complete_profile_scalar_source t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun x y h=>coefficient_first t ξ η x y h) f g
private theorem scalar_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (scalarKinetic (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (scalarKinetic (correctedCompleteCore t ht z.1 z.2 g)) ∂γ.prod γ)=
      sourcePair f (gaussianProfileWeight t ht (-7/9) (scalarKinetic g)):=by
  have h:=actual_corrected_gaussian_weighted_source_pair t ht (-2/3) 2 f (scalarKinetic g)
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun z=>( scalar_paired t ht z.1 z.2 f g).symm))
  · simp_rw [scalar_paired]
    convert h.2 using 1; norm_num

private theorem gauge_paired(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (gaugeKinetic (correctedCompleteCore t ht ξ η g))=
      sourcePair f (correctedProfileWeight t ht (2/3) (-2) ξ η (gaugeKinetic g)):=by
  exact actual_complete_profile_gauge_source t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun x y h=>coefficient_first t ξ η x y h) f g
private theorem gauge_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (gaugeKinetic (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (gaugeKinetic (correctedCompleteCore t ht z.1 z.2 g)) ∂γ.prod γ)=
      sourcePair f (gaussianProfileWeight t ht (11/9) (gaugeKinetic g)):=by
  have h:=actual_corrected_gaussian_weighted_source_pair t ht (2/3) (-2) f (gaugeKinetic g)
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun z=>( gauge_paired t ht z.1 z.2 f g).symm))
  · simp_rw [gauge_paired]
    convert h.2 using 1; norm_num

private theorem matter_paired(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (GaussMatterCore.matterAction (correctedCompleteCore t ht ξ η g))=
      sourcePair f (correctedProfileWeight t ht 0 1 ξ η (GaussMatterCore.matterAction g)):=by
  exact SourceClockPhiProfileLocalNativeReturn.actual_profile_complete_matter_pair t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun x y h=>coefficient_first t ξ η x y h) f g
private theorem matter_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (GaussMatterCore.matterAction (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (GaussMatterCore.matterAction (correctedCompleteCore t ht z.1 z.2 g)) ∂γ.prod γ)=
      sourcePair f (gaussianProfileWeight t ht (-1/9) (GaussMatterCore.matterAction g)):=by
  have h:=actual_corrected_gaussian_weighted_source_pair t ht 0 1 f (GaussMatterCore.matterAction g)
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun z=>( matter_paired t ht z.1 z.2 f g).symm))
  · simp_rw [matter_paired]
    convert h.2 using 1; norm_num

private theorem centered_paired(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (centeredAction (correctedCompleteCore t ht ξ η g))=
      sourcePair f (correctedProfileWeight t ht (4/3) (-2) ξ η (centeredAction g)):=by
  exact SourceClockPhiProfileLocalNativeReturn.actual_profile_complete_centered_pair t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun x y h=>coefficient_first t ξ η x y h) f g
private theorem centered_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (centeredAction (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (centeredAction (correctedCompleteCore t ht z.1 z.2 g)) ∂γ.prod γ)=
      sourcePair f (gaussianProfileWeight t ht (17/9) (centeredAction g)):=by
  have h:=actual_corrected_gaussian_weighted_source_pair t ht (4/3) (-2) f (centeredAction g)
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun z=>( centered_paired t ht z.1 z.2 f g).symm))
  · simp_rw [centered_paired]
    convert h.2 using 1; norm_num

private theorem vacuum_linear_paired(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (vacuumLinearAction (correctedCompleteCore t ht ξ η g))=
      sourcePair f (correctedProfileWeight t ht (4/3) (-1) ξ η (vacuumLinearAction g)):=by
  exact SourceClockPhiProfileLocalNativeReturn.actual_profile_complete_vacuum_linear_pair t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun x y h=>coefficient_first t ξ η x y h) f g
private theorem vacuum_linear_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (vacuumLinearAction (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (vacuumLinearAction (correctedCompleteCore t ht z.1 z.2 g)) ∂γ.prod γ)=
      sourcePair f (gaussianProfileWeight t ht (14/9) (vacuumLinearAction g)):=by
  have h:=actual_corrected_gaussian_weighted_source_pair t ht (4/3) (-1) f (vacuumLinearAction g)
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun z=>( vacuum_linear_paired t ht z.1 z.2 f g).symm))
  · simp_rw [vacuum_linear_paired]
    convert h.2 using 1; norm_num

private theorem vacuum_constant_paired(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (vacuumConstantAction (correctedCompleteCore t ht ξ η g))=
      sourcePair f (correctedProfileWeight t ht (4/3) 0 ξ η (vacuumConstantAction g)):=by
  exact SourceClockPhiProfileLocalNativeReturn.actual_profile_complete_vacuum_constant_pair t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun x y h=>coefficient_first t ξ η x y h) f g
private theorem vacuum_constant_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (vacuumConstantAction (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (vacuumConstantAction (correctedCompleteCore t ht z.1 z.2 g)) ∂γ.prod γ)=
      sourcePair f (gaussianProfileWeight t ht (12/9) (vacuumConstantAction g)):=by
  have h:=actual_corrected_gaussian_weighted_source_pair t ht (4/3) 0 f (vacuumConstantAction g)
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun z=>( vacuum_constant_paired t ht z.1 z.2 f g).symm))
  · simp_rw [vacuum_constant_paired]
    convert h.2 using 1; norm_num

private theorem signed_spatial_paired(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (scalarSpatialAction (correctedCompleteCore t ht ξ η g))=
      sourcePair f (correctedProfileWeight t ht (2/3) 0 ξ η (scalarSpatialAction g)):=by
  exact SourceClockPhiProfileLocalNativeReturn.actual_profile_complete_signed_spatial_pair t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun x y h=>coefficient_first t ξ η x y h) f g
private theorem signed_spatial_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (scalarSpatialAction (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (scalarSpatialAction (correctedCompleteCore t ht z.1 z.2 g)) ∂γ.prod γ)=
      sourcePair f (gaussianProfileWeight t ht (6/9) (scalarSpatialAction g)):=by
  have h:=actual_corrected_gaussian_weighted_source_pair t ht (2/3) 0 f (scalarSpatialAction g)
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun z=>( signed_spatial_paired t ht z.1 z.2 f g).symm))
  · simp_rw [signed_spatial_paired]
    convert h.2 using 1; norm_num

private theorem magnetic_paired(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (magneticAction (correctedCompleteCore t ht ξ η g))=
      sourcePair f (correctedProfileWeight t ht (2/3) 4 ξ η (magneticAction g)):=by
  exact SourceClockPhiProfileLocalNativeReturn.actual_profile_complete_magnetic_pair t ht (correctedCoefficient t ξ η)
    (coefficient_smooth t ht ξ η) (fun x y h=>coefficient_first t ξ η x y h) f g
private theorem magnetic_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (magneticAction (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      (magneticAction (correctedCompleteCore t ht z.1 z.2 g)) ∂γ.prod γ)=
      sourcePair f (gaussianProfileWeight t ht (8/9) (magneticAction g)):=by
  have h:=actual_corrected_gaussian_weighted_source_pair t ht (2/3) 4 f (magneticAction g)
  constructor
  · exact h.1.congr (Filter.Eventually.of_forall (fun z=>( magnetic_paired t ht z.1 z.2 f g).symm))
  · simp_rw [magnetic_paired]
    convert h.2 using 1; norm_num


private theorem native_split:GaussNativeForm.nativeAction+GaussMatterCore.matterAction=
    scalarKinetic+gaugeKinetic+GaussMatterCore.matterAction+centeredAction-(2:ℂ) • vacuumLinearAction+
      vacuumConstantAction+scalarSpatialAction+magneticAction:=by
  unfold GaussNativeForm.nativeAction
  rw [potential_action_decompose]
  abel
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(a:ℂ)(f g:QuantumTest):sourcePair f (a • g)=a*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]
private def nativeGaussianPair(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  sourcePair f (gaussianProfileWeight t ht (-7/9) (scalarKinetic g))+
  sourcePair f (gaussianProfileWeight t ht (11/9) (gaugeKinetic g))+
  sourcePair f (gaussianProfileWeight t ht (-1/9) (GaussMatterCore.matterAction g))+
  sourcePair f (gaussianProfileWeight t ht (17/9) (centeredAction g))-
  2*sourcePair f (gaussianProfileWeight t ht (14/9) (vacuumLinearAction g))+
  sourcePair f (gaussianProfileWeight t ht (12/9) (vacuumConstantAction g))+
  sourcePair f (gaussianProfileWeight t ht (6/9) (scalarSpatialAction g))+
  sourcePair f (gaussianProfileWeight t ht (8/9) (magneticAction g))
private theorem corrected_native_pair_split(t:ℝ)(ht:0<t)(z:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (correctedCompleteCore t ht z.1 z.2 g))=
      sourcePair (correctedCompleteCore t ht z.1 z.2 f) (scalarKinetic (correctedCompleteCore t ht z.1 z.2 g))+
      sourcePair (correctedCompleteCore t ht z.1 z.2 f) (gaugeKinetic (correctedCompleteCore t ht z.1 z.2 g))+
      sourcePair (correctedCompleteCore t ht z.1 z.2 f) (GaussMatterCore.matterAction (correctedCompleteCore t ht z.1 z.2 g))+
      sourcePair (correctedCompleteCore t ht z.1 z.2 f) (centeredAction (correctedCompleteCore t ht z.1 z.2 g))-
      2*sourcePair (correctedCompleteCore t ht z.1 z.2 f) (vacuumLinearAction (correctedCompleteCore t ht z.1 z.2 g))+
      sourcePair (correctedCompleteCore t ht z.1 z.2 f) (vacuumConstantAction (correctedCompleteCore t ht z.1 z.2 g))+
      sourcePair (correctedCompleteCore t ht z.1 z.2 f) (scalarSpatialAction (correctedCompleteCore t ht z.1 z.2 g))+
      sourcePair (correctedCompleteCore t ht z.1 z.2 f) (magneticAction (correctedCompleteCore t ht z.1 z.2 g)):=by
  rw [native_split]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,pair_add_r,pair_sub_r,pair_smul_r]
private theorem original_native_pair_split(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (completeHeatCore t ht ξ f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (completeHeatCore t ht ξ g))=
      sourcePair (completeHeatCore t ht ξ f) (scalarKinetic (completeHeatCore t ht ξ g))+
      sourcePair (completeHeatCore t ht ξ f) (gaugeKinetic (completeHeatCore t ht ξ g))+
      sourcePair (completeHeatCore t ht ξ f) (GaussMatterCore.matterAction (completeHeatCore t ht ξ g))+
      sourcePair (completeHeatCore t ht ξ f) (centeredAction (completeHeatCore t ht ξ g))-
      2*sourcePair (completeHeatCore t ht ξ f) (vacuumLinearAction (completeHeatCore t ht ξ g))+
      sourcePair (completeHeatCore t ht ξ f) (vacuumConstantAction (completeHeatCore t ht ξ g))+
      sourcePair (completeHeatCore t ht ξ f) (scalarSpatialAction (completeHeatCore t ht ξ g))+
      sourcePair (completeHeatCore t ht ξ f) (magneticAction (completeHeatCore t ht ξ g)):=by
  rw [native_split]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,pair_add_r,pair_sub_r,pair_smul_r]

private theorem corrected_native_gaussian_value(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z=>sourcePair (correctedCompleteCore t ht z.1 z.2 f) ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    (∫(z:ℝ×ℝ),sourcePair (correctedCompleteCore t ht z.1 z.2 f) ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (correctedCompleteCore t ht z.1 z.2 g)) ∂(γ.prod γ))=nativeGaussianPair t ht f g:=by
  have h1:=scalar_gaussian t ht f g
  have h2:=gauge_gaussian t ht f g
  have h3:=matter_gaussian t ht f g
  have h4:=centered_gaussian t ht f g
  have h5:=vacuum_linear_gaussian t ht f g
  have h6:=vacuum_constant_gaussian t ht f g
  have h7:=signed_spatial_gaussian t ht f g
  have h8:=magnetic_gaussian t ht f g
  have hi:=(((((((h1.1.add h2.1).add h3.1).add h4.1).sub (h5.1.const_mul 2)).add h6.1).add h7.1).add h8.1)
  refine ⟨hi.congr (Filter.Eventually.of_forall (fun z=>(corrected_native_pair_split t ht z f g).symm)),?_⟩
  simp_rw [corrected_native_pair_split]
  let F1:ℝ×ℝ→ℂ:=fun z=>sourcePair (correctedCompleteCore t ht z.1 z.2 f) (scalarKinetic (correctedCompleteCore t ht z.1 z.2 g))
  let F2:ℝ×ℝ→ℂ:=fun z=>sourcePair (correctedCompleteCore t ht z.1 z.2 f) (gaugeKinetic (correctedCompleteCore t ht z.1 z.2 g))
  let F3:ℝ×ℝ→ℂ:=fun z=>sourcePair (correctedCompleteCore t ht z.1 z.2 f) (GaussMatterCore.matterAction (correctedCompleteCore t ht z.1 z.2 g))
  let F4:ℝ×ℝ→ℂ:=fun z=>sourcePair (correctedCompleteCore t ht z.1 z.2 f) (centeredAction (correctedCompleteCore t ht z.1 z.2 g))
  let F5:ℝ×ℝ→ℂ:=fun z=>sourcePair (correctedCompleteCore t ht z.1 z.2 f) (vacuumLinearAction (correctedCompleteCore t ht z.1 z.2 g))
  let F6:ℝ×ℝ→ℂ:=fun z=>sourcePair (correctedCompleteCore t ht z.1 z.2 f) (vacuumConstantAction (correctedCompleteCore t ht z.1 z.2 g))
  let F7:ℝ×ℝ→ℂ:=fun z=>sourcePair (correctedCompleteCore t ht z.1 z.2 f) (scalarSpatialAction (correctedCompleteCore t ht z.1 z.2 g))
  let F8:ℝ×ℝ→ℂ:=fun z=>sourcePair (correctedCompleteCore t ht z.1 z.2 f) (magneticAction (correctedCompleteCore t ht z.1 z.2 g))
  change (∫(z:ℝ×ℝ),(F1+F2+F3+F4-(fun z=>2*F5 z)+F6+F7+F8) z ∂(γ.prod γ))=_
  erw [integral_add ((((((h1.1.add h2.1).add h3.1).add h4.1).sub (h5.1.const_mul 2)).add h6.1).add h7.1) h8.1]
  erw [integral_add (((((h1.1.add h2.1).add h3.1).add h4.1).sub (h5.1.const_mul 2)).add h6.1) h7.1]
  erw [integral_add ((((h1.1.add h2.1).add h3.1).add h4.1).sub (h5.1.const_mul 2)) h6.1]
  erw [integral_sub (((h1.1.add h2.1).add h3.1).add h4.1) (h5.1.const_mul 2)]
  erw [integral_add ((h1.1.add h2.1).add h3.1) h4.1,integral_add (h1.1.add h2.1) h3.1,integral_add h1.1 h2.1,integral_const_mul]
  rw [h1.2,h2.2,h3.2,h4.2,h5.2,h6.2,h7.2,h8.2]
  rfl


private theorem original_native_gaussian_value(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z=>sourcePair (completeHeatCore t ht z f) ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (completeHeatCore t ht z g))) γ ∧
    (∫(z:ℝ),sourcePair (completeHeatCore t ht z f) ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (completeHeatCore t ht z g)) ∂γ)=nativeGaussianPair t ht f g:=by
  have h1:=SourceClockPhiHeatNativeGaussianWork.actual_complete_scalar_gaussian t ht f g
  have h2:=SourceClockPhiHeatNativeGaussianWork.actual_complete_gauge_gaussian t ht f g
  have h3:=SourceClockPhiHeatLocalNativeGaussian.actual_complete_matter_gaussian t ht f g
  have h4:=SourceClockPhiHeatLocalNativeGaussian.actual_complete_centered_gaussian t ht f g
  have h5:=SourceClockPhiHeatLocalNativeGaussian.actual_complete_vacuum_linear_gaussian t ht f g
  have h6:=SourceClockPhiHeatLocalNativeGaussian.actual_complete_vacuum_constant_gaussian t ht f g
  have h7:=SourceClockPhiHeatLocalNativeGaussian.actual_complete_signed_spatial_gaussian t ht f g
  have h8:=SourceClockPhiHeatLocalNativeGaussian.actual_complete_magnetic_gaussian t ht f g
  have hi:=(((((((h1.1.add h2.1).add h3.1).add h4.1).sub (h5.1.const_mul 2)).add h6.1).add h7.1).add h8.1)
  refine ⟨hi.congr (Filter.Eventually.of_forall (fun z=>(original_native_pair_split t ht z f g).symm)),?_⟩
  simp_rw [original_native_pair_split]
  let F1:ℝ→ℂ:=fun z=>sourcePair (completeHeatCore t ht z f) (scalarKinetic (completeHeatCore t ht z g))
  let F2:ℝ→ℂ:=fun z=>sourcePair (completeHeatCore t ht z f) (gaugeKinetic (completeHeatCore t ht z g))
  let F3:ℝ→ℂ:=fun z=>sourcePair (completeHeatCore t ht z f) (GaussMatterCore.matterAction (completeHeatCore t ht z g))
  let F4:ℝ→ℂ:=fun z=>sourcePair (completeHeatCore t ht z f) (centeredAction (completeHeatCore t ht z g))
  let F5:ℝ→ℂ:=fun z=>sourcePair (completeHeatCore t ht z f) (vacuumLinearAction (completeHeatCore t ht z g))
  let F6:ℝ→ℂ:=fun z=>sourcePair (completeHeatCore t ht z f) (vacuumConstantAction (completeHeatCore t ht z g))
  let F7:ℝ→ℂ:=fun z=>sourcePair (completeHeatCore t ht z f) (scalarSpatialAction (completeHeatCore t ht z g))
  let F8:ℝ→ℂ:=fun z=>sourcePair (completeHeatCore t ht z f) (magneticAction (completeHeatCore t ht z g))
  change (∫(z:ℝ),(F1+F2+F3+F4-(fun z=>2*F5 z)+F6+F7+F8) z ∂γ)=_
  erw [integral_add ((((((h1.1.add h2.1).add h3.1).add h4.1).sub (h5.1.const_mul 2)).add h6.1).add h7.1) h8.1]
  erw [integral_add (((((h1.1.add h2.1).add h3.1).add h4.1).sub (h5.1.const_mul 2)).add h6.1) h7.1]
  erw [integral_add ((((h1.1.add h2.1).add h3.1).add h4.1).sub (h5.1.const_mul 2)) h6.1]
  erw [integral_sub (((h1.1.add h2.1).add h3.1).add h4.1) (h5.1.const_mul 2)]
  erw [integral_add ((h1.1.add h2.1).add h3.1) h4.1,integral_add (h1.1.add h2.1) h3.1,integral_add h1.1 h2.1,integral_const_mul]
  rw [h1.2,h2.2,h3.2,h4.2,h5.2,h6.2,h7.2,h8.2]
  rfl


theorem actual_corrected_native_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (correctedCompleteCore t ht z.1 z.2 g))) (γ.prod γ) ∧
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (completeHeatCore t ht ξ g))) γ ∧
    (∫z:ℝ×ℝ,sourcePair (correctedCompleteCore t ht z.1 z.2 f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (correctedCompleteCore t ht z.1 z.2 g)) ∂γ.prod γ)=
    (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (completeHeatCore t ht ξ g)) ∂γ):=by
  have hn:=corrected_native_gaussian_value t ht f g
  have ho:=original_native_gaussian_value t ht f g
  exact ⟨hn.1,ho.1,hn.2.trans ho.2.symm⟩

end LowEnergy.SourceClockPhiCorrectedNativeGaussianWork
