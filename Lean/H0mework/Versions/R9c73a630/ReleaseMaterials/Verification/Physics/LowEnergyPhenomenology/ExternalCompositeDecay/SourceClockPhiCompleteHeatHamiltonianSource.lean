import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatLocalNativeGaussian
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatNativeGaussianWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCoframeHamiltonianWork
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCompleteHeatHamiltonianSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarVirialBulk SourceClockPhiCompleteHeatGainPayment
open SourceClockPhiHeatLocalNativeWork SourceClockPhiHeatLocalNativeGaussian
open SourceClockPhiHeatNativeHamiltonianWork SourceClockPhiHeatNativeGaussianWork ClockPhiHeatCoframeHamiltonianWork
open MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev gaussian:=gaussianReal 0 1
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
private theorem complete_split:
    GaussDiagonalHistory.diagonalAction=scalarKinetic+gaugeKinetic+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction+
      centeredAction-(2:ℂ) • vacuumLinearAction+vacuumConstantAction+scalarSpatialAction+magneticAction:=by
  unfold GaussDiagonalHistory.diagonalAction GaussNativeForm.nativeAction
  rw [potential_action_decompose]
  abel
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(a:ℂ)(f g:QuantumTest):sourcePair f (a • g)=a*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]

def wholeFixedHeatHamiltonianPair(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):ℂ:=
  sourcePair f (radialNoiseWeight t ht ξ (-2/3) 2 (scalarKinetic g))+
  sourcePair f (radialNoiseWeight t ht ξ (2/3) (-2) (gaugeKinetic g))+
  ((∑i:Fin 6,∑j:Fin 6,sourcePair (covariantHeatRow t ht ξ i f)
    (SourceCoframeCovariantAction.metricAction i j (covariantHeatRow t ht ξ j g)))+localCoframePair t ht f g)+
  sourcePair f (heatProfileWeight t ht 0 1 ξ (GaussMatterCore.matterAction g))+
  sourcePair f (heatProfileWeight t ht (4/3) (-2) ξ (centeredAction g))-
  2*sourcePair f (heatProfileWeight t ht (4/3) (-1) ξ (vacuumLinearAction g))+
  sourcePair f (gaussianProfileWeight t ht (4/3) (vacuumConstantAction g))+
  sourcePair f (gaussianProfileWeight t ht (2/3) (scalarSpatialAction g))+
  sourcePair f (heatProfileWeight t ht (2/3) 4 ξ (magneticAction g))

def wholeGaussianHeatHamiltonianPair(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  sourcePair f (gaussianProfileWeight t ht (-7/9) (scalarKinetic g))+
  sourcePair f (gaussianProfileWeight t ht (11/9) (gaugeKinetic g))+
  ((∑i:Fin 6,∑j:Fin 6,(sourcePair (deterministicCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))+
    sourcePair (stochasticCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g))))+localCoframePair t ht f g)+
  sourcePair f (gaussianProfileWeight t ht (-1/9) (GaussMatterCore.matterAction g))+
  sourcePair f (gaussianProfileWeight t ht (17/9) (centeredAction g))-
  2*sourcePair f (gaussianProfileWeight t ht (14/9) (vacuumLinearAction g))+
  sourcePair f (gaussianProfileWeight t ht (12/9) (vacuumConstantAction g))+
  sourcePair f (gaussianProfileWeight t ht (6/9) (scalarSpatialAction g))+
  sourcePair f (gaussianProfileWeight t ht (8/9) (magneticAction g))
private theorem heat_zero_reader(t:ℝ)(ht:0<t)(p ξ:ℝ):heatProfileWeight t ht p 0 ξ=gaussianProfileWeight t ht p:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (((SourceClockPhiCoframeForwardCore.forwardRatio t z)^p*Real.exp (0*(ClockPhiConservativeHeatSource.heatMean t z+
    Real.sqrt (ClockPhiConservativeHeatSource.heatVariance t z)*ξ)):ℝ):ℂ) • f z=
    (((SourceClockPhiCoframeForwardCore.forwardRatio t z)^p:ℝ):ℂ) • f z
  rw [zero_mul,Real.exp_zero,mul_one]
private theorem heat_matter_point(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    heatProfileWeight t ht 0 1 ξ f z=
      (Real.exp (ClockPhiConservativeHeatSource.heatMean t z+Real.sqrt (ClockPhiConservativeHeatSource.heatVariance t z)*ξ):ℂ) • f z:=by
  change ((((SourceClockPhiCoframeForwardCore.forwardRatio t z)^0*
    Real.exp (1*(ClockPhiConservativeHeatSource.heatMean t z+Real.sqrt (ClockPhiConservativeHeatSource.heatVariance t z)*ξ)):ℝ):ℂ) • f z)=_
  rw [Real.rpow_zero,one_mul,one_mul]
private theorem heat_matter_reader(t:ℝ)(ht:0<t)(ξ:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (he:∀z,b z=Real.exp (ClockPhiConservativeHeatSource.heatMean t z+Real.sqrt (ClockPhiConservativeHeatSource.heatVariance t z)*ξ)):
    multiply b hb=heatProfileWeight t ht 0 1 ξ:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  rw [heat_matter_point]
  change (b z:ℂ) • f z=_
  rw [he]

attribute [local irreducible] GaussDiagonalHistory.diagonalAction scalarKinetic gaugeKinetic GaussCoframeForm.coframeAction
  GaussMatterCore.matterAction centeredAction vacuumLinearAction vacuumConstantAction scalarSpatialAction magneticAction

theorem actual_complete_heat_hamiltonian_source(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (completeHeatCore t ht ξ f) (GaussDiagonalHistory.diagonalAction (completeHeatCore t ht ξ g))=
      wholeFixedHeatHamiltonianPair t ht ξ f g:=by
  rw [complete_split]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,pair_add_r,pair_sub_r,pair_smul_r]
  rw [actual_complete_scalar_source,actual_complete_gauge_source,actual_complete_coframe_source]
  have hm:=actual_complete_matter_pair t ht ξ f g
  have hc:=actual_complete_centered_pair t ht ξ f g
  have hl:=actual_complete_vacuum_linear_pair t ht ξ f g
  have hv:=actual_complete_vacuum_constant_pair t ht ξ f g
  have hs:=actual_complete_signed_spatial_pair t ht ξ f g
  have hb:=actual_complete_magnetic_pair t ht ξ f g
  rw [hm,hc,hl,hv,hs,hb]
  change _=wholeFixedHeatHamiltonianPair t ht ξ f g
  unfold wholeFixedHeatHamiltonianPair
  rw [heat_matter_reader t ht ξ _ _ (fun _=>rfl)]
  rfl

private theorem original_pair_split(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (completeHeatCore t ht ξ f) (GaussDiagonalHistory.diagonalAction (completeHeatCore t ht ξ g))=
    sourcePair (completeHeatCore t ht ξ f) (scalarKinetic (completeHeatCore t ht ξ g))+
    sourcePair (completeHeatCore t ht ξ f) (gaugeKinetic (completeHeatCore t ht ξ g))+
    sourcePair (completeHeatCore t ht ξ f) (GaussCoframeForm.coframeAction (completeHeatCore t ht ξ g))+
    sourcePair (completeHeatCore t ht ξ f) (GaussMatterCore.matterAction (completeHeatCore t ht ξ g))+
    sourcePair (completeHeatCore t ht ξ f) (centeredAction (completeHeatCore t ht ξ g))-
    2*sourcePair (completeHeatCore t ht ξ f) (vacuumLinearAction (completeHeatCore t ht ξ g))+
    sourcePair (completeHeatCore t ht ξ f) (vacuumConstantAction (completeHeatCore t ht ξ g))+
    sourcePair (completeHeatCore t ht ξ f) (scalarSpatialAction (completeHeatCore t ht ξ g))+
    sourcePair (completeHeatCore t ht ξ f) (magneticAction (completeHeatCore t ht ξ g)):=by
  rw [complete_split]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,pair_add_r,pair_sub_r,pair_smul_r]

private theorem integral_add_source {F G:ℝ→ℂ}(hF:Integrable F gaussian)(hG:Integrable G gaussian):
    (∫ξ:ℝ,F ξ+G ξ ∂gaussian)=(∫ξ:ℝ,F ξ ∂gaussian)+(∫ξ:ℝ,G ξ ∂gaussian):=by
  convert! integral_add hF hG using 1
private theorem integral_sub_source {F G:ℝ→ℂ}(hF:Integrable F gaussian)(hG:Integrable G gaussian):
    (∫ξ:ℝ,F ξ-G ξ ∂gaussian)=(∫ξ:ℝ,F ξ ∂gaussian)-(∫ξ:ℝ,G ξ ∂gaussian):=by
  convert! integral_sub hF hG using 1

theorem actual_complete_heat_hamiltonian_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f)
      (GaussDiagonalHistory.diagonalAction (completeHeatCore t ht ξ g))) gaussian∧
    (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f)
      (GaussDiagonalHistory.diagonalAction (completeHeatCore t ht ξ g)) ∂gaussian)=
        wholeGaussianHeatHamiltonianPair t ht f g:=by
  have hk:=actual_complete_scalar_gaussian t ht f g
  have hg:=actual_complete_gauge_gaussian t ht f g
  have hcf:=actual_complete_coframe_gaussian t ht f g
  have hm:=actual_complete_matter_gaussian t ht f g
  have hc:=actual_complete_centered_gaussian t ht f g
  have hl:=actual_complete_vacuum_linear_gaussian t ht f g
  have hv:=actual_complete_vacuum_constant_gaussian t ht f g
  have hs:=actual_complete_signed_spatial_gaussian t ht f g
  have hb:=actual_complete_magnetic_gaussian t ht f g
  have hi:=((((((((hk.1.add hg.1).add hcf.1).add hm.1).add hc.1).sub (hl.1.const_mul 2)).add hv.1).add hs.1).add hb.1)
  refine ⟨hi.congr (Filter.Eventually.of_forall (fun ξ=>(original_pair_split t ht ξ f g).symm)),?_⟩
  simp_rw [original_pair_split]
  let F1:ℝ→ℂ:=fun ξ=>sourcePair (completeHeatCore t ht ξ f) (scalarKinetic (completeHeatCore t ht ξ g))
  let F2:ℝ→ℂ:=fun ξ=>sourcePair (completeHeatCore t ht ξ f) (gaugeKinetic (completeHeatCore t ht ξ g))
  let F3:ℝ→ℂ:=fun ξ=>sourcePair (completeHeatCore t ht ξ f) (GaussCoframeForm.coframeAction (completeHeatCore t ht ξ g))
  let F4:ℝ→ℂ:=fun ξ=>sourcePair (completeHeatCore t ht ξ f) (GaussMatterCore.matterAction (completeHeatCore t ht ξ g))
  let F5:ℝ→ℂ:=fun ξ=>sourcePair (completeHeatCore t ht ξ f) (centeredAction (completeHeatCore t ht ξ g))
  let F6:ℝ→ℂ:=fun ξ=>sourcePair (completeHeatCore t ht ξ f) (vacuumLinearAction (completeHeatCore t ht ξ g))
  let F7:ℝ→ℂ:=fun ξ=>sourcePair (completeHeatCore t ht ξ f) (vacuumConstantAction (completeHeatCore t ht ξ g))
  let F8:ℝ→ℂ:=fun ξ=>sourcePair (completeHeatCore t ht ξ f) (scalarSpatialAction (completeHeatCore t ht ξ g))
  let F9:ℝ→ℂ:=fun ξ=>sourcePair (completeHeatCore t ht ξ f) (magneticAction (completeHeatCore t ht ξ g))
  change (∫ξ:ℝ,(F1+F2+F3+F4+F5-(fun ξ=>2*F6 ξ)+F7+F8+F9) ξ ∂gaussian)=_
  erw [integral_add_source (((((((hk.1.add hg.1).add hcf.1).add hm.1).add hc.1).sub (hl.1.const_mul 2)).add hv.1).add hs.1) hb.1]
  erw [integral_add_source ((((((hk.1.add hg.1).add hcf.1).add hm.1).add hc.1).sub (hl.1.const_mul 2)).add hv.1) hs.1]
  erw [integral_add_source (((((hk.1.add hg.1).add hcf.1).add hm.1).add hc.1).sub (hl.1.const_mul 2)) hv.1]
  erw [integral_sub_source ((((hk.1.add hg.1).add hcf.1).add hm.1).add hc.1) (hl.1.const_mul 2)]
  erw [integral_add_source (((hk.1.add hg.1).add hcf.1).add hm.1) hc.1]
  erw [integral_add_source ((hk.1.add hg.1).add hcf.1) hm.1]
  erw [integral_add_source (hk.1.add hg.1) hcf.1,integral_add_source hk.1 hg.1,integral_const_mul]
  rw [hk.2,hg.2,hcf.2,hm.2,hc.2,hl.2,hv.2,hs.2,hb.2]
  rfl
end LowEnergy.SourceClockPhiCompleteHeatHamiltonianSource
