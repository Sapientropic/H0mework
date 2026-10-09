import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatHamiltonianWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianComplexIBP
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCoframeRemainingWork
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiHeatCoframeHamiltonianWork
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert SourceQuantumConfigurationHilbert
open SourceQuantumFockGauge SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open MeasureTheory
open scoped ContDiff Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private theorem coframeWeight_smooth(t:ℝ)(ht:0<t)(p:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(SourceClockPhiCoframeForwardCore.forwardRatio t x)^p) z.val:=by
  have h:ContDiffAt ℝ ∞ (SourceClockPhiCoframeForwardCore.forwardRatio t) z.val:=
    (GaussNativeEnergy.volume_smooth.contDiffAt.add contDiffAt_const).div GaussNativeEnergy.volume_smooth.contDiffAt (GaussNativeEnergy.volume_pos z).ne'
  exact h.rpow_const_of_ne (SourceClockPhiCoframeForwardCore.forward_ratio_pos t ht.le z).ne'
private def coframeWeight(t:ℝ)(ht:0<t)(p:ℝ):End:=
  GaussNativeForm.multiply (fun z=>(SourceClockPhiCoframeForwardCore.forwardRatio t z)^p) (coframeWeight_smooth t ht p)
def covariantHeatRow(t:ℝ)(ht:0<t)(ξ:ℝ)(i:Fin 6):End:=
  ClockPhiHeatHamiltonianWork.heatCoframeRow t ht ξ i+
    coframeWeight t ht (-1/3)*SourceCoframeCovariantAction.connectionAction i
private theorem covariant_return(t:ℝ)(ht:0<t)(ξ:ℝ)(i:Fin 6):
    SourceCoframeCovariantAction.covariantMomentum i*SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ=
      SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ*covariantHeatRow t ht ξ i:=by
  have hc:SourceCoframeCovariantAction.connectionAction i*SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ=
      SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ*(coframeWeight t ht (-1/3)*SourceCoframeCovariantAction.connectionAction i):=
    SourceClockPhiHeatCoframeRemainingWork.actual_complete_connection_return t ht ξ i
  rw [SourceCoframeCovariantAction.covariantMomentum,add_mul,
    ClockPhiHeatHamiltonianWork.actual_complete_heat_coframe_return,hc,covariantHeatRow,mul_add]
private theorem covariant_kinetic_pair(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (SourceCoframeCovariantAction.covariantKinetic (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))=
      ∑i:Fin 6,∑j:Fin 6,sourcePair (covariantHeatRow t ht ξ i f)
        (SourceCoframeCovariantAction.metricAction i j (covariantHeatRow t ht ξ j g)):=by
  simp only [SourceCoframeCovariantAction.covariantKinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change sourcePair _ (SourceCoframeCovariantAction.covariantAdjoint i (SourceCoframeCovariantAction.metricAction i j
    (SourceCoframeCovariantAction.covariantMomentum j (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))))=_
  have had(p q:QuantumTest):sourcePair p (SourceCoframeCovariantAction.covariantAdjoint i q)=
      sourcePair (SourceCoframeCovariantAction.covariantMomentum i p) q:=by
    simp only [SourceCoframeCovariantAction.covariantAdjoint,SourceCoframeCovariantAction.covariantMomentum,
      LinearMap.add_apply,sourcePair,map_add,inner_add_right,inner_add_left]
    exact congrArg₂ (·+·) (GaussCoframeKinetic.adjoint_pair i p q)
      (SourceCoframeCovariantAction.original_connection_pair i p q)
  rw [had]
  have hi:=LinearMap.congr_fun (covariant_return t ht ξ i) f
  have hj:=LinearMap.congr_fun (covariant_return t ht ξ j) g
  change SourceCoframeCovariantAction.covariantMomentum i (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)=
    SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ (covariantHeatRow t ht ξ i f) at hi
  change SourceCoframeCovariantAction.covariantMomentum j (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g)=
    SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ (covariantHeatRow t ht ξ j g) at hj
  rw [hi,hj]
  exact ClockPhiHeatHamiltonianWork.actual_complete_heat_metric_pair t ht ξ i j _ _
private abbrev gaussian:=ProbabilityTheory.gaussianReal 0 1
private theorem gaussian_affine_pair(A B C D:QuantumTest)(M:End):
    MeasureTheory.Integrable (fun ξ:ℝ=>sourcePair (A+(ξ:ℂ) • B) (M (C+(ξ:ℂ) • D))) gaussian ∧
      (∫ξ:ℝ,sourcePair (A+(ξ:ℂ) • B) (M (C+(ξ:ℂ) • D)) ∂gaussian)=
        sourcePair A (M C)+sourcePair B (M D):=by
  have h1:MeasureTheory.Integrable (fun ξ:ℝ=>ξ) gaussian:=
    (ProbabilityTheory.memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  have h2:MeasureTheory.Integrable (fun ξ:ℝ=>ξ^2) gaussian:=
    (ProbabilityTheory.memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  have he(ξ:ℝ):sourcePair (A+(ξ:ℂ) • B) (M (C+(ξ:ℂ) • D))=
      sourcePair A (M C)+(ξ:ℂ)*(sourcePair A (M D)+sourcePair B (M C))+
        ((ξ^2:ℝ):ℂ)*sourcePair B (M D):=by
    simp only [sourcePair,map_add,map_smul,inner_add_left,inner_add_right,
      inner_smul_left,inner_smul_right,Complex.conj_ofReal,Complex.ofReal_pow]
    ring
  have hc:MeasureTheory.Integrable (fun _:ℝ=>sourcePair A (M C)) gaussian:=MeasureTheory.integrable_const _
  have hl:MeasureTheory.Integrable (fun ξ:ℝ=>(ξ:ℂ)*(sourcePair A (M D)+sourcePair B (M C))) gaussian:=h1.ofReal.mul_const _
  have hq:MeasureTheory.Integrable (fun ξ:ℝ=>((ξ^2:ℝ):ℂ)*sourcePair B (M D)) gaussian:=h2.ofReal.mul_const _
  refine ⟨((hc.add hl).add hq).congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  calc
    _=(∫ξ:ℝ,sourcePair A (M C)+(ξ:ℂ)*(sourcePair A (M D)+sourcePair B (M C)) ∂gaussian)+
      (∫ξ:ℝ,((ξ^2:ℝ):ℂ)*sourcePair B (M D) ∂gaussian):=MeasureTheory.integral_add (hc.add hl) hq
    _=((∫_:ℝ,sourcePair A (M C) ∂gaussian)+
      (∫ξ:ℝ,(ξ:ℂ)*(sourcePair A (M D)+sourcePair B (M C)) ∂gaussian))+
      (∫ξ:ℝ,((ξ^2:ℝ):ℂ)*sourcePair B (M D) ∂gaussian):=by
        rw [MeasureTheory.integral_add hc hl]
    _=_:=by
      rw [MeasureTheory.integral_mul_const,MeasureTheory.integral_mul_const,
        integral_complex_ofReal,integral_complex_ofReal,
        ProbabilityTheory.integral_id_gaussianReal,SourceClockPhiGaussianComplexIBP.standard_gaussian_square_moment]
      simp

def deterministicCoframeRow(t:ℝ)(ht:0<t)(i:Fin 6):End:=covariantHeatRow t ht 0 i
def stochasticCoframeRow(t:ℝ)(ht:0<t)(i:Fin 6):End:=
  ClockPhiHeatHamiltonianWork.heatCoframeRow t ht 1 i-ClockPhiHeatHamiltonianWork.heatCoframeRow t ht 0 i
private theorem covariantRow_affine(t:ℝ)(ht:0<t)(ξ:ℝ)(i:Fin 6)(f:QuantumTest):
    covariantHeatRow t ht ξ i f=deterministicCoframeRow t ht i f+(ξ:ℂ) • stochasticCoframeRow t ht i f:=by
  simp only [covariantHeatRow,ClockPhiHeatHamiltonianWork.heatCoframeRow,deterministicCoframeRow,stochasticCoframeRow,
    Module.End.mul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_sub,map_smul,
    Complex.ofReal_zero,Complex.ofReal_one,mul_zero,mul_one,zero_smul,add_zero]
  module

private theorem covariant_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    MeasureTheory.Integrable (fun ξ:ℝ=>sourcePair
      (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (SourceCoframeCovariantAction.covariantKinetic (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))) gaussian ∧
    (∫ξ:ℝ,sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (SourceCoframeCovariantAction.covariantKinetic (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g)) ∂gaussian)=
      ∑i:Fin 6,∑j:Fin 6,(sourcePair (deterministicCoframeRow t ht i f)
        (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))+
        sourcePair (stochasticCoframeRow t ht i f)
          (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g))):=by
  have h(i j:Fin 6):=gaussian_affine_pair (deterministicCoframeRow t ht i f) (stochasticCoframeRow t ht i f)
    (deterministicCoframeRow t ht j g) (stochasticCoframeRow t ht j g) (SourceCoframeCovariantAction.metricAction i j)
  have hi(i j:Fin 6):MeasureTheory.Integrable (fun ξ:ℝ=>sourcePair (covariantHeatRow t ht ξ i f)
      (SourceCoframeCovariantAction.metricAction i j (covariantHeatRow t ht ξ j g))) gaussian:=by
    simpa only [covariantRow_affine] using (h i j).1
  have hsum:MeasureTheory.Integrable (fun ξ:ℝ=>∑i:Fin 6,∑j:Fin 6,sourcePair (covariantHeatRow t ht ξ i f)
      (SourceCoframeCovariantAction.metricAction i j (covariantHeatRow t ht ξ j g))) gaussian:=
    MeasureTheory.integrable_finsetSum _ (fun i _=>MeasureTheory.integrable_finsetSum _ (fun j _=>hi i j))
  refine ⟨hsum.congr (Filter.Eventually.of_forall (fun ξ=>(covariant_kinetic_pair t ht ξ f g).symm)),?_⟩
  simp_rw [covariant_kinetic_pair]
  rw [MeasureTheory.integral_finsetSum _ (fun i _=>MeasureTheory.integrable_finsetSum _ (fun j _=>hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_finsetSum _ (fun j _=>hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [covariantRow_affine] using (h i j).2

private theorem pair_add_r(p f g:QuantumTest):sourcePair p (f+g)=sourcePair p f+sourcePair p g:=by
  simp only [sourcePair,map_add,inner_add_right]
def localCoframePair(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  sourcePair f (coframeWeight t ht (-2/3) (SourceCoframeCovariantSquare.spinRemainder g))+
  sourcePair f (coframeWeight t ht (-2/3) (GaussCoframeForm.numberShift g))+
  sourcePair f (coframeWeight t ht (4/3)
    (GaussNativeForm.multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth g))

theorem actual_complete_coframe_source(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (GaussCoframeForm.coframeAction (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))=
      (∑i:Fin 6,∑j:Fin 6,sourcePair (covariantHeatRow t ht ξ i f)
        (SourceCoframeCovariantAction.metricAction i j (covariantHeatRow t ht ξ j g)))+localCoframePair t ht f g:=by
  rw [SourceCoframeCovariantSquare.original_coframe_covariant]
  simp only [LinearMap.add_apply,pair_add_r]
  rw [covariant_kinetic_pair,SourceClockPhiHeatCoframeRemainingWork.actual_complete_spin_remainder_pair,
    SourceClockPhiHeatCoframeRemainingWork.actual_complete_number_shift_pair,
    SourceClockPhiHeatCoframeRemainingWork.actual_complete_coframe_volume_pair]
  dsimp only [localCoframePair,coframeWeight]
  ring

theorem actual_complete_coframe_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (GaussCoframeForm.coframeAction (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))) gaussian ∧
    (∫ξ:ℝ,sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (GaussCoframeForm.coframeAction (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g)) ∂gaussian)=
      (∑i:Fin 6,∑j:Fin 6,(sourcePair (deterministicCoframeRow t ht i f)
        (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))+
        sourcePair (stochasticCoframeRow t ht i f)
          (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g))))+localCoframePair t ht f g:=by
  have h:=covariant_gaussian t ht f g
  have he(ξ:ℝ):sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (GaussCoframeForm.coframeAction (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))=
      sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
        (SourceCoframeCovariantAction.covariantKinetic (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))+localCoframePair t ht f g:=by
    rw [actual_complete_coframe_source,covariant_kinetic_pair]
  refine ⟨(h.1.add (integrable_const _)).congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  rw [integral_add h.1 (integrable_const _),h.2]
  simp

end LowEnergy.ClockPhiHeatCoframeHamiltonianWork
