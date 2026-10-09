import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeHamiltonianReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeGaussianVariance
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileCoframeRemainingWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedGaussianPair
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussCoframeForm SourceCoframeCovariantSquare SourceCoframeCovariantAction
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceClockPhiCoframeForwardCore SourceClockPhiActualCovarianceStep SourceClockPhiCoframeForwardPair
open SourceClockPhiProfileNativeReturn SourceClockPhiProfileLocalNativeReturn SourceClockPhiProfileCoframeRemainingWork
open SourceClockPhiProfileCoframeReturn SourceClockPhiCorrectedGaussianPair SourceScalarVirialBulk
open SourceClockPhiOriginalGaussianH0NativeJoin SourceClockPhiOriginalGaussianH0FinalJoin FirstCurrentPayerNext
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource
open scoped ContDiff InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev K(t:ℝ)(ht:0<t)(x:ℝ×ℝ):End:=correctedCompleteCore t ht x.1 x.2
private abbrev G(t:ℝ):End:=sourceGain (Real.sqrt t)
private abbrev W(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ):End:=correctedProfileWeight t ht p q x.1 x.2
attribute [local irreducible] sourcePair embed diagonalAction scalarKinetic gaugeKinetic covariantKinetic
  GaussMatterCore.matterAction centeredAction vacuumLinearAction vacuumConstantAction scalarSpatialAction magneticAction
  spinRemainder numberShift

def nativeVarianceRow:Fin 11→End:=
  ![scalarKinetic,gaugeKinetic,GaussMatterCore.matterAction,centeredAction,(-2:ℂ) • vacuumLinearAction,
    vacuumConstantAction,scalarSpatialAction,magneticAction,spinRemainder,numberShift,
    multiply volumePotential volumePotential_smooth]
def nativeVariancePower:Fin 11→ℝ:=![-2/3,2/3,0,4/3,4/3,4/3,2/3,2/3,-2/3,-2/3,4/3]
def nativeVarianceDegree:Fin 11→ℝ:=![2,-2,1,-2,-1,0,0,4,0,0,0]
def nativeVarianceReturn(t:ℝ)(ht:0<t)(x:ℝ×ℝ):End:=
  ∑i:Fin 11,W t ht (nativeVariancePower i-1/3) (nativeVarianceDegree i) x*nativeVarianceRow i

private theorem coefficient_first(t ξ η:ℝ):∀x y:SourceCoordinateSlice,x.1=y.1→
    correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  rintro ⟨a,b⟩ ⟨d,e⟩ h
  cases h
  rfl
private theorem weight_zero(t:ℝ)(ht:0<t)(p:ℝ)(x:ℝ×ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ (fun z:SourceCoordinateSlice=>(forwardRatio t z)^p) z.val):
    W t ht p 0 x=multiply (fun z=>(forwardRatio t z)^p) hb:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((((forwardRatio t z)^p*Real.exp (0*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • f z)=_
  simp only[zero_mul,Real.exp_zero,mul_one]
  rfl
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem native_row_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(i:Fin 11)(f g:QuantumTest):
    sourcePair (K t ht x f) (nativeVarianceRow i (K t ht x g))=
      sourcePair f (W t ht (nativeVariancePower i) (nativeVarianceDegree i) x (nativeVarianceRow i g)):=by
  let c:=correctedCoefficient t x.1 x.2
  let hc:=coefficient_smooth t ht x.1 x.2
  let hi:=coefficient_first t x.1 x.2
  have hs:=actual_complete_profile_scalar_source t ht c hc hi f g
  have hg:=actual_complete_profile_gauge_source t ht c hc hi f g
  have hm:=actual_profile_complete_matter_pair t ht c hc hi f g
  have hC:=actual_profile_complete_centered_pair t ht c hc hi f g
  have hL:=actual_profile_complete_vacuum_linear_pair t ht c hc hi f g
  have hV:=actual_profile_complete_vacuum_constant_pair t ht c hc hi f g
  have hS:=actual_profile_complete_signed_spatial_pair t ht c hc hi f g
  have hB:=actual_profile_complete_magnetic_pair t ht c hc hi f g
  have hspin:=actual_profile_complete_spin_remainder_pair t ht c hc hi f g
  have hnum:=actual_profile_complete_number_shift_pair t ht c hc hi f g
  have hvol:=actual_profile_complete_coframe_volume_pair t ht c hc hi f g
  change sourcePair (K t ht x f) (scalarKinetic (K t ht x g))=sourcePair f (W t ht (-2/3) 2 x (scalarKinetic g)) at hs
  change sourcePair (K t ht x f) (gaugeKinetic (K t ht x g))=sourcePair f (W t ht (2/3) (-2) x (gaugeKinetic g)) at hg
  change sourcePair (K t ht x f) (GaussMatterCore.matterAction (K t ht x g))=sourcePair f (W t ht 0 1 x (GaussMatterCore.matterAction g)) at hm
  change sourcePair (K t ht x f) (centeredAction (K t ht x g))=sourcePair f (W t ht (4/3) (-2) x (centeredAction g)) at hC
  change sourcePair (K t ht x f) (vacuumLinearAction (K t ht x g))=sourcePair f (W t ht (4/3) (-1) x (vacuumLinearAction g)) at hL
  change sourcePair (K t ht x f) (vacuumConstantAction (K t ht x g))=sourcePair f (W t ht (4/3) 0 x (vacuumConstantAction g)) at hV
  change sourcePair (K t ht x f) (scalarSpatialAction (K t ht x g))=sourcePair f (W t ht (2/3) 0 x (scalarSpatialAction g)) at hS
  change sourcePair (K t ht x f) (magneticAction (K t ht x g))=sourcePair f (W t ht (2/3) 4 x (magneticAction g)) at hB
  rw [←weight_zero t ht (-2/3) x] at hspin hnum
  rw [←weight_zero t ht (4/3) x] at hvol
  change sourcePair (K t ht x f) (spinRemainder (K t ht x g))=sourcePair f (W t ht (-2/3) 0 x (spinRemainder g)) at hspin
  change sourcePair (K t ht x f) (numberShift (K t ht x g))=sourcePair f (W t ht (-2/3) 0 x (numberShift g)) at hnum
  change sourcePair (K t ht x f) (multiply volumePotential volumePotential_smooth (K t ht x g))=
    sourcePair f (W t ht (4/3) 0 x (multiply volumePotential volumePotential_smooth g)) at hvol
  fin_cases i
  all_goals norm_num only[nativeVarianceRow,nativeVariancePower,nativeVarianceDegree,Matrix.cons_val] at ⊢
  · convert hs using 1 <;> norm_num
  · exact hg
  · exact hm
  · exact hC
  · change sourcePair (K t ht x f) ((-2:ℂ) • vacuumLinearAction (K t ht x g))=
      sourcePair f (W t ht (4/3) (-1) x ((-2:ℂ) • vacuumLinearAction g))
    simp only[map_smul,pair_smul_r,hL]
  · exact hV
  · exact hS
  · exact hB
  · convert hspin using 1 <;> norm_num
  · convert hnum using 1 <;> norm_num
  · exact hvol

private theorem gain_square(t:ℝ)(ht:0<t)(z:physicalChart):
    (gainProfile (Real.sqrt t) z.val)^2=(forwardRatio t z.val)^(1/3:ℝ):=by
  have hr:=forward_ratio_pos t ht.le z
  unfold gainProfile
  rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  congr 1
  norm_num
private theorem gain_power_return(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ)(f:QuantumTest):
    G t (G t (W t ht (p-1/3) q x f))=W t ht p q x f:=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (gainProfile (Real.sqrt t) z:ℂ) • ((gainProfile (Real.sqrt t) z:ℂ) •
      ((((forwardRatio t z)^(p-1/3)*Real.exp (q*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • f z))=
      ((((forwardRatio t z)^p*Real.exp (q*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • f z)
    simp only[smul_smul,←Complex.ofReal_mul]
    have he:gainProfile (Real.sqrt t) z*(gainProfile (Real.sqrt t) z*
        ((forwardRatio t z)^(p-1/3)*Real.exp (q*correctedCoefficient t x.1 x.2 z)))=
        (forwardRatio t z)^p*Real.exp (q*correctedCoefficient t x.1 x.2 z):=by
      calc
        _=(gainProfile (Real.sqrt t) z)^2*(forwardRatio t z)^(p-1/3)*Real.exp (q*correctedCoefficient t x.1 x.2 z):=by ring
        _=_:=by rw [gain_square t ht ⟨z,hz⟩,←Real.rpow_add (forward_ratio_pos t ht.le ⟨z,hz⟩)];congr 2;ring
    rw [he]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem complete_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (K t ht x f) (K t ht x g)=sourcePair (G t f) (G t g):=by
  change sourcePair (sourceForwardCore t ht.le (correctedProfileCore t ht x.1 x.2 (G t f)))
    (sourceForwardCore t ht.le (correctedProfileCore t ht x.1 x.2 (G t g)))=_
  rw [actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _
private theorem gained_power_pair(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (K t ht x f) (K t ht x (W t ht (p-1/3) q x g))=
      sourcePair f (W t ht p q x g):=by
  rw [complete_pair]
  have h:sourcePair (G t f) (G t (W t ht (p-1/3) q x g))=
      sourcePair f (G t (G t (W t ht (p-1/3) q x g))):=(multiply_pair _ _ _ _).symm
  rw [h,gain_power_return]

private theorem H0_native_sum:diagonalAction-covariantKinetic=∑i:Fin 11,nativeVarianceRow i:=by
  rw [original_H0_operator_split]
  unfold nativeBase localBase nativeVarianceRow
  simp only[Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero]
  module

def fullPowerReturn(t:ℝ)(ht:0<t)(x:ℝ×ℝ):End:=
  nativeVarianceReturn t ht x+returnedCoframeKinetic t ht x.1 x.2
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]
private theorem pair_sum_r(f:QuantumTest)(v:Fin 11→QuantumTest):sourcePair f (∑i,v i)=∑i,sourcePair f (v i):=by
  simp only[sourcePair,map_sum,inner_sum]
private theorem native_return_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (K t ht x f) ((diagonalAction-covariantKinetic) (K t ht x g))=
      sourcePair (K t ht x f) (K t ht x (nativeVarianceReturn t ht x g)):=by
  rw [H0_native_sum]
  simp only[LinearMap.sum_apply,nativeVarianceReturn,Module.End.mul_apply,map_sum,pair_sum_r]
  apply Finset.sum_congr rfl
  intro i _
  rw [native_row_pair, gained_power_pair]
private theorem point_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (K t ht x f) (K t ht x (returnedHamiltonian t ht x.1 x.2 g))=
      sourcePair (K t ht x f) (K t ht x (fullPowerReturn t ht x g)):=by
  have hH:=LinearMap.congr_fun (actual_corrected_H0_point_return t ht x.1 x.2) g
  have hC:=LinearMap.congr_fun (actual_corrected_coframe_second_order t ht x.1 x.2) g
  change diagonalAction (K t ht x g)=K t ht x (returnedHamiltonian t ht x.1 x.2 g) at hH
  change covariantKinetic (K t ht x g)=K t ht x (returnedCoframeKinetic t ht x.1 x.2 g) at hC
  have hp:=native_return_pair t ht x f g
  simp only[LinearMap.sub_apply,pair_sub_r,hH,hC] at hp
  simp only[fullPowerReturn,LinearMap.add_apply,map_add,pair_add_r]
  linear_combination hp

private theorem gain_injective(t:ℝ)(_ht:0<t):Function.Injective (G t):=by
  intro f g h
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have he:=congrArg (fun u:QuantumTest=>u z) h
    change (gainProfile (Real.sqrt t) z:ℂ) • f z=(gainProfile (Real.sqrt t) z:ℂ) • g z at he
    have hn:(gainProfile (Real.sqrt t) z:ℂ)≠0:=by
      apply Complex.ofReal_ne_zero.mpr
      exact (Real.rpow_pos_of_pos (forward_ratio_pos ((Real.sqrt t)^2) (sq_nonneg _) ⟨z,hz⟩) _).ne'
    exact (smul_right_injective FockFiber hn) he
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

/-- The complete returned Hamiltonian is generated by eleven original profile rows and the
full covariant coframe action; the pairing recognition becomes an actual point identity. -/
theorem actual_whole_return_finite_power(t:ℝ)(ht:0<t)(x:ℝ×ℝ):
    returnedHamiltonian t ht x.1 x.2=fullPowerReturn t ht x:=by
  apply LinearMap.ext
  intro g
  let d:=returnedHamiltonian t ht x.1 x.2 g-fullPowerReturn t ht x g
  have hp:=point_pair t ht x d g
  have hz:sourcePair (G t d) (G t d)=0:=by
    rw [←complete_pair]
    change sourcePair (K t ht x d) (K t ht x (returnedHamiltonian t ht x.1 x.2 g-fullPowerReturn t ht x g))=0
    rw [map_sub,pair_sub_r]
    simpa only[d,map_sub] using sub_eq_zero.mpr hp
  have hG:G t d=0:=by
    apply embed_injective
    rw [map_zero]
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    simpa only[sourcePair] using hz
  have hd:d=0:=gain_injective t ht (hG.trans (map_zero (G t)).symm)
  exact sub_eq_zero.mp hd

/-- This is the actual full H0 point source in finite original native/profile and coframe columns. -/
theorem actual_corrected_H0_finite_power(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(w:QuantumTest):
    diagonalAction (K t ht x w)=K t ht x (fullPowerReturn t ht x w):=by
  have h:=LinearMap.congr_fun (actual_corrected_H0_point_return t ht x.1 x.2) w
  rw [actual_whole_return_finite_power] at h
  exact h
end LowEnergy.FirstCurrentWholeVariance
