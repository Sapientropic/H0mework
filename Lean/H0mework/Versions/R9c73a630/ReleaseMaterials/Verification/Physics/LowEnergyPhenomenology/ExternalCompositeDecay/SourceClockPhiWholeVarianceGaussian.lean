import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWeightedVarianceGaussian
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeVariance
open SourceCoframeCovariantAction
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussDiagonalHistory
open SourceClockPhiCoframeForwardCore SourceClockPhiActualCovarianceStep SourceClockPhiCoframeForwardPair SourceCoframeVolume
open SourceClockPhiCorrectedGaussianPair SourceClockPhiHeatLocalNativeGaussian
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource FirstCurrentPayerNext MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev K(t:ℝ)(ht:0<t)(x:ℝ×ℝ):End:=correctedCompleteCore t ht x.1 x.2
private abbrev G(t:ℝ):End:=sourceGain (Real.sqrt t)
private abbrev W(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ):End:=correctedProfileWeight t ht p q x.1 x.2
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ2:=γ.prod γ
attribute [local irreducible] sourcePair embed diagonalAction covariantKinetic
private theorem complete_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (K t ht x f) (K t ht x g)=sourcePair (G t f) (G t g):=by
  change sourcePair (sourceForwardCore t ht.le (correctedProfileCore t ht x.1 x.2 (G t f)))
    (sourceForwardCore t ht.le (correctedProfileCore t ht x.1 x.2 (G t g)))=_
  rw [actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _
private theorem weight_zero(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f:QuantumTest):W t ht 0 0 x f=f:=by
  apply DFunLike.ext
  intro z
  change ((((forwardRatio t z)^0*Real.exp (0*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • f z)=f z
  simp
private theorem native_column_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(i:Fin 11)(f g:QuantumTest):
    sourcePair (G t (W t ht (nativeVariancePower i-1/3) (nativeVarianceDegree i) x f)) (G t g)=
      sourcePair f (W t ht (nativeVariancePower i) (nativeVarianceDegree i) x g):=by
  have h:=actual_gained_profile_pair t ht (nativeVariancePower i-1/3) (nativeVarianceDegree i) 0 0 x f g
  simp only[weight_zero,add_zero] at h
  convert h using 1; congr 3; ring

def wholeVarianceColumn(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f:QuantumTest):QuantumTest:=
  nativeVarianceReturn t ht x f+quadraticSource (fun a=>coframeQuadraticColumn t ht a f) x

/-- One finite source generates both complete original H0 legs at the actual clock. -/
theorem actual_whole_variance_column(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f:QuantumTest):
    diagonalAction (K t ht x f)=K t ht x (wholeVarianceColumn t ht x f):=by
  rw [actual_corrected_H0_finite_power]
  unfold fullPowerReturn wholeVarianceColumn
  simp only[LinearMap.add_apply,map_add]
  have hC:=LinearMap.congr_fun (actual_corrected_coframe_second_order t ht x.1 x.2) f
  have hQ:=actual_corrected_coframe_quadratic_return t ht x f
  change covariantKinetic (K t ht x f)=K t ht x (returnedCoframeKinetic t ht x.1 x.2 f) at hC
  rw [←hC,hQ]
private theorem native_pair_expansion(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (G t (nativeVarianceReturn t ht x f)) (G t (nativeVarianceReturn t ht x g))=
    ∑i:Fin 11,∑j:Fin 11,sourcePair
      (G t (W t ht (nativeVariancePower i-1/3) (nativeVarianceDegree i) x (nativeVarianceRow i f)))
      (G t (W t ht (nativeVariancePower j-1/3) (nativeVarianceDegree j) x (nativeVarianceRow j g))):=by
  simp only[nativeVarianceReturn,LinearMap.sum_apply,Module.End.mul_apply,map_sum,sourcePair,sum_inner,inner_sum]
  rw [Finset.sum_comm]
private theorem native_pair_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (G t (nativeVarianceReturn t ht x f)) (G t (nativeVarianceReturn t ht x g))) γ2:=by
  simp_rw [native_pair_expansion]
  exact integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ
    (fun j _=>(actual_native_variance_row_gaussian t ht i j f g).1))
private theorem native_coframe_expansion(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (G t (nativeVarianceReturn t ht x f))
      (G t (quadraticSource (fun a=>coframeQuadraticColumn t ht a g) x))=
      ∑i:Fin 11,∑a:QuadraticIndex,(noiseQuadratic a x:ℂ)*
        sourcePair (nativeVarianceRow i f)
          (W t ht (nativeVariancePower i) (nativeVarianceDegree i) x (coframeQuadraticColumn t ht a g)):=by
  simp only[nativeVarianceReturn,LinearMap.sum_apply,Module.End.mul_apply,quadraticSource,map_sum,map_smul,
    sourcePair,sum_inner,inner_sum,inner_smul_right]
  simp only[Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  have h:=native_column_pair t ht x i (nativeVarianceRow i f) (coframeQuadraticColumn t ht a g)
  have hh:=congrArg (fun u:ℂ=>(noiseQuadratic a x:ℂ)*u) h
  simpa only[sourcePair] using hh
private theorem native_coframe_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (G t (nativeVarianceReturn t ht x f))
      (G t (quadraticSource (fun a=>coframeQuadraticColumn t ht a g) x))) γ2:=by
  simp_rw [native_coframe_expansion]
  exact integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ
    (fun a _=>actual_quadratic_profile_pair_integrable t ht (nativeVariancePower i) (nativeVarianceDegree i) a
      (nativeVarianceRow i f) (coframeQuadraticColumn t ht a g)))
private theorem coframe_native_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (G t (quadraticSource (fun a=>coframeQuadraticColumn t ht a f) x))
      (G t (nativeVarianceReturn t ht x g))) γ2:=by
  have h:=Complex.conjCLE.toContinuousLinearMap.integrable_comp (native_coframe_integrable t ht g f)
  exact h.congr (Eventually.of_forall (fun x=>GaussNativeForm.pair_conjugate _ _))
private theorem coframe_pair_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (G t (quadraticSource (fun a=>coframeQuadraticColumn t ht a f) x))
      (G t (quadraticSource (fun a=>coframeQuadraticColumn t ht a g) x))) γ2:=by
  have h:=(actual_corrected_coframe_square_gaussian t ht f g).1
  exact h.congr (Eventually.of_forall (fun x=>by
    dsimp only
    rw [actual_corrected_coframe_quadratic_return,actual_corrected_coframe_quadratic_return,complete_pair]))

/-- The complete actual H0² Gaussian form is internally integrable from all 121 native
pairs, 81 coframe pairs and both ordered exponential-polynomial cross sectors. -/
theorem actual_corrected_whole_H0_square_integrable(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (diagonalAction (K t ht x f)) (diagonalAction (K t ht x g))) γ2:=by
  have h:=((native_pair_integrable t ht f g).add (native_coframe_integrable t ht f g)).add
    ((coframe_native_integrable t ht f g).add (coframe_pair_integrable t ht f g))
  exact h.congr (Eventually.of_forall (fun x=>by
    dsimp only[Pi.add_apply]
    rw [actual_whole_variance_column,actual_whole_variance_column,complete_pair]
    simp only[wholeVarianceColumn,map_add,sourcePair,inner_add_left,inner_add_right]
    ring))
end LowEnergy.FirstCurrentWholeVariance
