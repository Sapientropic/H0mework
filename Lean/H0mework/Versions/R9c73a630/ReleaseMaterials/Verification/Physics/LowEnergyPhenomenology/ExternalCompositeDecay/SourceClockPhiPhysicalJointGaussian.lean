import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarNoetherGaussian
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiAdmissibleElectricWard
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNativeComplementJointSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedFieldGaussian
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianCubicContraction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1600000
noncomputable section
namespace LowEnergy.FirstCurrentAdmissibleElectric.PhysicalGaussian
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore ClockPhiHeatComparisonWork
open ClockPhiHeatCorrectedCovarianceSource SourceClockPhiProfileNativeReturn SourceClockPhiProfileLocalNativeReturn
open SourceClockPhiCorrectedGaussianPair SourceClockPhiCorrectedWeightTransport SourceClockPhiForwardNativeReturn
open SourceClockPhiCombinedScalePressure SourceScalarVirialBulk SourceClockPhiHeatLocalNativeGaussian
open SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource SourceClockReflectedForm SourceScalarInverseNativeEnergy
open SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarDoubleCurrent SourceScalarOscillatorAbsorption
open SourceHamiltonianVolume SourceClockPhiMatchedElectricSource SourceInverseNoetherEnergy SourceScalarNativeComparison
open FirstCurrentJointBudget FirstCurrentJointBudgetNext FirstCurrentElectricSuccessor FirstCurrentGeometricPayer
open FirstCurrentPayerNext SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open NativePointReturn PositiveClockGenerator ScalarGaussian MeasureTheory Filter
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev n:ℝ:=sourceTime 0
private abbrev U:End:=inverseVolumeAction
private abbrev Dc:End:=dilation
private abbrev D:End:=combinedGenerator
private abbrev M:End:=matchedTester
private abbrev B:End:=scalarBulkComplete
private abbrev W:End:=magneticVolumeWeight
private abbrev K:=correctedCompleteCore
private abbrev G(t:ℝ):=SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
attribute [local irreducible] diagonalAction sourcePair embed scalarKinetic scalarBulkComplete
  normalizedState updatedForcing matchedTester
private theorem coeff_first(t ξ η:ℝ)(x y:SourceCoordinateSlice)(h:x.1=y.1):
    correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  dsimp at h
  subst y₁
  rfl
private theorem U_pair(f g:QuantumTest):sourcePair f (inverseVolumeAction g)=sourcePair (inverseVolumeAction f) g:=
  multiply_pair _ _ _ _
private theorem forwardU_pair(t:ℝ)(ht:0<t)(f g:QuantumTest):
    sourcePair f (forwardUAction t ht.le g)=sourcePair (forwardUAction t ht.le f) g:=multiply_pair _ _ _ _
private theorem U_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    inverseVolumeAction (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η (forwardUAction t ht.le f):=
  LinearMap.congr_fun (actual_corrected_complete_inverse_volume t ht ξ η) f
private theorem D_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    combinedGenerator (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η (combinedGenerator f):=
  LinearMap.congr_fun (actual_corrected_complete_generator_commute t ht ξ η).eq f
private theorem complete_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (correctedCompleteCore t ht ξ η g)=
      sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) g):=by
  change sourcePair (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)))
    (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) g)))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact ClockPhiConservativeHeatSource.clockProfileAction_pair _ _ _ _ _ _
private theorem inverse_sector(t:ℝ)(ht:0<t)(X:End)(p q:ℝ)
    (law:∀ξ η:ℝ,∀f g:QuantumTest,
      sourcePair (correctedCompleteCore t ht ξ η f) (X (correctedCompleteCore t ht ξ η g))=
        sourcePair f (correctedProfileWeight t ht p q ξ η (X g))) (f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g)))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g))) ∂γ.prod γ)=
      sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (p+q*(q-3)/18) (X g)):=by
  have he(x:ℝ×ℝ):sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g)))=
      sourcePair (forwardUAction t ht.le f) (correctedProfileWeight t ht p q x.1 x.2 (X g)):=by
    rw [U_pair,U_return,law]
  simpa only [he] using
    actual_corrected_gaussian_weighted_source_pair t ht p q (forwardUAction t ht.le f) (X g)

private theorem n_pos : 0 < n := by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem inverse_volume (f : QuantumTest) : U (volumeAction f)=f := by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z)=f z
    rw [smul_smul]
    simp only [reciprocalVolume,Complex.ofReal_inv,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (volume_pos ⟨z,hz⟩).ne'),one_smul]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem scalar_U (f : QuantumTest) : scalarKinetic (U f)=U (scalarKinetic f) := by
  have h:=LinearMap.congr_fun scalar_kinetic_volume.eq (U f)
  change scalarKinetic (volumeAction (U f))=volumeAction (scalarKinetic (U f)) at h
  rw [volume_inverse] at h
  have hi:=congrArg U h
  rw [inverse_volume] at hi
  exact hi.symm
private theorem inverse_scalar_form (f : QuantumTest) :
    (sourcePair f (U (scalarKinetic f))).re= -(n/2)*inverseNativeEnergy f := by
  have h:=actual_native_scalar_form (U f)
  rw [scalar_U,volume_inverse,original_inverse_native_return] at h
  rw [U_pair]
  exact h


private def scalarAtom:Fin 4→End:=![scalarKinetic,centeredAction,vacuumLinearAction,vacuumConstantAction]
private def atomExponent:Fin 4→ℝ:=![-7/9,17/9,14/9,12/9]
private def atomMean(s:ℝ)(hs:0<s)(i:Fin 4)(f:QuantumTest):ℂ:=
  sourcePair (forwardUAction s hs.le f) (gaussianProfileWeight s hs (atomExponent i) (scalarAtom i f))
private theorem atom_gaussian(s:ℝ)(hs:0<s)(i:Fin 4)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (K s hs x.1 x.2 f) (U (scalarAtom i (K s hs x.1 x.2 f)))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (K s hs x.1 x.2 f) (U (scalarAtom i (K s hs x.1 x.2 f))) ∂γ.prod γ)=atomMean s hs i f:=by
  have h0:=inverse_sector s hs scalarKinetic (-2/3) 2
    (fun ξ η p q=>actual_complete_profile_scalar_source s hs (correctedCoefficient s ξ η)
      (coefficient_smooth s hs ξ η) (coeff_first s ξ η) p q) f f
  have h1:=inverse_sector s hs centeredAction (4/3) (-2)
    (fun ξ η p q=>actual_profile_complete_centered_pair s hs (correctedCoefficient s ξ η)
      (coefficient_smooth s hs ξ η) (coeff_first s ξ η) p q) f f
  have h2:=inverse_sector s hs vacuumLinearAction (4/3) (-1)
    (fun ξ η p q=>actual_profile_complete_vacuum_linear_pair s hs (correctedCoefficient s ξ η)
      (coefficient_smooth s hs ξ η) (coeff_first s ξ η) p q) f f
  have h3:=inverse_sector s hs vacuumConstantAction (4/3) 0
    (fun ξ η p q=>actual_profile_complete_vacuum_constant_pair s hs (correctedCoefficient s ξ η)
      (coefficient_smooth s hs ξ η) (coeff_first s ξ η) p q) f f
  fin_cases i
  · convert h0 using 1 <;> norm_num[scalarAtom,atomMean,atomExponent]
  · convert h1 using 1 <;> norm_num[scalarAtom,atomMean,atomExponent]
  · convert h2 using 1 <;> norm_num[scalarAtom,atomMean,atomExponent]
  · convert h3 using 1 <;> norm_num[scalarAtom,atomMean,atomExponent]
private def scalarCoefficient:Fin 3→Fin 4→ℂ:=
  ![![-8,8,-8,2],![-14,34,-56,128/5],![-2/(n:ℂ),0,0,0]]
private def scalarQuantity:Fin 3→QuantumTest→ℝ:=![scalarEnergy,scalarNativePrice,inverseNativeEnergy]
def scalarMean(s:ℝ)(hs:0<s)(i:Fin 3)(f:QuantumTest):ℝ:=
  (∑j:Fin 4,scalarCoefficient i j*atomMean s hs j f).re
private theorem scalar_bulk_atoms:scalarBulkComplete=(-8:ℂ) • (U*scalarKinetic)+(8:ℂ) • (U*centeredAction)-
    (8:ℂ) • (U*vacuumLinearAction)+(2:ℂ) • (U*vacuumConstantAction):=by
  have h:=original_bulk_complete_split
  rw [bulkAction,positiveBulk,original_filtered_bulk] at h
  simp only[mul_add,mul_sub,mul_smul_comm] at h
  linear_combination (norm:=module) -h
private theorem scalar_quantity_source(i:Fin 3)(f:QuantumTest):
    scalarQuantity i f=(∑j:Fin 4,scalarCoefficient i j*sourcePair f (U (scalarAtom j f))).re:=by
  fin_cases i
  · change scalarEnergy f=_
    rw [←original_scalar_energy,scalar_bulk_atoms]
    simp only[LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
      pair_add_r,pair_sub_r,pair_smul_r]
    congr 1
    norm_num[scalarCoefficient,scalarAtom,Fin.sum_univ_succ]
    ring
  · unfold scalarQuantity scalarNativePrice scalarNativeBlock
    simp only[LinearMap.add_apply,LinearMap.sub_apply,
      LinearMap.smul_apply,Module.End.mul_apply,pair_add_r,pair_sub_r,pair_smul_r]
    norm_num[scalarCoefficient,scalarAtom,Fin.sum_univ_succ]
    ring
  · have h:=inverse_scalar_form f
    have hn:n≠0:=n_pos.ne'
    change inverseNativeEnergy f=_
    norm_num[scalarCoefficient,scalarAtom,Fin.sum_univ_succ,Complex.mul_re,
      Complex.div_re,Complex.div_im,Complex.normSq_ofReal]
    field_simp [hn]
    nlinarith only[h]
private theorem scalar_gaussian(s:ℝ)(hs:0<s)(i:Fin 3)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>scalarQuantity i (K s hs x.1 x.2 f)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,scalarQuantity i (K s hs x.1 x.2 f) ∂γ.prod γ)=scalarMean s hs i f:=by
  have hi(j:Fin 4):Integrable (fun x:ℝ×ℝ=>scalarCoefficient i j*
      sourcePair (K s hs x.1 x.2 f) (U (scalarAtom j (K s hs x.1 x.2 f)))) (γ.prod γ):=
    (atom_gaussian s hs j f).1.const_mul _
  have hsum:=integrable_finsetSum Finset.univ (fun j _=>hi j)
  simp_rw [scalar_quantity_source]
  refine ⟨hsum.re,?_⟩
  have hr:=Complex.reCLM.integral_comp_comm hsum
  simp only[Complex.reCLM_apply] at hr
  rw [hr,integral_finsetSum _ (fun j _=>hi j)]
  simp only[integral_const_mul,(atom_gaussian s hs _ f).2,scalarMean]

private theorem gauge_weight_smooth(i j:Fin 3)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun v=>volume v*gaugeWeight v i j) z.val:=
  volume_smooth.contDiffAt.mul (gaugeWeight_smooth i j z)
private theorem polynomial_smooth(i j:Fin 6):ContDiff ℝ ∞ (fun z:SourceCoordinateSlice=>
    GaussCoframeKinetic.polynomial z.1 i j):=by
  fin_cases i <;> fin_cases j <;> simp [GaussCoframeKinetic.polynomial] <;> fun_prop
private def polynomialAction(i j:Fin 6):End:=multiply
  (fun z=>GaussCoframeKinetic.polynomial z.1 i j) (fun _=>(polynomial_smooth i j).contDiffAt)
private def reflectedPair(f g:QuantumTest):ℂ:=
  ∑i:Fin 6,∑j:Fin 6,sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
    (((coordinateAction i*coordinateAction j)-polynomialAction i j)
      (SourceCoframeCovariantAction.covariantMomentum j g))
private def gaugePair(f g:QuantumTest):ℂ:=
  (1/2:ℂ)*∑a:LieIndex,∑i:Fin 3,∑j:Fin 3,
    sourcePair (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f)
      (multiply (fun z=>volume z*gaugeWeight z i j) (gauge_weight_smooth i j)
        (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) g))
private def scalarPair(f g:QuantumTest):ℂ:=
  ∑a:ScalarIndex,sourcePair (U (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))
    (U (GaussCoreDifferential.covariantMomentum (scalarDirection a) g))
private def localKernel(half advanced:Bool)(z:ℂ)(a b:QuantumTest×QuantumTest):ℂ:=
  (-Complex.I*(scalarNoetherFactor half:ℂ)*(if advanced then (-1:ℂ) else 1))*
    (sourcePair a.2 (B b.1)-(1/2:ℂ)*sourcePair a.1 (geometricScalarCurrent b.1))+
  (3*(n:ℂ))*reflectedPair (U a.1) (U b.1)+(10:ℂ)*gaugePair (U a.1) (U b.1)+
  (magneticPrimitiveFactor:ℂ)*sourcePair a.1 ((W*wedgeAction) b.1)+
  (9*(n:ℂ)/4)*Complex.I*sourcePair (U (D a.1)) (Dc (U b.1))+
  (35*(n:ℂ)/96)*sourcePair (U (D a.1)) (U (D b.1))+
  6*sourcePair (M a.1) (z • b.1)-(n/48:ℂ)*sourcePair (M a.1) (M b.1)-
  (7*(n:ℂ))*scalarPair a.1 b.1


private theorem local_kernel_eq(half advanced:Bool)(z:ℂ)(a b:QuantumTest×QuantumTest):
    localKernel half advanced z a b=jointSourceKernel half advanced z a b:=rfl
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only[sourcePair] using! inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem physical_diagonal(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):
    physicalJointPrice half advanced z a=
      scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
        ((sourcePair a.2 (B a.1)).im-(sourcePair a.1 (geometricScalarCurrent a.1)).im/2)+
      remainingGeometricPrice a.1 z:=by
  have hR:(reflectedPair (U a.1) (U a.1)).re=reflectedForm (U a.1):=rfl
  have hG:(gaugePair (U a.1) (U a.1)).re=gaugeForm (U a.1):=by
    unfold gaugePair gaugeForm
    simp only[Complex.mul_re,Complex.div_re,Complex.div_im,Complex.re_ofNat,Complex.im_ofNat,
      Complex.normSq_ofNat]
    norm_num
  have hS:(scalarPair a.1 a.1).re=inverseNativeEnergy a.1:=by
    unfold scalarPair inverseNativeEnergy
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun j _=>pair_norm _)
  unfold physicalJointPrice physicalJointKernel
  rw [←local_kernel_eq]
  unfold localKernel remainingGeometricPrice
  simp only[Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.div_re,Complex.div_im,Complex.normSq_ofNat,Complex.re_ofNat,
    Complex.im_ofNat,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,hR,hG,hS,
    pair_norm (U (D a.1)),pair_norm (M a.1)]
  cases advanced <;> norm_num <;> ring

private def column (a : QuadraticIndex) (f : QuantumTest) : QuadraticIndex → QuantumTest :=
  fun b => if b=a then f else 0
private theorem single_source (a : QuadraticIndex) (f : QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (column a f) x=(noiseQuadratic a x:ℂ) • f := by
  classical
  unfold quadraticSource column
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim
private theorem source_add (v w : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (v+w) x=quadraticSource v x+quadraticSource w x := by
  simp only [quadraticSource,Pi.add_apply,smul_add,Finset.sum_add_distrib]
private theorem source_sub (v w : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) :
    quadraticSource (v-w) x=quadraticSource v x-quadraticSource w x := by
  simp only [quadraticSource,Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]

private theorem matched_return (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (w : QuantumTest) :
    matchedTester (correctedCompleteCore t ht x.1 x.2 w)=
      correctedCompleteCore t ht x.1 x.2 (quadraticSource (matchedGaussianColumn t ht w) x) := by
  change matchedTester (correctedCompleteCore t ht x.1 x.2 w)=
    correctedCompleteCore t ht x.1 x.2 (quadraticSource
      (column (0,0) (matchedTester w)+column (1,0) (-(noiseAction t ht 1 0 (combinedGenerator w)))+
        column (2,0) (-(noiseAction t ht 0 1 (combinedGenerator w)))) x)
  rw [source_add,source_add,single_source,single_source,single_source,
    actual_corrected_complete_matched_tester]
  simp only [noiseQuadratic,(noiseLinear_values x).1,(noiseLinear_values x).2.1,
    (noiseLinear_values x).2.2,mul_one,Complex.ofReal_one,one_smul,smul_neg]
  congr 1
  have hn : noiseAction t ht x.1 x.2 (combinedGenerator w)=
      (x.1:ℂ) • noiseAction t ht 1 0 (combinedGenerator w)+
      (x.2:ℂ) • noiseAction t ht 0 1 (combinedGenerator w) := by
    apply DFunLike.ext
    intro q
    change (covarianceNoise t x.1 x.2 q:ℂ) • combinedGenerator w q=_
    rw [actual_covariance_noise_affine]
    simp only [Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul]
    rfl
  rw [hn]
  module
private theorem coframe_return (t : ℝ) (ht : 0 < t) (x : ℝ×ℝ) (z : ℂ) (w : QuantumTest) :
    coframeForcing t ht x z w=
      correctedCompleteCore t ht x.1 x.2 (quadraticSource (coframeForcingColumn t ht z w) x) := by
  unfold coframeForcing
  change SourceCoframeCovariantAction.covariantKinetic (correctedCompleteCore t ht x.1 x.2 w)-
      z • correctedCompleteCore t ht x.1 x.2 w=
    correctedCompleteCore t ht x.1 x.2 (quadraticSource
      ((fun a=>coframeQuadraticColumn t ht a w)-column (0,0) (z • w)) x)
  rw [source_sub,single_source,actual_corrected_coframe_quadratic_return]
  simp only [noiseQuadratic,(noiseLinear_values x).1,one_mul,Complex.ofReal_one,one_smul,map_sub,map_smul]

private theorem gain_source(t:ℝ)(v:QuadraticIndex→QuantumTest)(x:ℝ×ℝ):
    G t (quadraticSource v x)=quadraticSource (fun a=>G t (v a)) x:=by
  simp only[quadraticSource,map_sum,map_smul]
private theorem packet_pair(t:ℝ)(ht:0<t)(v w:QuadraticIndex→QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (K t ht x.1 x.2 (quadraticSource v x))
      (K t ht x.1 x.2 (quadraticSource w x))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (K t ht x.1 x.2 (quadraticSource v x))
      (K t ht x.1 x.2 (quadraticSource w x)) ∂γ.prod γ)=coframeGaussianPair t v w:=by
  simpa only[complete_pair,gain_source,Module.End.one_apply,coframeGaussianPair] using
    quadratic_gaussian_pair (fun a=>G t (v a)) (fun a=>G t (w a)) (1:End)
def signedCoframeMean(t:ℝ)(ht:0<t)(z:ℂ)(f:QuantumTest):ℝ:=
  -6*(coframeGaussianPair t (matchedGaussianColumn t ht f) (coframeForcingColumn t ht z f)).re-
    (n/48)*(coframeGaussianPair t (matchedGaussianColumn t ht f) (matchedGaussianColumn t ht f)).re
private def signedCoframePrice(t:ℝ)(ht:0<t)(z:ℂ)(f:QuantumTest)(x:ℝ×ℝ):ℝ:=
  -6*(sourcePair (M (K t ht x.1 x.2 f)) (coframeForcing t ht x z f)).re-
    (n/48)*‖embed (M (K t ht x.1 x.2 f))‖^2
private theorem coframe_gaussian(t:ℝ)(ht:0<t)(z:ℂ)(f:QuantumTest):
    Integrable (signedCoframePrice t ht z f) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,signedCoframePrice t ht z f x ∂γ.prod γ)=signedCoframeMean t ht z f:=by
  have hc:=packet_pair t ht (matchedGaussianColumn t ht f) (coframeForcingColumn t ht z f)
  have hM:=packet_pair t ht (matchedGaussianColumn t ht f) (matchedGaussianColumn t ht f)
  simp_rw [←matched_return,←coframe_return] at hc hM
  have he(x:ℝ×ℝ):signedCoframePrice t ht z f x=
      -6*(sourcePair (M (K t ht x.1 x.2 f)) (coframeForcing t ht x z f)).re-
        (n/48)*(sourcePair (M (K t ht x.1 x.2 f)) (M (K t ht x.1 x.2 f))).re:=by
    rw [pair_norm];rfl
  have hC:Integrable (fun x:ℝ×ℝ=>(sourcePair (M (K t ht x.1 x.2 f)) (coframeForcing t ht x z f)).re) (γ.prod γ):=hc.1.re
  have hS:Integrable (fun x:ℝ×ℝ=>(sourcePair (M (K t ht x.1 x.2 f)) (M (K t ht x.1 x.2 f))).re) (γ.prod γ):=hM.1.re
  refine ⟨((hC.const_mul (-6)).sub (hS.const_mul (n/48))).congr (Eventually.of_forall (fun x=>(he x).symm)),?_⟩
  simp_rw [he]
  rw [integral_sub (hC.const_mul (-6)) (hS.const_mul (n/48)),integral_const_mul,integral_const_mul]
  have hrC:=Complex.reCLM.integral_comp_comm hc.1
  have hrM:=Complex.reCLM.integral_comp_comm hM.1
  simp only[Complex.reCLM_apply] at hrC hrM
  rw [hrC,hrM,hc.2,hM.2]
  rfl

private theorem pair_add_left(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by
  simp only[sourcePair,map_add,inner_add_left]
private theorem pair_smul_left(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by
  simp only[sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem scalar_self (f:QuantumTest):sourcePair f (B f)=((scalarEnergy f:ℝ):ℂ) := by
  have hr:=original_scalar_energy f
  have hp:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B f))
  rw [←original_scalar_pair] at hp
  simp only [Complex.conj_im] at hp
  apply Complex.ext
  · exact hr
  · simp only [Complex.ofReal_im];linarith only [hp]
private theorem scalar_ward (w f:QuantumTest)(z:ℂ)(he:diagonalAction w=f+z • w):
    z.im*scalarEnergy w=(sourcePair f (B w)).im-
      (sourcePair w ((diagonalAction*B-B*diagonalAction) w)).im/2 := by
  have hp:sourcePair w ((diagonalAction*B-B*diagonalAction) w)=
      sourcePair (diagonalAction w) (B w)-sourcePair (B w) (diagonalAction w) := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r,diagonalAction_pair,original_scalar_pair]
  have hbself:sourcePair (B w) w=((scalarEnergy w:ℝ):ℂ) :=
    (original_scalar_pair w w).symm.trans (scalar_self w)
  rw [he,pair_add_left,pair_smul_left,pair_add_r,pair_smul_r,scalar_self,hbself] at hp
  have hc:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B w))
  simp only [Complex.conj_im] at hc
  have hi:=congrArg Complex.im hp
  simp only [Complex.sub_im,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,mul_zero,zero_add] at hi
  linarith only [hi,hc]


private theorem noether_return(half advanced:Bool)(freq:ℝ)(w f:QuantumTest)
    (he:diagonalAction w=f+actualFrequency advanced (sourceNoetherFrequency half) freq • w):
    (if advanced then (-1:ℝ) else 1)*
      ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)=
      sourceNoetherFrequency half*scalarEnergy w+
        (if advanced then (-1:ℝ) else 1)*16*n^2*(quarterPair w).re:=by
  have h:=scalar_ward w f (actualFrequency advanced (sourceNoetherFrequency half) freq) he
  rw [original_scalar_current_geometric] at h
  simp only[LinearMap.add_apply,pair_add_r,Complex.add_im,add_div] at h
  rw [original_complete_scalar_form] at h
  cases advanced <;> simp only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im] at h ⊢ <;> linarith only[h]
private theorem geometric_return(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(z:ℂ)(f:QuantumTest):
    remainingGeometricPrice (K s hs x.1 x.2 f) z=
      (sourcePair (K s hs x.1 x.2 f)
        (SourceClockPhiMatchedDiffusionSource.completeCurrent nativeComplement (K s hs x.1 x.2 f))).re+
      matchedField (K s hs x.1 x.2 f)-scalarNativePrice (K s hs x.1 x.2 f)+signedCoframePrice s hs z f x+
      (35*n/96)*‖embed (U (D (K s hs x.1 x.2 f)))‖^2-
      72*n*‖embed (K s hs x.1 x.2 f)‖^2-7*n*inverseNativeEnergy (K s hs x.1 x.2 f):=by
  have hN:=actual_native_field_scalar_split (K s hs x.1 x.2 f)
  have hC:=actual_remaining_field_coframe_payment (K s hs x.1 x.2 f)
  unfold remainingGeometricPrice signedCoframePrice coframeForcing
  rw [pair_sub_r,Complex.sub_re]
  linear_combination (norm:=ring) -hN-hC
private theorem clock_canonical(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(z:ℂ)(f:QuantumTest):
    diagonalAction (clockSourcePair s hs x (f,diagonalAction f-z • f)).1=
      (clockSourcePair s hs x (f,diagonalAction f-z • f)).2+
        z • (clockSourcePair s hs x (f,diagonalAction f-z • f)).1:=by
  simp only[clockSourcePair,bracket,Module.End.mul_apply,LinearMap.sub_apply,map_sub,map_smul]
  module
private theorem norm_return(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(f:QuantumTest):
    ‖embed (K s hs x.1 x.2 f)‖^2=‖embed (G s f)‖^2:=by
  have h:=congrArg Complex.re (complete_pair s hs x.1 x.2 f f)
  simpa only[pair_norm] using h
private theorem UD_return(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(f:QuantumTest):
    ‖embed (U (D (K s hs x.1 x.2 f)))‖^2=(FirstCurrentPayer.clockUDDensity s hs f).re:=by
  have h:=congrArg Complex.re (FirstCurrentPayer.actual_corrected_UD_clock_density s hs x.1 x.2 f)
  simpa only[←Complex.ofReal_pow,Complex.ofReal_re] using h.symm

def physicalMean(s:ℝ)(hs:0<s)(half advanced:Bool)(freq:ℝ)(f:QuantumTest):ℝ:=
  scalarNoetherFactor half*(sourceNoetherFrequency half*scalarMean s hs 0 f+
    (if advanced then (-1:ℝ) else 1)*16*n^2*(quarterMean s hs f).re)+
  (nativePositiveMean s hs f f+localPositiveMean s hs f f).re+matchedFieldMean s hs f-
  scalarMean s hs 1 f+signedCoframeMean s hs (actualFrequency advanced (sourceNoetherFrequency half) freq) f+
  (35*n/96)*(FirstCurrentPayer.clockUDDensity s hs f).re-72*n*‖embed (G s f)‖^2-7*n*scalarMean s hs 2 f
private def canonicalPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(freq:ℝ)(f:QuantumTest)(x:ℝ×ℝ):ℝ:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
  physicalJointPrice half advanced z (clockSourcePair s hs x (f,diagonalAction f-z • f))
private def gaussianRhs(s:ℝ)(hs:0<s)(half advanced:Bool)(freq:ℝ)(f:QuantumTest)(x:ℝ×ℝ):ℝ:=
  let u:=K s hs x.1 x.2 f
  scalarNoetherFactor half*(sourceNoetherFrequency half*scalarQuantity 0 u+
    (if advanced then (-1:ℝ) else 1)*16*n^2*(quarterPair u).re)+
  (sourcePair u (SourceClockPhiMatchedDiffusionSource.completeCurrent nativeComplement u)).re+matchedField u-
  scalarQuantity 1 u+signedCoframePrice s hs (actualFrequency advanced (sourceNoetherFrequency half) freq) f x+
  (35*n/96)*(FirstCurrentPayer.clockUDDensity s hs f).re-72*n*‖embed (G s f)‖^2-7*n*scalarQuantity 2 u
attribute [local irreducible] correctedCompleteCore completeCurrent nativeComplement coframeForcing
  quarterPair scalarEnergy inverseNativeEnergy scalarNativePrice remainingGeometricPrice
private theorem canonical_price_return(s:ℝ)(hs:0<s)(half advanced:Bool)(freq:ℝ)(f:QuantumTest)(x:ℝ×ℝ):
    canonicalPrice s hs half advanced freq f x=gaussianRhs s hs half advanced freq f x:=by
  unfold canonicalPrice
  rw [physical_diagonal,mul_assoc (scalarNoetherFactor half) (if advanced then (-1:ℝ) else 1),
    noether_return half advanced freq _ _ (clock_canonical s hs x _ f)]
  simp only[clockSourcePair]
  rw [geometric_return,UD_return,norm_return]
  dsimp only[gaussianRhs,scalarQuantity]
  simp only[Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  ring

/-- The complete physical joint price has a genuine Gaussian integral, fixed before any update is chosen. -/
theorem actual_physical_joint_gaussian(s:ℝ)(hs:0<s)(half advanced:Bool)(freq:ℝ)(f:QuantumTest):
    Integrable (canonicalPrice s hs half advanced freq f) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,canonicalPrice s hs half advanced freq f x ∂γ.prod γ)=physicalMean s hs half advanced freq f:=by
  have h0:=scalar_gaussian s hs 0 f
  have h1:=scalar_gaussian s hs 1 f
  have h2:=scalar_gaussian s hs 2 f
  have hQ:=actual_quarter_pair_gaussian s hs f
  have hN:=actual_corrected_native_joint_gaussian s hs f f
  have hF:=actual_corrected_matched_field_gaussian s hs f
  have hC:=coframe_gaussian s hs (actualFrequency advanced (sourceNoetherFrequency half) freq) f
  have hn:=(h0.1.const_mul (sourceNoetherFrequency half)).add
    (hQ.1.re.const_mul ((if advanced then (-1:ℝ) else 1)*16*n^2))
  have hA:=hn.const_mul (scalarNoetherFactor half)
  have hB:=hA.add hN.1.re |>.add hF.1 |>.sub h1.1 |>.add hC.1
  let c:ℝ:=(35*n/96)*(FirstCurrentPayer.clockUDDensity s hs f).re-72*n*‖embed (G s f)‖^2
  have hc:Integrable (fun _:ℝ×ℝ=>c) (γ.prod γ):=integrable_const _
  have hi:Integrable (gaussianRhs s hs half advanced freq f) (γ.prod γ):=by
    apply ((hB.add hc).sub (h2.1.const_mul (7*n))).congr
    exact Eventually.of_forall (fun x=>by
      dsimp only[gaussianRhs,c,Pi.add_apply,Pi.sub_apply]
      simp only[RCLike.re_eq_complex_re]
      ring)
  refine ⟨hi.congr (Eventually.of_forall (fun x=>(canonical_price_return s hs half advanced freq f x).symm)),?_⟩
  simp_rw [canonical_price_return]
  have he:gaussianRhs s hs half advanced freq f=
    (fun x=>scalarNoetherFactor half*(sourceNoetherFrequency half*scalarQuantity 0 (K s hs x.1 x.2 f)+
      (if advanced then (-1:ℝ) else 1)*16*n^2*(quarterPair (K s hs x.1 x.2 f)).re)+
      (sourcePair (K s hs x.1 x.2 f) (SourceClockPhiMatchedDiffusionSource.completeCurrent nativeComplement (K s hs x.1 x.2 f))).re+
      matchedField (K s hs x.1 x.2 f)-scalarQuantity 1 (K s hs x.1 x.2 f)+
      signedCoframePrice s hs (actualFrequency advanced (sourceNoetherFrequency half) freq) f x+c-
      7*n*scalarQuantity 2 (K s hs x.1 x.2 f)):=by funext x;dsimp only[gaussianRhs,c];ring
  rw [he]
  erw [integral_sub (hB.add hc) (h2.1.const_mul (7*n)),integral_add hB hc,
    integral_add (hA.add hN.1.re |>.add hF.1 |>.sub h1.1) hC.1,
    integral_sub (hA.add hN.1.re |>.add hF.1) h1.1,integral_add (hA.add hN.1.re) hF.1,
    integral_add hA hN.1.re,integral_const_mul,integral_add (h0.1.const_mul _) (hQ.1.re.const_mul _)]
  have hrN:=Complex.reCLM.integral_comp_comm hN.1
  have hrQ:=Complex.reCLM.integral_comp_comm hQ.1
  simp only[Complex.reCLM_apply] at hrN hrQ
  simp only[integral_const_mul,RCLike.re_eq_complex_re,hrN,hrQ,h0.2,h1.2,h2.2,hQ.2,hN.2,hF.2,hC.2,integral_const,
    MeasureTheory.probReal_univ,one_smul,physicalMean,c]
  ring

private theorem physical_add_left(half advanced:Bool)(z:ℂ)(a b c:QuantumTest×QuantumTest):
    physicalJointKernel half advanced z (a+b) c=
      physicalJointKernel half advanced z a c+physicalJointKernel half advanced z b c:=by
  simp only[physicalJointKernel,←local_kernel_eq,localKernel,reflectedPair,gaugePair,scalarPair,
    Prod.fst_add,Prod.snd_add,map_add,sourcePair,inner_add_left,Finset.sum_add_distrib]
  ring
private theorem physical_add_right(half advanced:Bool)(z:ℂ)(a b c:QuantumTest×QuantumTest):
    physicalJointKernel half advanced z a (b+c)=
      physicalJointKernel half advanced z a b+physicalJointKernel half advanced z a c:=by
  simp only[physicalJointKernel,←local_kernel_eq,localKernel,reflectedPair,gaugePair,scalarPair,
    Prod.fst_add,map_add,smul_add,sourcePair,inner_add_right,Finset.sum_add_distrib]
  ring
private theorem physical_real_left(half advanced:Bool)(z:ℂ)(t:ℝ)(a b:QuantumTest×QuantumTest):
    physicalJointKernel half advanced z ((t:ℂ) • a) b=(t:ℂ)*physicalJointKernel half advanced z a b:=by
  simp only[physicalJointKernel,←local_kernel_eq,localKernel,reflectedPair,gaugePair,scalarPair,
    Prod.smul_fst,Prod.smul_snd,map_smul,sourcePair,inner_smul_left,Complex.conj_ofReal,←Finset.mul_sum]
  ring
private theorem physical_real_right(half advanced:Bool)(z:ℂ)(t:ℝ)(a b:QuantumTest×QuantumTest):
    physicalJointKernel half advanced z a ((t:ℂ) • b)=(t:ℂ)*physicalJointKernel half advanced z a b:=by
  simp only[physicalJointKernel,←local_kernel_eq,localKernel,reflectedPair,gaugePair,scalarPair,
    Prod.smul_fst,map_smul,smul_comm z (t:ℂ),sourcePair,inner_smul_right,←Finset.mul_sum]
  ring
private theorem physical_price_add(half advanced:Bool)(z:ℂ)(a b:QuantumTest×QuantumTest):
    physicalJointPrice half advanced z (a+b)=physicalJointPrice half advanced z a+physicalJointPrice half advanced z b+
      ((physicalJointKernel half advanced z a b).re+(physicalJointKernel half advanced z b a).re):=by
  simp only[physicalJointPrice,physical_add_left,physical_add_right,Complex.add_re]
  ring
private theorem physical_price_polynomial(half advanced:Bool)(z:ℂ)(t:ℝ)(a b:QuantumTest×QuantumTest):
    physicalJointPrice half advanced z (a+(t:ℂ) • b)=physicalJointPrice half advanced z a+
      t*((physicalJointKernel half advanced z a b).re+(physicalJointKernel half advanced z b a).re)+
      t^2*physicalJointPrice half advanced z b:=by
  simp only[physicalJointPrice,physical_add_left,physical_add_right,physical_real_left,physical_real_right,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring
private def sourceCanonical(z:ℂ)(f:QuantumTest):QuantumTest×QuantumTest:=(f,diagonalAction f-z • f)
private theorem canonical_add(z:ℂ)(f g:QuantumTest):sourceCanonical z (f+g)=sourceCanonical z f+sourceCanonical z g:=by
  apply Prod.ext
  · rfl
  · simp only[sourceCanonical,map_add,smul_add,Prod.snd_add]
    module
private theorem canonical_real(z:ℂ)(t:ℝ)(f:QuantumTest):sourceCanonical z ((t:ℂ) • f)=(t:ℂ) • sourceCanonical z f:=by
  apply Prod.ext
  · rfl
  · simp only[sourceCanonical,map_smul,Prod.smul_snd,smul_sub,smul_smul]
    module
private theorem direction_canonical(z:ℂ)(f:QuantumTest):
    electricSourceDirection (sourceCanonical z f)=sourceCanonical z (weightedElectricCurrent f):=by
  apply Prod.ext
  · rfl
  · simp only[electricSourceDirection,sourceCanonical,bracket,Module.End.mul_apply,LinearMap.sub_apply,map_sub,map_smul]
    module
private theorem clock_add(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(a b:QuantumTest×QuantumTest):
    clockSourcePair s hs x (a+b)=clockSourcePair s hs x a+clockSourcePair s hs x b:=by
  apply Prod.ext
  · simp only[clockSourcePair,Prod.fst_add,map_add]
  · simp only[clockSourcePair,Prod.fst_add,Prod.snd_add,map_add]
    module
private theorem clock_real(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(t:ℝ)(a:QuantumTest×QuantumTest):
    clockSourcePair s hs x ((t:ℂ) • a)=(t:ℂ) • clockSourcePair s hs x a:=by
  apply Prod.ext
  · simp only[clockSourcePair,Prod.smul_fst,map_smul]
  · simp only[clockSourcePair,Prod.smul_fst,Prod.smul_snd,map_smul,smul_add]
private theorem canonical_price_as(s:ℝ)(hs:0<s)(half advanced:Bool)(freq:ℝ)(f:QuantumTest)(x:ℝ×ℝ):
    canonicalPrice s hs half advanced freq f x=physicalJointPrice half advanced
      (actualFrequency advanced (sourceNoetherFrequency half) freq)
      (clockSourcePair s hs x (sourceCanonical (actualFrequency advanced (sourceNoetherFrequency half) freq) f)):=rfl
private theorem cross_return(s:ℝ)(hs:0<s)(half advanced:Bool)(freq:ℝ)(f:QuantumTest)(x:ℝ×ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
    let a:=sourceCanonical z f
    (physicalJointKernel half advanced z (clockSourcePair s hs x a)
      (clockSourcePair s hs x (electricSourceDirection a))).re+
    (physicalJointKernel half advanced z (clockSourcePair s hs x (electricSourceDirection a))
      (clockSourcePair s hs x a)).re=
      canonicalPrice s hs half advanced freq (f+weightedElectricCurrent f) x-
        canonicalPrice s hs half advanced freq f x-canonicalPrice s hs half advanced freq (weightedElectricCurrent f) x:=by
  dsimp only
  rw [direction_canonical,canonical_price_as,canonical_price_as,canonical_price_as,
    canonical_add,clock_add,physical_price_add]
  ring
private theorem canonical_coefficients(s:ℝ)(hs:0<s)(half advanced:Bool)(freq:ℝ)(f:QuantumTest):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
    let a:=sourceCanonical z f
    Integrable (fun x:ℝ×ℝ=>
      (physicalJointKernel half advanced z (clockSourcePair s hs x a)
        (clockSourcePair s hs x (electricSourceDirection a))).re+
      (physicalJointKernel half advanced z (clockSourcePair s hs x (electricSourceDirection a))
        (clockSourcePair s hs x a)).re) (γ.prod γ) ∧
    Integrable (fun x:ℝ×ℝ=>physicalJointPrice half advanced z
      (clockSourcePair s hs x (electricSourceDirection a))) (γ.prod γ) ∧
    averagedJointSlope s hs half advanced z a=
      physicalMean s hs half advanced freq (f+weightedElectricCurrent f)-
        physicalMean s hs half advanced freq f-physicalMean s hs half advanced freq (weightedElectricCurrent f) ∧
    averagedJointCurvature s hs half advanced z a=physicalMean s hs half advanced freq (weightedElectricCurrent f):=by
  dsimp only
  have h0:=actual_physical_joint_gaussian s hs half advanced freq f
  have h1:=actual_physical_joint_gaussian s hs half advanced freq (weightedElectricCurrent f)
  have h2:=actual_physical_joint_gaussian s hs half advanced freq (f+weightedElectricCurrent f)
  have hA:=((h2.1.sub h0.1).sub h1.1).congr
    (Eventually.of_forall (fun x=>(cross_return s hs half advanced freq f x).symm))
  refine ⟨hA,?_,?_,?_⟩
  · rw [direction_canonical]
    change Integrable (canonicalPrice s hs half advanced freq (weightedElectricCurrent f)) (γ.prod γ)
    exact h1.1
  · unfold averagedJointSlope
    simp_rw [cross_return]
    erw [integral_sub (h2.1.sub h0.1) h1.1,integral_sub h2.1 h0.1]
    rw [h2.2,h0.2,h1.2]
  · unfold averagedJointCurvature
    simpa only[direction_canonical,canonical_price_as] using h1.2

/-- The actual normalized event generates both pre-noise coefficients from finite original-source means. -/
theorem actual_averaged_joint_coefficients(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (freq:ℝ)(g:diagonal.domain)(hz:(actualFrequency advanced (sourceNoetherFrequency half) freq).im≠0):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
    let w:=normalizedState m ell F z hz g
    let a:QuantumTest×QuantumTest:=(w,normalizedForcing m ell F z hz g)
    Integrable (fun x:ℝ×ℝ=>
      (physicalJointKernel half advanced z (clockSourcePair s hs x a)
        (clockSourcePair s hs x (electricSourceDirection a))).re+
      (physicalJointKernel half advanced z (clockSourcePair s hs x (electricSourceDirection a))
        (clockSourcePair s hs x a)).re) (γ.prod γ) ∧
    Integrable (fun x:ℝ×ℝ=>physicalJointPrice half advanced z
      (clockSourcePair s hs x (electricSourceDirection a))) (γ.prod γ) ∧
    averagedJointSlope s hs half advanced z a=
      physicalMean s hs half advanced freq (w+weightedElectricCurrent w)-
        physicalMean s hs half advanced freq w-physicalMean s hs half advanced freq (weightedElectricCurrent w) ∧
    averagedJointCurvature s hs half advanced z a=physicalMean s hs half advanced freq (weightedElectricCurrent w):=by
  dsimp only
  have h:=JointElectricSource.actual_full_normalized_source m ell F
    (actualFrequency advanced (sourceNoetherFrequency half) freq) hz g
  have ha:(normalizedState m ell F (actualFrequency advanced (sourceNoetherFrequency half) freq) hz g,
      normalizedForcing m ell F (actualFrequency advanced (sourceNoetherFrequency half) freq) hz g)=
      sourceCanonical (actualFrequency advanced (sourceNoetherFrequency half) freq)
        (normalizedState m ell F (actualFrequency advanced (sourceNoetherFrequency half) freq) hz g):=by
    apply Prod.ext
    · rfl
    · dsimp only[sourceCanonical]
      linear_combination (norm:=module) -h
  rw [ha]
  exact canonical_coefficients s hs half advanced freq _

private def noiseSlope(s:ℝ)(hs:0<s)(half advanced:Bool)(freq:ℝ)(f:QuantumTest)(x:ℝ×ℝ):ℝ:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
  let a:=sourceCanonical z f
  (physicalJointKernel half advanced z (clockSourcePair s hs x a)
    (clockSourcePair s hs x (electricSourceDirection a))).re+
  (physicalJointKernel half advanced z (clockSourcePair s hs x (electricSourceDirection a))
    (clockSourcePair s hs x a)).re
private theorem canonical_price_polynomial(s:ℝ)(hs:0<s)(half advanced:Bool)(freq h:ℝ)(f:QuantumTest)(x:ℝ×ℝ):
    canonicalPrice s hs half advanced freq (f+(h:ℂ) • weightedElectricCurrent f) x=
      canonicalPrice s hs half advanced freq f x+h*noiseSlope s hs half advanced freq f x+
        h^2*canonicalPrice s hs half advanced freq (weightedElectricCurrent f) x:=by
  unfold noiseSlope
  dsimp only
  rw [direction_canonical]
  simp_rw [canonical_price_as]
  rw [canonical_add,canonical_real,clock_add,clock_real,physical_price_polynomial]
private theorem mean_polynomial(s:ℝ)(hs:0<s)(half advanced:Bool)(freq h:ℝ)(f:QuantumTest):
    physicalMean s hs half advanced freq (f+(h:ℂ) • weightedElectricCurrent f)=
      physicalMean s hs half advanced freq f+
      h*averagedJointSlope s hs half advanced (actualFrequency advanced (sourceNoetherFrequency half) freq)
        (sourceCanonical (actualFrequency advanced (sourceNoetherFrequency half) freq) f)+
      h^2*averagedJointCurvature s hs half advanced (actualFrequency advanced (sourceNoetherFrequency half) freq)
        (sourceCanonical (actualFrequency advanced (sourceNoetherFrequency half) freq) f):=by
  have h0:=actual_physical_joint_gaussian s hs half advanced freq f
  have h1:=actual_physical_joint_gaussian s hs half advanced freq (weightedElectricCurrent f)
  have hh:=actual_physical_joint_gaussian s hs half advanced freq (f+(h:ℂ) • weightedElectricCurrent f)
  have hc:=canonical_coefficients s hs half advanced freq f
  have hA:Integrable (noiseSlope s hs half advanced freq f) (γ.prod γ):=hc.1
  rw [←hh.2]
  simp_rw [canonical_price_polynomial]
  erw [integral_add (h0.1.add (hA.const_mul h)) (h1.1.const_mul (h^2)),
    integral_add h0.1 (hA.const_mul h),integral_const_mul,integral_const_mul]
  rw [h0.2,h1.2,hc.2.2.2]
  rfl
private theorem original_pair_canonical(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (normalizedState m ell F z hz g,normalizedForcing m ell F z hz g)=
      sourceCanonical z (normalizedState m ell F z hz g):=by
  have h:=JointElectricSource.actual_full_normalized_source m ell F z hz g
  apply Prod.ext
  · rfl
  · dsimp only[sourceCanonical]
    linear_combination (norm:=module) -h

/-- Every fixed finite electric restriction has the exact full Gaussian physical action,
with the same original forcing and both source-generated coefficient prices. -/
theorem actual_source_joint_mean_polynomial(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (freq h:ℝ)(g:diagonal.domain)(hz:(actualFrequency advanced (sourceNoetherFrequency half) freq).im≠0):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
    let w:=normalizedState m ell F z hz g
    let a:QuantumTest×QuantumTest:=(w,normalizedForcing m ell F z hz g)
    let b:=a+(h:ℂ) • electricSourceDirection a
    Integrable (fun x:ℝ×ℝ=>physicalJointPrice half advanced z (clockSourcePair s hs x b)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,physicalJointPrice half advanced z (clockSourcePair s hs x b) ∂γ.prod γ)=
      physicalMean s hs half advanced freq w+h*averagedJointSlope s hs half advanced z a+
        h^2*averagedJointCurvature s hs half advanced z a:=by
  dsimp only
  rw [original_pair_canonical,direction_canonical,←canonical_real,←canonical_add]
  have hg:=actual_physical_joint_gaussian s hs half advanced freq
    (normalizedState m ell F _ hz g+(h:ℂ) • weightedElectricCurrent (normalizedState m ell F _ hz g))
  constructor
  · change Integrable (canonicalPrice s hs half advanced freq
      (normalizedState m ell F _ hz g+(h:ℂ) • weightedElectricCurrent (normalizedState m ell F _ hz g))) (γ.prod γ)
    exact hg.1
  · have hp:=mean_polynomial s hs half advanced freq h (normalizedState m ell F _ hz g)
    exact hg.2.trans hp

private def responseFraction(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  ‖embed a.1‖/((|averagedJointSlope s hs half advanced z a|+1)*
    (‖embed a.1‖+‖embed (weightedElectricCurrent a.1)‖+1))
def admissibleMeanDebit(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  responseFraction s hs half advanced z a*(averagedJointSlope s hs half advanced z a)^2/
    (4*(|averagedJointCurvature s hs half advanced z a|+1))
private theorem fraction_interval(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):
    0≤responseFraction s hs half advanced z a ∧ responseFraction s hs half advanced z a≤1:=by
  unfold responseFraction
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    have ha:=norm_nonneg (embed a.1)
    have hr:=norm_nonneg (embed (weightedElectricCurrent a.1))
    have hA:=abs_nonneg (averagedJointSlope s hs half advanced z a)
    nlinarith [mul_nonneg hA (show 0≤‖embed a.1‖+‖embed (weightedElectricCurrent a.1)‖+1 by positivity)]
private theorem scalar_descent(A C lam:ℝ)(hlam:0≤lam)(hlam1:lam≤1):
    (-A/(2*(|C|+1))*lam)*A+(-A/(2*(|C|+1))*lam)^2*C≤ -lam*A^2/(4*(|C|+1)):=by
  have hd:0 < |C|+1:=by positivity
  have hC:lam*C≤|C|+1:=by
    calc lam*C≤lam*(|C|+1):=mul_le_mul_of_nonneg_left (by linarith[le_abs_self C]) hlam
         _≤|C|+1:=by nlinarith only[hlam1,hd]
  have h:=mul_le_mul_of_nonneg_left hC (mul_nonneg hlam (sq_nonneg A))
  field_simp [hd.ne']
  nlinarith only[h]

/-- The same admissible input that the common Ward consumer pays now lowers the complete original Gaussian joint price. -/
theorem actual_admissible_joint_mean_descent(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (freq:ℝ)(g:diagonal.domain)(hz:(actualFrequency advanced (sourceNoetherFrequency half) freq).im≠0):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
    let w:=normalizedState m ell F z hz g
    let a:QuantumTest×QuantumTest:=(w,normalizedForcing m ell F z hz g)
    let b:=admissibleElectricNext s hs half advanced z a
    Integrable (fun x:ℝ×ℝ=>physicalJointPrice half advanced z (clockSourcePair s hs x b)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,physicalJointPrice half advanced z (clockSourcePair s hs x b) ∂γ.prod γ)≤
      physicalMean s hs half advanced freq w-admissibleMeanDebit s hs half advanced z a:=by
  dsimp only
  let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
  let w:=normalizedState m ell F z hz g
  let a:QuantumTest×QuantumTest:=(w,normalizedForcing m ell F z hz g)
  have hp:=actual_source_joint_mean_polynomial s hs half advanced m ell F freq
    (admissibleElectricStep s hs half advanced z a) g hz
  dsimp only at hp
  refine ⟨hp.1,?_⟩
  unfold admissibleElectricNext
  rw [hp.2]
  have hlam:=fraction_interval s hs half advanced z a
  have hd:=scalar_descent (averagedJointSlope s hs half advanced z a)
    (averagedJointCurvature s hs half advanced z a) (responseFraction s hs half advanced z a) hlam.1 hlam.2
  change physicalMean s hs half advanced freq w+
    admissibleElectricStep s hs half advanced z a*averagedJointSlope s hs half advanced z a+
    (admissibleElectricStep s hs half advanced z a)^2*averagedJointCurvature s hs half advanced z a≤_
  have ht:admissibleElectricStep s hs half advanced z a=
      (-averagedJointSlope s hs half advanced z a/(2*(|averagedJointCurvature s hs half advanced z a|+1)))*
        responseFraction s hs half advanced z a:=rfl
  rw [ht]
  unfold admissibleMeanDebit
  have hpay:=add_le_add_left hd (physicalMean s hs half advanced freq w)
  convert hpay using 1 <;> ring
end LowEnergy.FirstCurrentAdmissibleElectric.PhysicalGaussian
