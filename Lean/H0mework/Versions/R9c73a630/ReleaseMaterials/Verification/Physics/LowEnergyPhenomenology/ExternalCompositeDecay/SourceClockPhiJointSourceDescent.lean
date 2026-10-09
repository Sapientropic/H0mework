import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedElectricTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentElectricSuccessor
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourcePhysicalKineticSquare
open SourceClockPhiMatchedElectricSource SourceClockPhiNativeMatchedSource SourceClockPhiCombinedScalePressure
open SourceClockReflectedForm SourceScalarInverseNativeEnergy SourceScalarShiftedBulk SourceScalarEssentialBudget
open FirstCurrentJointBudget FirstCurrentJointBudgetNext FirstCurrentGeometricPayer
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ClockPhiHeatCorrectedCovarianceSource FirstCurrentPayerNext
open scoped ContDiff InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev Dc : End := dilation
private abbrev D : End := combinedGenerator
private abbrev M : End := matchedTester
private abbrev X : End := weightedElectricCurrent
private abbrev P : End := electricPrimitive
private abbrev W : End := magneticVolumeWeight
private abbrev B : End := scalarBulkComplete
private abbrev H0 : End := diagonalAction
attribute [local irreducible] sourcePair embed diagonalAction normalizedState normalizedForcing correctedCompleteCore updatedForcing
  weightedElectricCurrent matchedTester combinedGenerator volumeAction inverseVolumeAction dilation scalarBulkComplete geometricScalarCurrent
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
/-- Full signed source action: scalar Noether, reflected/gauge fields, true electric primitive,
UD/Dc cross, literal frequency and the original matched negative square. -/
def jointSourceKernel(half advanced:Bool)(z:ℂ)(a b:QuantumTest×QuantumTest):ℂ:=
  (-Complex.I*(scalarNoetherFactor half:ℂ)*(if advanced then (-1:ℂ) else 1))*
    (sourcePair a.2 (B b.1)-(1/2:ℂ)*sourcePair a.1 (geometricScalarCurrent b.1))+
  (3*(n:ℂ))*reflectedPair (U a.1) (U b.1)+(10:ℂ)*gaugePair (U a.1) (U b.1)+
  (magneticPrimitiveFactor:ℂ)*sourcePair a.1 ((W*wedgeAction) b.1)+
  (9*(n:ℂ)/4)*Complex.I*sourcePair (U (D a.1)) (Dc (U b.1))+
  (35*(n:ℂ)/96)*sourcePair (U (D a.1)) (U (D b.1))+
  6*sourcePair (M a.1) (z • b.1)-(n/48:ℂ)*sourcePair (M a.1) (M b.1)-
  (7*(n:ℂ))*scalarPair a.1 b.1

def jointSourcePrice(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  (jointSourceKernel half advanced z a a).re
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only[sourcePair] using! inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem work_contact(F:Index)(g:diagonal.domain)(w:QuantumTest):
    magneticPrimitiveWork 1 w=magneticPrimitiveFactor*(sourcePair w ((W*wedgeAction) w)).re:=by
  have h:=(actual_weighted_electric_midpoint F g 1 w).2
  unfold magneticPrimitiveWork
  norm_num at h ⊢
  linear_combination (-2*magneticPrimitiveFactor)*h
private theorem kernel_diagonal(F:Index)(g:diagonal.domain)(half advanced:Bool)(z:ℂ)(w f:QuantumTest):
    jointSourcePrice half advanced z (w,f)=
      scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
        ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)+
      electricGeometricPrice 1 w z:=by
  have hR:(reflectedPair (U w) (U w)).re=reflectedForm (U w):=rfl
  have hG:(gaugePair (U w) (U w)).re=gaugeForm (U w):=by
    unfold gaugePair gaugeForm
    simp only[Complex.mul_re,Complex.div_re,Complex.div_im,Complex.re_ofNat,Complex.im_ofNat,
      Complex.normSq_ofNat]
    norm_num
  have hS:(scalarPair w w).re=inverseNativeEnergy w:=by
    unfold scalarPair inverseNativeEnergy
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun a _=>pair_norm _)
  rw [electricGeometricPrice,work_contact F g]
  unfold jointSourcePrice jointSourceKernel remainingGeometricPrice
  simp only[Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.div_re,Complex.div_im,Complex.normSq_ofNat,Complex.re_ofNat,
    Complex.im_ofNat,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,hR,hG,hS,
    pair_norm (U (D w)),pair_norm (M w)]
  cases advanced <;> norm_num <;> ring
private theorem kernel_add_left(half advanced:Bool)(z:ℂ)(a b c:QuantumTest×QuantumTest):
    jointSourceKernel half advanced z (a+b) c=
      jointSourceKernel half advanced z a c+jointSourceKernel half advanced z b c:=by
  simp only[jointSourceKernel,reflectedPair,gaugePair,scalarPair,Prod.fst_add,Prod.snd_add,
    map_add,sourcePair,inner_add_left,Finset.sum_add_distrib]
  ring
private theorem kernel_add_right(half advanced:Bool)(z:ℂ)(a b c:QuantumTest×QuantumTest):
    jointSourceKernel half advanced z a (b+c)=
      jointSourceKernel half advanced z a b+jointSourceKernel half advanced z a c:=by
  simp only[jointSourceKernel,reflectedPair,gaugePair,scalarPair,Prod.fst_add,
    map_add,smul_add,sourcePair,inner_add_right,Finset.sum_add_distrib]
  ring
private theorem kernel_real_left(half advanced:Bool)(z:ℂ)(t:ℝ)(a b:QuantumTest×QuantumTest):
    jointSourceKernel half advanced z ((t:ℂ) • a) b=(t:ℂ)*jointSourceKernel half advanced z a b:=by
  simp only[jointSourceKernel,reflectedPair,gaugePair,scalarPair,Prod.smul_fst,Prod.smul_snd,
    map_smul,sourcePair,inner_smul_left,Complex.conj_ofReal,←Finset.mul_sum]
  ring
private theorem kernel_real_right(half advanced:Bool)(z:ℂ)(t:ℝ)(a b:QuantumTest×QuantumTest):
    jointSourceKernel half advanced z a ((t:ℂ) • b)=(t:ℂ)*jointSourceKernel half advanced z a b:=by
  simp only[jointSourceKernel,reflectedPair,gaugePair,scalarPair,Prod.smul_fst,
    map_smul,smul_comm z (t:ℂ),sourcePair,inner_smul_right,←Finset.mul_sum]
  ring
private theorem price_polynomial(half advanced:Bool)(z:ℂ)(t:ℝ)(a d:QuantumTest×QuantumTest):
    jointSourcePrice half advanced z (a+(t:ℂ) • d)=
      jointSourcePrice half advanced z a+
      t*((jointSourceKernel half advanced z a d).re+(jointSourceKernel half advanced z d a).re)+
      t^2*jointSourcePrice half advanced z d:=by
  simp only[jointSourcePrice,kernel_add_left,kernel_add_right,kernel_real_left,kernel_real_right,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- Actual forcing successor: the commutator keeps every original Hamiltonian term. -/
def electricSourceDirection(a:QuantumTest×QuantumTest):QuantumTest×QuantumTest:=
  (X a.1,X a.2+bracket H0 X a.1)
def jointSourceSlope(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  (jointSourceKernel half advanced z a (electricSourceDirection a)).re+
    (jointSourceKernel half advanced z (electricSourceDirection a) a).re
def jointSourceCurvature(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  jointSourcePrice half advanced z (electricSourceDirection a)
def jointSourceStep(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  -jointSourceSlope half advanced z a/(2*(|jointSourceCurvature half advanced z a|+1))
def jointSourceNext(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):QuantumTest×QuantumTest:=
  a+((jointSourceStep half advanced z a:ℝ):ℂ) • electricSourceDirection a
private theorem price_descent(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):
    jointSourcePrice half advanced z (jointSourceNext half advanced z a) ≤
      jointSourcePrice half advanced z a-
      (jointSourceSlope half advanced z a)^2/(4*(|jointSourceCurvature half advanced z a|+1)):=by
  rw [jointSourceNext,price_polynomial]
  change jointSourcePrice half advanced z a+jointSourceStep half advanced z a*jointSourceSlope half advanced z a+
    (jointSourceStep half advanced z a)^2*jointSourceCurvature half advanced z a ≤ _
  unfold jointSourceStep
  let A:=jointSourceSlope half advanced z a
  let C:=jointSourceCurvature half advanced z a
  change _+(-A/(2*(|C|+1)))*A+(-A/(2*(|C|+1)))^2*C ≤ _-A^2/(4*(|C|+1))
  have hp:0 < |C|+1:=by positivity
  have hC:C ≤ |C|+1:=by linarith[le_abs_self C]
  have h:=mul_le_mul_of_nonneg_left hC (sq_nonneg A)
  field_simp [hp.ne']
  nlinarith only[h]
private theorem source_next(H:End)(z:ℂ)(a d:QuantumTest×QuantumTest)(t:ℝ)
    (ha:H a.1=a.2+z • a.1)(hd:H d.1=d.2+z • d.1):
    H (a+(t:ℂ) • d).1=(a+(t:ℂ) • d).2+z • (a+(t:ℂ) • d).1:=by
  simp only[Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,map_add,map_smul,ha,hd,
    smul_add,smul_smul]
  module
private theorem source_direction(z:ℂ)(a:QuantumTest×QuantumTest)(ha:H0 a.1=a.2+z • a.1):
    H0 (electricSourceDirection a).1=(electricSourceDirection a).2+z • (electricSourceDirection a).1:=by
  simp only[electricSourceDirection,bracket,Module.End.mul_apply,LinearMap.sub_apply,ha,map_add,map_smul]
  module
private theorem source_matched_next(F:Index)(g:diagonal.domain)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):
    M (jointSourceNext half advanced z a).1=
      M a.1+(jointSourceStep half advanced z a:ℂ) • matchedElectricSuccessor a.1:=by
  change M (weightedElectricEndpoint (jointSourceStep half advanced z a) false a.1)=_
  simpa only[Bool.false_eq_true,ite_false] using
    actual_matched_electric_endpoint F g (jointSourceStep half advanced z a) false a.1
/-- The actual complete joint source chooses its own finite electric step and pays a definite descent;
no price, derivative norm, endpoint bound or tail is supplied by the caller. -/
theorem actual_joint_source_variational_update(s:ℝ)(hs:0<s)(ξ η:ℝ)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain)
    (hz:(actualFrequency advanced (sourceNoetherFrequency half) x).im≠0):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) x
    let w:=correctedCompleteCore s hs ξ η (normalizedState m ell F z hz g)
    let f:=updatedForcing s hs (ξ,η) m ell F z hz g
    let a:QuantumTest×QuantumTest:=(w,f)
    let b:=jointSourceNext half advanced z a
    jointSourcePrice half advanced z a=
      scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
        electricGeometricPrice 1 w z ∧
    H0 b.1=b.2+z • b.1 ∧
    M b.1=M w+(jointSourceStep half advanced z a:ℂ) • matchedElectricSuccessor w ∧
    jointSourcePrice half advanced z b ≤ jointSourcePrice half advanced z a-
      (jointSourceSlope half advanced z a)^2/(4*(|jointSourceCurvature half advanced z a|+1)):=by
  dsimp only
  have he:=actual_corrected_full_forcing s hs (ξ,η) m ell F
    (actualFrequency advanced (sourceNoetherFrequency half) x) hz g
  dsimp only at he
  refine ⟨?_,?_,?_,price_descent half advanced _ _⟩
  · rw [kernel_diagonal F g]
    unfold correctedScalarNoetherPrice
    ring
  · apply source_next H0 _ _ _ _ he
    exact source_direction _ _ he
  · exact source_matched_next F g half advanced _ _
end LowEnergy.FirstCurrentElectricSuccessor
