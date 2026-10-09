import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPrimitiveNoether
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentPrimitiveNoether
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourcePhysicalKineticSquare
open SourceClockPhiMatchedElectricSource SourceClockPhiNativeMatchedSource SourceClockPhiCombinedScalePressure
open SourceClockReflectedForm SourceScalarInverseNativeEnergy SourceScalarShiftedBulk SourceScalarEssentialBudget
open FirstCurrentJointBudget FirstCurrentJointBudgetNext FirstCurrentGeometricPayer
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ClockPhiHeatCorrectedCovarianceSource FirstCurrentPayerNext FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier
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
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem physical_diagonal(half advanced:Bool)(z:ℂ)(w f:QuantumTest):
    physicalJointPrice half advanced z (w,f)=
      scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
        ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)+
      remainingGeometricPrice w z:=by
  have hR:(reflectedPair (U w) (U w)).re=reflectedForm (U w):=rfl
  have hG:(gaugePair (U w) (U w)).re=gaugeForm (U w):=by
    unfold gaugePair gaugeForm
    simp only[Complex.mul_re,Complex.div_re,Complex.div_im,Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat]
    norm_num
  have hS:(scalarPair w w).re=inverseNativeEnergy w:=by
    unfold scalarPair inverseNativeEnergy
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun a _=>pair_norm _)
  unfold physicalJointPrice physicalJointKernel FirstCurrentElectricSuccessor.jointSourceKernel remainingGeometricPrice
  change (((-Complex.I*(scalarNoetherFactor half:ℂ)*(if advanced then (-1:ℂ) else 1))*
    (sourcePair f (B w)-(1/2:ℂ)*sourcePair w (geometricScalarCurrent w))+
    (3*(n:ℂ))*reflectedPair (U w) (U w)+(10:ℂ)*gaugePair (U w) (U w)+
    (magneticPrimitiveFactor:ℂ)*sourcePair w ((W*wedgeAction) w)+
    (9*(n:ℂ)/4)*Complex.I*sourcePair (U (D w)) (Dc (U w))+
    (35*(n:ℂ)/96)*sourcePair (U (D w)) (U (D w))+
    6*sourcePair (M w) (z • w)-(n/48:ℂ)*sourcePair (M w) (M w)-
    (7*(n:ℂ))*scalarPair w w)-(magneticPrimitiveFactor:ℂ)*sourcePair w ((W*wedgeAction) w)+
    4*sourcePair w (U (SourceScalarVirialBulk.magneticAction w))).re=_
  simp only[Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.div_re,Complex.div_im,Complex.normSq_ofNat,Complex.re_ofNat,
    Complex.im_ofNat,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,hR,hG,hS,
    pair_norm (U (D w)),pair_norm (M w)]
  cases advanced <;> norm_num <;> ring

/-- Full scalar Noether and geometric source, now with the primitive's real negative frequency potentials
and its own complete electric Noether work paying magnetism. -/
def primitiveJointPrice(half advanced:Bool)(z:ℂ)(w f:QuantumTest):ℝ:=
  scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
    ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)+
  3*n*reflectedForm (U w)+10*gaugeForm (U w)+magneticNoetherPrice z w f-
  (9*n/4)*(sourcePair (U (D w)) (Dc (U w))).im+(35*n/96)*‖embed (U (D w))‖^2+
  primitivePhasePrice z w f-(n/48)*‖embed (M w)‖^2-7*n*inverseNativeEnergy w

/-- The actual updated action consumes both primitive Noether mechanisms on one full source.
Neither endpoint energy nor a desired upper bound is supplied. -/
theorem actual_updated_primitive_joint_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
    physicalJointPrice half advanced z a≤primitiveJointPrice half advanced z a.1 a.2:=by
  dsimp only
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
  have hs0:=actual_updated_primitive_noether_source s hs half advanced m ell F g q x
  have hphase:=hs0.2.1
  have hmag:=hs0.2.2.2
  change physicalJointPrice half advanced z a≤primitiveJointPrice half advanced z a.1 a.2
  rw [show a=(a.1,a.2) from (Prod.eta a).symm,physical_diagonal]
  unfold remainingGeometricPrice primitiveJointPrice
  rw [hphase]
  linarith only[hmag]

/-- The same joint price accepts every generated complete source equation, including original channel forces. -/
theorem actual_full_source_primitive_joint_payment(half advanced:Bool)(m ell:ℕ)(F:Index)
    (z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(w f:QuantumTest)(he:H0 w=f+z • w):
    physicalJointPrice half advanced z (w,f)≤primitiveJointPrice half advanced z w f:=by
  have hs0:=actual_full_source_primitive_noether m ell F z hz g w f he
  have hphase:=hs0.2.1
  have hmag:=hs0.2.2.2
  rw [physical_diagonal]
  unfold remainingGeometricPrice primitiveJointPrice
  rw [hphase]
  linarith only[hmag]
end LowEnergy.FirstCurrentPrimitiveNoether
