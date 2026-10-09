import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiTwoPolePrimitiveWord
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRPrimitiveDifference
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiNormalizedScalarBudget SourceResolventBandLimit
open SourceCoframeDilation SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure
open SourceClockPhiNativeMatchedSource SourceClockReflectedForm SourceScalarInverseNativeEnergy
open SourceScalarShiftedBulk SourceScalarEssentialBudget SourceClockPhiMatchedElectricSource SourceScalarVirialBulk
open ClockPhiHeatCorrectedCovarianceSource SourceScalarDoubleCurrent
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentWholeVariance
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare FirstCurrentDilationPrimitive
open FirstCurrentJointBudget OriginalRCommutatorSource SourceLocalizedInverseFormPayment SourceResolventBandLimit
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev K(s:ℝ)(hs:0<s)(x:ℝ×ℝ):End:=correctedCompleteCore s hs x.1 x.2
private abbrev n:ℝ:=sourceTime 0
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev B:End:=scalarBulkComplete
attribute [local irreducible] sourcePair embed diagonalAction positivePrimitive correctedCompleteCore
  normalizedState normalizedForcing sourceTime scalarBulkComplete inverseVolumeAction combinedGenerator matchedTester

def primitiveResidualFields(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
    ((sourcePair a.2 (B a.1)).im-(sourcePair a.1 (geometricScalarCurrent a.1)).im/2)-
  3*(sourcePair a.1 (U (nativeDilationWord a.1))).re+
  6*z.im*((sourcePair (U (D a.1)) a.1).im-(sourcePair a.1 (coframeElectricCurrent a.1)).im)+
  12*n*spinForm (U a.1)+12*n*densityForm (U a.1)-24*n*radiusForm a.1-
  12*(sourcePair a.1 (U (scalarSpatialAction a.1))).re-13*n*inverseNativeEnergy a.1+
  (35*n/96)*‖embed (U (D a.1))‖^2
private theorem dilation_fields(half advanced:Bool)(z:ℂ)(w f:QuantumTest):
    dilationSourcePrice half advanced z w f=primitiveResidualFields half advanced z (w,f)+3*primitiveEnergy f:=by
  unfold dilationSourcePrice primitiveResidualFields
  ring
private theorem source_clock(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(z:ℂ)(w f:QuantumTest)(he:diagonalAction w=f+z • w):
    diagonalAction (clockSourcePair s hs x (w,f)).1=(clockSourcePair s hs x (w,f)).2+
      z • (clockSourcePair s hs x (w,f)).1:=by
  simp only [clockSourcePair,bracket,Module.End.mul_apply,LinearMap.sub_apply,he,map_add,map_smul]
  module

/-- The complete original physical action consumes the cancellation before Gaussian integration. The two source forcing legs and native departments are literal; no Pplus-weighted H0-square price remains. -/
theorem actual_full_physical_primitive_clock_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(x:ℝ×ℝ)(w f:QuantumTest)(he:diagonalAction w=f+z • w):
    let b:=clockSourcePair s hs x (w,f)
    physicalJointPrice half advanced z b=
      primitiveResidualFields half advanced z b+
      3*primitiveEnergy (K s hs x f)-3*primitiveEnergy (K s hs x (oppositeForcing z w f))+
      12*z.im*(sourcePair (actualPrimitiveCommutator s hs x w) (positivePrimitive (K s hs x w))).im+
      originalNormalizerPrice s hs x (w,f)-2*gaugeForm (U b.1)-
      8*(sourcePair b.1 (U (magneticAction b.1))).re:=by
  dsimp only
  let b:=clockSourcePair s hs x (w,f)
  have hb:=source_clock s hs x z w f he
  have hp:=actual_full_source_dilation_joint_balance half advanced m ell F z hz g b.1 b.2 hb
  have ho:=actual_opposite_forcing_norm z b.1 b.2 hb
  have hd:=actual_two_pole_primitive_clock_difference s hs x z w f
  dsimp only at hd
  rw [oppositePrimitiveDebit,ho,dilation_fields] at hp
  have hn:originalNormalizerPrice s hs x (w,f)=
      (432/n)*‖embed b.2‖^2-(n/48)*‖embed (matchedTester b.1)+((144/n:ℝ):ℂ) • embed b.2‖^2:=rfl
  change physicalJointPrice half advanced z b=primitiveResidualFields half advanced z b+
    3*primitiveEnergy (K s hs x f)-3*primitiveEnergy (K s hs x (oppositeForcing z w f))+
    12*z.im*(sourcePair (actualPrimitiveCommutator s hs x w) (positivePrimitive (K s hs x w))).im+
    originalNormalizerPrice s hs x (w,f)-2*gaugeForm (U b.1)-8*(sourcePair b.1 (U (magneticAction b.1))).re
  change primitiveEnergy b.2-primitiveEnergy (oppositeForcing z b.1 b.2)=_ at hd
  linarith only [hp,hd,hn]

/-- The actual wholeSourceNext supplies its original full H0 equation, so the returned primitive work has no new source hypothesis. -/
theorem actual_original_whole_physical_primitive_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=wholeSourceNext s hs half advanced m ell F g q
    let b:=clockSourcePair s hs x a
    physicalJointPrice half advanced z b=
      primitiveResidualFields half advanced z b+3*primitiveEnergy (K s hs x a.2)-
      3*primitiveEnergy (K s hs x (oppositeForcing z a.1 a.2))+
      12*z.im*(sourcePair (actualPrimitiveCommutator s hs x a.1) (positivePrimitive (K s hs x a.1))).im+
      originalNormalizerPrice s hs x a-2*gaugeForm (U b.1)-8*(sourcePair b.1 (U (magneticAction b.1))).re:=by
  dsimp only
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hμ:0<sourceNoetherFrequency half:=by linarith [actual_source_noether_gap half]
  have hz:(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
    cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
      Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
  exact actual_full_physical_primitive_clock_return s hs half advanced m ell F _ hz g x _ _
    (((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.1)
end LowEnergy.OriginalRPrimitiveDifference
