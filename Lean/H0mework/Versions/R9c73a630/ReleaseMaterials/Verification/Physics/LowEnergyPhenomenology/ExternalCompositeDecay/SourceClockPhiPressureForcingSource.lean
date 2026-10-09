import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeMatchedPressurePayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPrimitiveCurrentCancellation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentForcingPressure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceClockPhiRadiusSourceCurrent SourceClockPhiRadiusAcceleration
open SourceClockPhiCombinedScalePressure FirstCurrentGeometricPayer
open SourceClockPhiNativeMatchedSource SourceClockPhiMatchedElectricSource
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentJointBudget
open ReverseNativeClock ReverseNativeFrequencyWard ReverseScalarGaugeWard ReverseBalancedForcePayer
open PrimitiveInputPayer ScalarInputJointNoether FirstCurrentJointDifference FirstCurrentMatchedPressure
open JointDifferenceMatchedSource FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare OriginalRPrimitiveDifference
open SourceLocalizedInverseFormPayment SourceResolventBandLimit ClockPhiHeatCorrectedCovarianceSource
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev n:ℝ:=sourceTime 0
private abbrev U:End:=inverseVolumeAction
private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
private abbrev H0:End:=diagonalAction
private abbrev P:End:=positivePrimitive
private abbrev Phi:End:=SourceScalarAffineScaleTransport.generator
attribute [local irreducible] sourcePair embed diagonalAction correctedCompleteCore wholeClockState
  wholeSourceNext clockSourcePair balancedCompressionForce matchedDifferenceRemainder
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem radius_pair(f g:QuantumTest):sourcePair f (r g)=sourcePair (r f) g:=multiply_pair _ _ _ _
private theorem inverse_radius_pair(f g:QuantumTest):sourcePair (S f) (r g)=sourcePair f g:=by
  have h:r (S f)=f:=by
    apply DFunLike.ext;intro z
    change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
    rw [smul_smul,←Complex.ofReal_mul]
    have hp:0<phiRadius z:=Real.sqrt_pos.2 (by positivity)
    unfold phiReciprocal
    rw [mul_inv_cancel₀ hp.ne',Complex.ofReal_one,one_smul]
  rw [radius_pair,h]
private theorem primitive_split(w:QuantumTest):
    phiSquare w=(n/2:ℂ) • P w-(n/4:ℂ) • electricAction w:=by
  unfold P positivePrimitive
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_add,smul_smul]
  have hn:(n:ℂ)≠0:=Complex.ofReal_ne_zero.mpr n_pos.ne'
  have hc:(n/2:ℂ)*(2/(n:ℂ))=1:=by field_simp
  rw [hc,one_smul]
  module

/-- The complete opposite-pole forcing of the original CF force. Its H0 commutator retains the own cutoff. -/
def oppositeCompressionSource(F:Index)(z:ℂ)(w f:QuantumTest):QuantumTest:=
  balancedCompressionForce F (oppositeForcing z w f)+bracket H0 (balancedCompressionForce F) w

theorem actual_opposite_compression_source(F:Index)(z:ℂ)(w f:QuantumTest)(he:H0 w=f+z • w):
    H0 (balancedCompressionForce F w)=oppositeCompressionSource F z w f+star z • balancedCompressionForce F w:=by
  have h:=actual_opposite_full_forcing z w f he
  unfold oppositeCompressionSource bracket
  simp only [Module.End.mul_apply,LinearMap.sub_apply,h,map_add,map_smul]
  module

/-- The ordered primitive and electric sources combine to the literal scalar current. No weighted forcing norm is introduced. -/
theorem actual_opposite_compression_primitive_transfer(F:Index)(z:ℂ)(w f:QuantumTest)(he:H0 w=f+z • w):
    sourcePair (balancedCompressionForce F w) (phiSquare f)=
      (n/2:ℂ)*sourcePair (oppositeCompressionSource F z w f) (P w)-
      (n/4:ℂ)*sourcePair (oppositeCompressionSource F z w f) (electricAction w)-
      (n/2:ℂ)*sourcePair (balancedCompressionForce F w) (U (Phi w)):=by
  have hc:=congrArg (fun v:QuantumTest=>sourcePair (balancedCompressionForce F w) v)
    (LinearMap.congr_fun original_phi_square_current w)
  simp only [bracket,Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_r,pair_smul_r] at hc
  have hh:=diagonalAction_pair (balancedCompressionForce F w) (phiSquare w)
  have hy:=actual_opposite_compression_source F z w f he
  change sourcePair (balancedCompressionForce F w) (H0 (phiSquare w))=
    sourcePair (H0 (balancedCompressionForce F w)) (phiSquare w) at hh
  rw [hy,pair_add_l,pair_smul_l,star_star] at hh
  rw [he,map_add,map_smul,pair_add_r,pair_smul_r] at hc
  rw [hh,primitive_split w,pair_sub_r,pair_smul_r,pair_smul_r] at hc
  linear_combination (norm:=ring) -hc

/-- This is the complete non-forcing word inside the actual matched remainder; the covariance and electric words are retained. -/
def pressureSourceRemainder(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  let w:=wholeClockState s hs half advanced m ell F g x q
  (6:ℂ) • U (combinedGenerator w)-(12:ℂ) • U w-(9:ℂ) • U (SourceGaugeScaleTransport.generator w)+
    (18:ℂ) • U (wholeFrequencyJet s hs half advanced m ell F g x q)-
    U (correctedCompleteCore s hs x.1 x.2 (reverseClockReturn s hs x.1 x.2 ((wholeSourceNext s hs half advanced m ell F g q).1)))+
    (36*(wholeStep s hs half advanced m ell F g:ℂ)) •
      U (correctedCompleteCore s hs x.1 x.2 (weightedElectricCurrent (frequencyState half advanced m ell F g q)))

theorem actual_pressure_full_forcing_split(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    sourcePressureVector s hs half advanced m ell F g x q=
      r (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))+
      ((14*n*reverseNoetherFactor half:ℝ):ℂ) • S
        ((432/(n:ℂ)) • (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2+
          pressureSourceRemainder s hs half advanced m ell F g x q):=by
  simp only [sourcePressureVector,matchedDifferenceRemainder,pressureSourceRemainder,map_add,map_sub,map_smul]
  module

/-- Testing the actual pressure against rφ times its own full forcing removes the inverse radius exactly, including the full 6048 a forcing coefficient. -/
theorem actual_pressure_full_forcing_pair(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    let w:=wholeClockState s hs half advanced m ell F g x q
    let f:=(clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2
    sourcePair (sourcePressureVector s hs half advanced m ell F g x q) (r f)=
      ((6048*reverseNoetherFactor half:ℝ):ℂ)*sourcePair f f+
      sourcePair (balancedCompressionForce F w) (phiSquare f)+
      ((14*n*reverseNoetherFactor half:ℝ):ℂ)*sourcePair (pressureSourceRemainder s hs half advanced m ell F g x q) f:=by
  dsimp only
  rw [actual_pressure_full_forcing_split,pair_add_l,pair_smul_l,inverse_radius_pair,pair_add_l,pair_smul_l]
  have hr(y f:QuantumTest):sourcePair (r y) (r f)=sourcePair y (phiSquare f):=by
    change sourcePair (r y) (r f)=sourcePair y (r (r f))
    exact (radius_pair y (r f)).symm
  rw [hr]
  simp only [Complex.star_def,map_div₀,map_ofNat,Complex.conj_ofReal]
  field_simp [Complex.ofReal_ne_zero.mpr n_pos.ne']
  push_cast
  ring

/-- The real physical full-forcing square is generated by one ordered pressure test and the opposite CF-force source, retaining the scalar current and all six remainder words. -/
theorem actual_whole_pressure_primitive_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let w:=wholeClockState s hs half advanced m ell F g x q
    let f:=(clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2
    sourcePair (sourcePressureVector s hs half advanced m ell F g x q) (r f)=
      ((6048*reverseNoetherFactor half:ℝ):ℂ)*sourcePair f f+
      (n/2:ℂ)*sourcePair (oppositeCompressionSource F z w f) (P w)-
      (n/4:ℂ)*sourcePair (oppositeCompressionSource F z w f) (electricAction w)-
      (n/2:ℂ)*sourcePair (balancedCompressionForce F w) (U (Phi w))+
      ((14*n*reverseNoetherFactor half:ℝ):ℂ)*sourcePair (pressureSourceRemainder s hs half advanced m ell F g x q) f:=by
  dsimp only
  have he:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  have hw:H0 (wholeClockState s hs half advanced m ell F g x q)=
    (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2+
      actualFrequency advanced (sourceNoetherFrequency half) q • wholeClockState s hs half advanced m ell F g x q:=by
    simpa only [wholeClockState] using he
  rw [actual_pressure_full_forcing_pair,actual_opposite_compression_primitive_transfer F _ _ _ hw]
  ring
end LowEnergy.FirstCurrentForcingPressure
