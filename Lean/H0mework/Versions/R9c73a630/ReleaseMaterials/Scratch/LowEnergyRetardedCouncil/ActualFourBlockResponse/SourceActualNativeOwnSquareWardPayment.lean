import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualUnweightedSquareCurrentPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseQuadraticMoment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualShiftedQuadraticWardPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovariancePairTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualNativeOwnSquareWardPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy SourcePhysicalKineticSquare SourceScalarPositiveBulkWard
open SourceScalarPairedTransport
open SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarInverseBulk SourceHamiltonianScaleJet
open SourceNativeCutoffContact SourceClockYukawaCubicCurrent SourceRetardedGraph
open ActualUnweightedSquareCurrentPayment ActualScalarPhaseJet ActualPhaseBulkSquare
open ActualPhaseWardIntertwiner ActualScalarPhaseFrequencyReturn ActualScalarPhaseQuadraticMoment
open SourceJointScaleBudget SourceEscapeCurrent SourceMinimalGraphParticular SourceDilationRemainder
open ActualMixedCompressionShape SourceCoframeVolume
open ActualMixedWindowGram ActualMixedCovarianceTail ActualMixedCovariancePairTail
open SourceClockPhiSecondBulk
open ActualVectorJointCost SourceScalarInverseNativeEnergy
open MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators ENNReal
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair resolventCore compressionCore diagonalAction phaseForce
  phaseSecond shiftedSquare phaseHamiltonianSquare inverseWeightedBulkJet shiftedInverseWard

elab "paid_native_square%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseBulkSquare 0) "LowEnergy") "ActualPhaseBulkSquare"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem local_add(A B:End):
    InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative (A+B)=
      InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative A+
      InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative B := by
  simp only [InverseVolumeWardAlgebra.inverseLocalPolynomial,map_add,smul_add]
  module
private theorem local_smul(c:ℂ)(A:End):
    InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative (c • A)=
      c • InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative A := by
  simp only [InverseVolumeWardAlgebra.inverseLocalPolynomial,map_smul,smul_smul]
  module
private theorem coframe_right(B:End):
    scaleDerivative (B*inverseVolumeAction)=scaleDerivative B*inverseVolumeAction-
      (3:ℂ) • (B*inverseVolumeAction) := by
  rw [(paid_native_square% coframe_product),inverse_coframe,mul_smul_comm]
  module
private theorem coframe_local_right(A:End):
    InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative (A*inverseVolumeAction)=
      InverseVolumeWardAlgebra.localPolynomial scaleDerivative A*inverseVolumeAction := by
  simp only [InverseVolumeWardAlgebra.inverseLocalPolynomial,InverseVolumeWardAlgebra.localPolynomial,
    coframe_right,map_sub,map_smul,add_mul,sub_mul,smul_mul_assoc]
  simp only [smul_sub,smul_smul]
  module
private theorem force_square_local_zero:
    InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative (phaseForce*phaseForce)=0 := by
  have he:scaleDerivative (phaseForce*phaseForce)=(-6:ℂ) • (phaseForce*phaseForce) := by
    rw [(paid_native_square% coframe_product),actual_source_phase_force_weights.2.2,
      smul_mul_assoc,mul_smul_comm]
    module
  simp only [InverseVolumeWardAlgebra.inverseLocalPolynomial,he,map_smul,smul_smul]
  module

/-- All three original coframe derivatives of the full unweighted phase square
return to the actual local action. The force square is killed by its true
source weight -6; no H0 homogeneity is assumed. -/
theorem actual_phase_square_coframe_local:
    InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative phaseHamiltonianSquare=
      (-48*(phaseCoefficient:ℂ)) •
        (localAction*inverseVolumeAction+inverseVolumeAction*localAction) := by
  have hH:InverseVolumeWardAlgebra.localPolynomial scaleDerivative diagonalAction=
      (48:ℂ) • localAction := by
    exact source_local_from_scale_jet
  rw [actual_source_phase_square,local_add,local_smul,local_smul,local_add,
    coframe_local_right,InverseVolumeWardAlgebra.inverse_local_mul scaleDerivative
      (paid_native_square% coframe_product) inverseVolumeAction diagonalAction inverse_coframe,
    force_square_local_zero,hH]
  simp only [smul_zero,add_zero,smul_mul_assoc,mul_smul_comm,←smul_add,smul_smul]
  module

/-- The original native and Own square words remain separate at their true
source positions until the complete coframe Ward polynomial is evaluated. -/
def nativeSquareWord(F:Index):End:=phaseSecond (compressionCore F*compressionCore F)
def ownSquareWord(F:Index):End:=phaseSecond (phaseSquareOwn F)

theorem actual_native_own_square_source(F:Index):
    nativeSquareWord F+ownSquareWord F=phaseHamiltonianSquare := by
  unfold nativeSquareWord ownSquareWord phaseHamiltonianSquare phaseSquareOwn
  rw [map_sub]
  module

/-- This source cancellation pays the entire coframe inventory of both words
at once, keeping the raw graded projection and all six ordered Own terms. -/
theorem actual_native_own_coframe_inventory(F:Index):
    InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative (nativeSquareWord F)+
      InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative (ownSquareWord F)=
      (-48*(phaseCoefficient:ℂ)) •
        (localAction*inverseVolumeAction+inverseVolumeAction*localAction) := by
  rw [←local_add,actual_native_own_square_source,actual_phase_square_coframe_local]

/-- Every original Own leg is expanded before any response or estimate. -/
theorem actual_own_square_six_source(F:Index):
    ownSquareWord F=
      (-(phaseCoefficient:ℂ) • (inverseVolumeAction-coreCompression F inverseVolumeAction)-wholePhaseShape F)*diagonalAction+
      defectAction F*(-(phaseCoefficient:ℂ) • inverseVolumeAction)+
      (2:ℂ) • (phaseJet (defectAction F)*phaseJet diagonalAction)+
      phaseSecond (compressionCore F)*defectAction F+
      compressionCore F*(-(phaseCoefficient:ℂ) • (inverseVolumeAction-coreCompression F inverseVolumeAction)-wholePhaseShape F)+
      (2:ℂ) • (phaseJet (compressionCore F)*phaseJet (defectAction F)) :=
  actual_source_phase_square_own_shape F


private theorem mixed_add(A B:End):
    InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge (A+B)=
      InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge A+
      InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge B := by
  simp only [InverseVolumeWardAlgebra.mixedPolynomial,map_add,map_sub,smul_add,smul_sub]
  module
private theorem affine_add(A B:End):
    InverseVolumeWardAlgebra.affinePolynomial deltaPhi (A+B)=
      InverseVolumeWardAlgebra.affinePolynomial deltaPhi A+
      InverseVolumeWardAlgebra.affinePolynomial deltaPhi B := by
  simp only [InverseVolumeWardAlgebra.affinePolynomial,map_add,smul_add]
  module

/-- The whole source field after the three coframe jets have been evaluated
on Native plus Own together. The true gamma and both local/U orders remain. -/
def sourceSquareField : End :=
  InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge phaseHamiltonianSquare+
    (vacuumJetCoefficient:ℂ) • InverseVolumeWardAlgebra.affinePolynomial deltaPhi
      ((-48*(phaseCoefficient:ℂ)) • (localAction*inverseVolumeAction+inverseVolumeAction*localAction))

theorem actual_native_own_whole_ward(F:Index):
    inverseWeightedBulkJet (nativeSquareWord F)+inverseWeightedBulkJet (ownSquareWord F)=sourceSquareField := by
  unfold inverseWeightedBulkJet InverseVolumeWardAlgebra.inverseWard
  rw [add_add_add_comm,←mixed_add,actual_native_own_square_source,←smul_add,←affine_add,
    actual_native_own_coframe_inventory]
  rfl

/-- The Phi+2 shift is the original phase intertwiner, internally paid before
this reduced source field is used on any moving resolvent state. -/
theorem actual_shifted_source_field:
    phaseSecond (shiftedInverseWard (diagonalAction*diagonalAction))=sourceSquareField := by
  have hw:inverseWeightedBulkJet phaseHamiltonianSquare=sourceSquareField := by
    unfold inverseWeightedBulkJet InverseVolumeWardAlgebra.inverseWard
    rw [actual_phase_square_coframe_local]
    rfl
  unfold phaseHamiltonianSquare at hw
  rw [actual_source_inverse_ward_phase_shift] at hw
  exact hw

/-- The original CF insertion carries native and Own currents together. -/
def nativeOwnFlux(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  sourcePair (coreWindow m ell F z hz g)
    (thetaAction m ell (((R*(compressionCore F*sourceSquareField-sourceSquareField*compressionCore F))*R) g))

/-- All six ordered Own words have been consumed in the coframe reduction
while the actual CF insertion itself remains whole. -/
theorem actual_native_own_flux_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    ActualShiftedQuadraticWardPayment.nativeResponseCorrection m ell F z hz g=nativeOwnFlux m ell F z hz g := by
  have hB:ActualShiftedQuadraticWardPayment.shiftedSquare=sourceSquareField := by
    unfold ActualShiftedQuadraticWardPayment.shiftedSquare
    exact actual_shifted_source_field
  unfold ActualShiftedQuadraticWardPayment.nativeResponseCorrection nativeOwnFlux
  rw [hB]
  dsimp only
  have hC:diagonalAction-defectAction F=compressionCore F := by unfold defectAction;abel
  have he:resolventCore F z hz*(diagonalAction*sourceSquareField-sourceSquareField*diagonalAction)-
      resolventCore F z hz*(defectAction F*sourceSquareField-sourceSquareField*defectAction F)=
      resolventCore F z hz*(compressionCore F*sourceSquareField-sourceSquareField*compressionCore F) := by
    rw [←hC]
    noncomm_ring
  rw [he]

private theorem mu_positive:0<sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large
private theorem causal_nonreal(advanced:Bool)(w:ℝ):(causalFrequency advanced sourceMu w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,SourceResolventBandLimit.line_im] using mu_positive.ne'
private def coreFrequency(advanced:Bool)(F:Index)(g:QuantumTest)(w:ℝ):QuantumTest :=
  resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced w) g

def nativeOwnPressure(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  let z:=causalFrequency advanced sourceMu w
  let hz:=causal_nonreal advanced w
  let q:=coreWindow m ell F z hz g
  inverseForm q+(8/phaseCoefficient)*‖embed (phaseForce q)‖^2+
    (1/(2*phaseCoefficient))*(nativeOwnFlux m ell F z hz g).re

private theorem actual_radial_source(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):
    (ActualShiftedQuadraticWardPayment.radialResponseCorrection m ell F
      (causalFrequency advanced sourceMu w) (causal_nonreal advanced w) g).re=
      radialSlot m ell (coreFrequency advanced F g w) := by
  rw [actual_radial_slot_commutator]
  unfold ActualShiftedQuadraticWardPayment.radialResponseCorrection coreWindow
  have hB:ActualShiftedQuadraticWardPayment.shiftedSquare=ActualUnweightedSquareCurrentPayment.shiftedSquare := by
    unfold ActualShiftedQuadraticWardPayment.shiftedSquare ActualUnweightedSquareCurrentPayment.shiftedSquare
    rfl
  rw [hB]
  rfl

private theorem actual_pressure_return(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):
    nativeOwnPressure advanced m ell F g w=
      ActualShiftedQuadraticWardPayment.wholePositivePayment advanced m ell F g w-
        radialSlot m ell (coreFrequency advanced F g w)/(2*phaseCoefficient) := by
  unfold nativeOwnPressure ActualShiftedQuadraticWardPayment.wholePositivePayment
  dsimp only
  rw [ActualShiftedQuadraticWardPayment.actual_live_response_parts,Complex.add_re,
    actual_native_own_flux_source,actual_radial_source]
  ring

/-- The actual positive inverse/force form and whole Native+Own insertion
are paid coherently: the only remaining price is the two original radial
half windows with source coefficient 216/3481 below 1/16. No current sign,
Own norm, or target flux budget is supplied. -/
theorem actual_native_own_pressure_causal_price(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      Integrable (nativeOwnPressure advanced m ell F g) ∧
      |∫w:ℝ,nativeOwnPressure advanced m ell F g w| ≤ ε+(216/3481:ℝ)*
        ((∫w:ℝ,inverseForm (thetaAction (m/2) m (coreFrequency advanced F g w)))+
          (∫w:ℝ,inverseForm (thetaAction (ell/2) ell (coreFrequency advanced F g w)))) := by
  intro ε hε
  obtain ⟨N,hN⟩:=ActualShiftedQuadraticWardPayment.actual_whole_positive_payment_tail g ε hε
  refine ⟨max N 1,fun m hm ell hml=>?_⟩
  filter_upwards [hN m (by omega) ell hml] with F hF
  intro advanced
  have h:=hF advanced
  have hr:=actual_radial_slot_causal_window_price advanced m ell (by omega) hml F g
  have hi:Integrable (fun w:ℝ=>radialSlot m ell (coreFrequency advanced F g w)):=hr.1
  have hb:=hr.2
  have he:nativeOwnPressure advanced m ell F g=(fun w:ℝ=>
      ActualShiftedQuadraticWardPayment.wholePositivePayment advanced m ell F g w-
        radialSlot m ell (coreFrequency advanced F g w)/(2*phaseCoefficient)):=by
    funext w
    exact actual_pressure_return advanced m ell F g w
  rw [he]
  refine ⟨h.1.sub (hi.div_const _),?_⟩
  rw [integral_sub h.1 (hi.div_const _),integral_div]
  apply (abs_sub _ _).trans
  have hc:=actual_phase_coefficient_positive
  rw [abs_div,abs_of_pos (by positivity:0<2*phaseCoefficient)]
  have hn:|∫w:ℝ,radialSlot m ell (coreFrequency advanced F g w)| ≤
      ∫w:ℝ,|radialSlot m ell (coreFrequency advanced F g w)|:=by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun w:ℝ=>radialSlot m ell (coreFrequency advanced F g w))
  have hp:=div_le_div_of_nonneg_right hn (by positivity:0 ≤ 2*phaseCoefficient)
  exact add_le_add h.2 (hp.trans hb)


elab "paid_native_phi%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarVirialBulk 0) "LowEnergy") "SourceScalarVirialBulk"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_native_inverse%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeBulk 0) "LowEnergy") "SourceScalarInverseBulk"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem affine_smul(c:ℂ)(A:End):
    InverseVolumeWardAlgebra.affinePolynomial deltaPhi (c • A)=
      c • InverseVolumeWardAlgebra.affinePolynomial deltaPhi A := by
  simp only [InverseVolumeWardAlgebra.affinePolynomial,map_smul,smul_smul]
  module
private theorem affine_inverse_left(A:End):
    InverseVolumeWardAlgebra.affinePolynomial deltaPhi (inverseVolumeAction*A)=
      inverseVolumeAction*InverseVolumeWardAlgebra.affinePolynomial deltaPhi A := by
  have h(B:End):deltaPhi (inverseVolumeAction*B)=inverseVolumeAction*deltaPhi B := by
    rw [(paid_native_square% phi_product),inverse_phi,zero_mul,zero_add]
  simp only [InverseVolumeWardAlgebra.affinePolynomial,h,mul_add,mul_sub,mul_smul_comm]
private theorem affine_inverse_right(A:End):
    InverseVolumeWardAlgebra.affinePolynomial deltaPhi (A*inverseVolumeAction)=
      InverseVolumeWardAlgebra.affinePolynomial deltaPhi A*inverseVolumeAction := by
  have h(B:End):deltaPhi (B*inverseVolumeAction)=deltaPhi B*inverseVolumeAction := by
    rw [(paid_native_square% phi_product),inverse_phi,mul_zero,add_zero]
  simp only [InverseVolumeWardAlgebra.affinePolynomial,h,add_mul,sub_mul,smul_mul_assoc]
private theorem actual_affine_local_jet:
    vacuumJet=(48:ℂ) • InverseVolumeWardAlgebra.affinePolynomial deltaPhi localAction := by
  have h:(paid_native_phi% coframeLocalJet)=(48:ℂ) • localAction := source_local_from_scale_jet
  unfold vacuumJet
  rw [h]
  simp only [InverseVolumeWardAlgebra.affinePolynomial,map_smul,smul_smul]
  module
private theorem vacuum_constant_volume:
    vacuumConstantAction=((sourceTime 0:ℂ)*(‖SourceQuantumScalarChart.vacuum‖^2:ℂ)) • volumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((sourceTime 0*volume z*‖SourceQuantumScalarChart.vacuum‖^2:ℝ):ℂ) • f z=
    ((sourceTime 0:ℂ)*(‖SourceQuantumScalarChart.vacuum‖^2:ℂ)) • ((volume z:ℂ) • f z)
  simp only [smul_smul,Complex.ofReal_mul,Complex.ofReal_pow]
  congr 1
  ring

/-- The true gamma times all three coframe and two affine derivatives is
central after both original inverse-volume legs return. This pays that entire
source department exactly after all six projection-defect terms return. -/
theorem actual_whole_coframe_ward_central:
    (vacuumJetCoefficient:ℂ) • InverseVolumeWardAlgebra.affinePolynomial deltaPhi
      ((-48*(phaseCoefficient:ℂ)) • (localAction*inverseVolumeAction+inverseVolumeAction*localAction))=
      (-4*(phaseCoefficient:ℂ)*(sourceTime 0:ℂ)*(‖SourceQuantumScalarChart.vacuum‖^2:ℂ)) • (1:End) := by
  have hc:=original_vacuum_compensation
  rw [actual_affine_local_jet] at hc
  have he:((vacuumJetCoefficient:ℂ)*(48:ℂ)) • InverseVolumeWardAlgebra.affinePolynomial deltaPhi localAction=
      (2:ℂ) • vacuumConstantAction := by
    simpa only [smul_smul] using hc
  have hl:=congrArg (fun A:End=>A*inverseVolumeAction) he
  have hr:=congrArg (fun A:End=>inverseVolumeAction*A) he
  simp only [smul_mul_assoc,mul_smul_comm] at hl hr
  rw [affine_smul,affine_add,affine_inverse_right,affine_inverse_left]
  simp only [smul_smul,smul_add]
  have hcoef:(vacuumJetCoefficient:ℂ)*(-48*(phaseCoefficient:ℂ))=
      -(phaseCoefficient:ℂ)*((vacuumJetCoefficient:ℂ)*48) := by ring
  rw [hcoef,←smul_smul,hl,←smul_smul,hr,vacuum_constant_volume]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,(paid_native_inverse% volume_right),
    (paid_native_inverse% volume_left)]
  module

def mixedSquareField:End:=InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge phaseHamiltonianSquare

theorem actual_whole_source_mixed_central:
    sourceSquareField=mixedSquareField+
      (-4*(phaseCoefficient:ℂ)*(sourceTime 0:ℂ)*(‖SourceQuantumScalarChart.vacuum‖^2:ℂ)) • (1:End) := by
  unfold sourceSquareField mixedSquareField
  rw [actual_whole_coframe_ward_central]

/-- The source coframe inventory contributes zero to the whole Native+Own
CF insertion, for every actual compression, without a sign or tail premise. -/
theorem actual_native_own_coframe_insertion_zero(F:Index):
    compressionCore F*((vacuumJetCoefficient:ℂ) • InverseVolumeWardAlgebra.affinePolynomial deltaPhi
      ((-48*(phaseCoefficient:ℂ)) • (localAction*inverseVolumeAction+inverseVolumeAction*localAction)))-
    ((vacuumJetCoefficient:ℂ) • InverseVolumeWardAlgebra.affinePolynomial deltaPhi
      ((-48*(phaseCoefficient:ℂ)) • (localAction*inverseVolumeAction+inverseVolumeAction*localAction)))*compressionCore F=0 := by
  rw [actual_whole_coframe_ward_central]
  simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,sub_self]

/-- Both original native and Own currents are now returned through only the
actual Phi/Gauge mixed source field. No coframe correction is discarded. -/
theorem actual_native_own_mixed_flux(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    nativeOwnFlux m ell F z hz g=
      sourcePair (coreWindow m ell F z hz g)
        (thetaAction m ell (((resolventCore F z hz*
          (compressionCore F*mixedSquareField-mixedSquareField*compressionCore F))*resolventCore F z hz) g)) := by
  unfold nativeOwnFlux
  dsimp only
  rw [actual_whole_source_mixed_central]
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  have he:compressionCore F*mixedSquareField+
      (-4*(phaseCoefficient:ℂ)*(sourceTime 0:ℂ)*(‖SourceQuantumScalarChart.vacuum‖^2:ℂ)) • compressionCore F-
      (mixedSquareField*compressionCore F+
        (-4*(phaseCoefficient:ℂ)*(sourceTime 0:ℂ)*(‖SourceQuantumScalarChart.vacuum‖^2:ℂ)) • compressionCore F)=
      compressionCore F*mixedSquareField-mixedSquareField*compressionCore F := by abel
  rw [he]


/-- The original Phi acts on the remaining mixed field after the phase return. -/
theorem actual_remaining_mixed_second:
    mixedSquareField=(4:ℂ) • secondJet phaseHamiltonianSquare-deltaGauge (secondJet phaseHamiltonianSquare) := by
  unfold mixedSquareField InverseVolumeWardAlgebra.mixedPolynomial secondJet
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,map_sub,smul_sub]
  module

private theorem actual_mixed_pair(A:End)(f h:QuantumTest):
    sourcePair f (InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge A h)=
      (4:ℂ)*sourcePair f (secondJet A h)+
      sourcePair (SourceScalarPositiveBulkWard.Gauge f) (secondJet A h)+
      sourcePair f (secondJet A (SourceScalarPositiveBulkWard.Gauge h)) := by
  have he:InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge A=
      (4:ℂ) • secondJet A-deltaGauge (secondJet A) := by
    unfold InverseVolumeWardAlgebra.mixedPolynomial secondJet
    simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,map_sub,smul_sub]
    module
  have hg:deltaGauge (secondJet A)=SourceScalarPositiveBulkWard.Gauge*secondJet A-
      secondJet A*SourceScalarPositiveBulkWard.Gauge:=SourceGaugeScaleTransport.generator_commutator _ |>.symm
  rw [he,hg]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply]
  have pa(x y:QuantumTest):sourcePair f (x-y)=sourcePair f x-sourcePair f y:=by
    simp only [sourcePair,map_sub,inner_sub_right]
  have ps(c:ℂ)(x:QuantumTest):sourcePair f (c • x)=c*sourcePair f x:=by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [pa,ps,pa,(paid_shifted_response% gauge_pair)]
  ring

private theorem native_cov_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    (causalFrequency advanced μ w).im≠0:=by
  cases advanced <;> simpa [causalFrequency,SourceResolventBandLimit.line_im] using hμ.ne'

private theorem cov_pair_continuous(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(f h:QuantumTest):
    Continuous (fun w:ℝ=>sourcePair f (secondJet (coreCovariance m ell F (causalFrequency advanced μ w)
      (native_cov_nonreal advanced μ hμ w)) h)) := by
  let p(a b:QuantumTest)(w:ℝ):ℂ:=inner ℂ (window m ell F (causalFrequency advanced μ w) a)
    (window m ell F (causalFrequency advanced μ w) b)
  have hp(a b:QuantumTest):Continuous (p a b):=
    ((paid_covariance_window% window_continuous) advanced μ hμ m ell F a).inner (𝕜:=ℂ)
      ((paid_covariance_window% window_continuous) advanced μ hμ m ell F b)
  simp_rw [actual_covariance_six_pair_source]
  change Continuous (fun w:ℝ=>-p (relativeGenerator f) h w-p f (relativeGenerator h) w-
    p (relativeGenerator (SourceScalarPositiveBulkWard.Gauge f)) h w-
    p (relativeGenerator f) (SourceScalarPositiveBulkWard.Gauge h) w-
    p (SourceScalarPositiveBulkWard.Gauge f) (relativeGenerator h) w-
    p f (relativeGenerator (SourceScalarPositiveBulkWard.Gauge h)) w)
  exact (((((hp _ _).neg.sub (hp _ _)).sub (hp _ _)).sub (hp _ _)).sub (hp _ _)).sub (hp _ _)

/-- Gauge is returned to two genuine fixed source inputs. The whole remaining
mixed covariance therefore receives a complex norm-L1 payment internally,
with one N before both causes and the moving compression. -/
theorem actual_native_mixed_covariance_pair_tail(μ:ℝ)(hμ:0<μ)(f h:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal ‖sourcePair f
        (InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge
          (coreCovariance m ell F (causalFrequency advanced μ w)
            (native_cov_nonreal advanced μ hμ w)) h)‖) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N0,h0⟩:=actual_covariance_pair_causal_tail μ hμ f h (ε/6) (by positivity)
  obtain ⟨N1,h1⟩:=actual_covariance_pair_causal_tail μ hμ (SourceScalarPositiveBulkWard.Gauge f) h (ε/6) (by positivity)
  obtain ⟨N2,h2⟩:=actual_covariance_pair_causal_tail μ hμ f (SourceScalarPositiveBulkWard.Gauge h) (ε/6) (by positivity)
  refine ⟨max (max N0 N1) N2,fun m hm ell hml=>?_⟩
  filter_upwards [h0 m (by omega) ell hml,h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hF0 hF1 hF2
  intro advanced
  let p(a b:QuantumTest)(w:ℝ):ℂ:=sourcePair a (secondJet
    (coreCovariance m ell F (causalFrequency advanced μ w) (native_cov_nonreal advanced μ hμ w)) b)
  have hp(a b:QuantumTest):Measurable (fun w:ℝ=>ENNReal.ofReal ‖p a b w‖):=
    ENNReal.measurable_ofReal.comp (cov_pair_continuous advanced μ hμ m ell F a b).norm.measurable
  have hn(a b c:ℂ):‖(4:ℂ)*a+b+c‖ ≤ 4*‖a‖+‖b‖+‖c‖ := by
    have ht:=(norm_add_le ((4:ℂ)*a) b).trans_eq (by rw [norm_mul,Complex.norm_ofNat])
    exact (norm_add_le _ c).trans (add_le_add ht (le_refl ‖c‖))
  simp_rw [actual_mixed_pair]
  have hi:=lintegral_mono (μ:=volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (hn (p f h w) (p (SourceScalarPositiveBulkWard.Gauge f) h w) (p f (SourceScalarPositiveBulkWard.Gauge h) w)))
  apply hi.trans
  have ho(w:ℝ):ENNReal.ofReal (4*‖p f h w‖+‖p (SourceScalarPositiveBulkWard.Gauge f) h w‖+
      ‖p f (SourceScalarPositiveBulkWard.Gauge h) w‖)=
      ENNReal.ofReal 4*ENNReal.ofReal ‖p f h w‖+
      ENNReal.ofReal ‖p (SourceScalarPositiveBulkWard.Gauge f) h w‖+
      ENNReal.ofReal ‖p f (SourceScalarPositiveBulkWard.Gauge h) w‖ := by
    rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _),
      ENNReal.ofReal_add (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  simp_rw [ho]
  rw [lintegral_add_right _ (hp _ _),lintegral_add_right _ (hp _ _),
    lintegral_const_mul (ENNReal.ofReal 4) (hp _ _)]
  have hm0:ENNReal.ofReal 4*(∫⁻w:ℝ,ENNReal.ofReal ‖p f h w‖) ≤ ENNReal.ofReal 4*ENNReal.ofReal (ε/6):=by
    gcongr
    exact hF0 advanced
  have hbound:=add_le_add (add_le_add hm0 (hF1 advanced)) (hF2 advanced)
  apply hbound.trans_eq
  rw [←ENNReal.ofReal_mul (by norm_num: (0:ℝ) ≤ 4),←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end LowEnergy.ActualNativeOwnSquareWardPayment
