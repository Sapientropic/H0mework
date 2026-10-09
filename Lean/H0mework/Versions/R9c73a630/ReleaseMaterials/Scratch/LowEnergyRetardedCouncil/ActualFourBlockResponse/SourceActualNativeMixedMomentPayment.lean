import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualShiftedQuadraticWardPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCompensatedQuadraticWardMoment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualNativeOwnSquareWardPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualNativeMixedMomentPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale ActualMixedCovarianceTail ActualMixedWindowGram
open SourcePhysicalKineticSquare SourceScalarInverseBulk ActualScalarPhaseJet SourceCoframeVolumeCurrent
open Lean Meta Elab Term
open SourceNativeCutoffContact SourceClockPhiSecondBulk ActualPhaseBulkSquare
open ActualShiftedQuadraticWardPayment ActualScalarPhaseFrequencyReturn
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair compressionCore resolventCore coreWindow phaseHamiltonianSquare


elab "paid_mixed_square%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseBulkSquare 0) "LowEnergy") "ActualPhaseBulkSquare"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem second_inverse_right(A:End):
    secondJet (A*inverseVolumeAction)=secondJet A*inverseVolumeAction := by
  unfold secondJet
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    (paid_mixed_square% phi_product),(paid_mixed_square% gauge_product),
    inverse_phi,inverse_gauge,mul_zero,add_zero,map_sub,sub_mul]

private theorem second_inverse_left(A:End):
    secondJet (inverseVolumeAction*A)=inverseVolumeAction*secondJet A := by
  unfold secondJet
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    (paid_mixed_square% phi_product),(paid_mixed_square% gauge_product),
    inverse_phi,inverse_gauge,zero_mul,zero_add,map_sub,mul_sub]

private theorem force_square_second:
    secondJet (phaseForce*phaseForce)=(-2:ℂ) • (phaseForce*phaseForce) := by
  obtain ⟨hp,hg,_⟩:=actual_source_phase_force_weights
  unfold secondJet
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    (paid_mixed_square% phi_product),(paid_mixed_square% gauge_product),hp,hg,
    zero_mul,mul_zero,add_zero,sub_zero,neg_mul,mul_neg,map_add,map_neg]
  module

/-- The lower-order field retains the native second pressure, including its
positive magnetic sector, before the final Gauge polynomial is applied. -/
theorem actual_native_phase_second_pressure:
    secondJet phaseHamiltonianSquare=
      (-(phaseCoefficient:ℂ)) •
        (secondJet diagonalAction*inverseVolumeAction+inverseVolumeAction*secondJet diagonalAction)-
      (4:ℂ) • (phaseForce*phaseForce) := by
  rw [actual_source_phase_square]
  simp only [map_add,map_smul,second_inverse_right,second_inverse_left,force_square_second,smul_smul]
  module

private theorem gauge_inverse(F:Index)(z:ℂ)(hz:z.im≠0):
    Gauge*resolventCore F z hz-resolventCore F z hz*Gauge=
      -resolventCore F z hz*deltaGauge (compressionCore F)*resolventCore F z hz := by
  have h:=(paid_phase_inverse% inverse_comm) (compressionCore F-z • (1:End))
    (resolventCore F z hz) Gauge
    ((paid_phase_inverse% actual_inverse) F z hz).1
    ((paid_phase_inverse% actual_inverse) F z hz).2
  have hg:Gauge*compressionCore F-compressionCore F*Gauge=deltaGauge (compressionCore F):=
    SourceGaugeScaleTransport.generator_commutator _
  rw [(paid_phase_inverse% comm_spectral)] at h
  change Gauge*resolventCore F z hz-resolventCore F z hz*Gauge=
    -resolventCore F z hz*(Gauge*compressionCore F-compressionCore F*Gauge)*resolventCore F z hz at h
  simpa only [hg] using h

private theorem gauge_current_algebra(C R G S:End)
    (hR:G*R-R*G= -R*(G*C-C*G)*R):
    R*(C*(G*S-S*G)-(G*S-S*G)*C)*R=
      G*(R*(C*S-S*C)*R)-(R*(C*S-S*C)*R)*G+
      R*(G*C-C*G)*(R*(C*S-S*C)*R)+
      (R*(C*S-S*C)*R)*(G*C-C*G)*R-
      R*((G*C-C*G)*S-S*(G*C-C*G))*R := by
  have hl:=congrArg (fun A:End=>A*(C*S-S*C)*R) hR
  have hr:=congrArg (fun A:End=>R*(C*S-S*C)*A) hR
  linear_combination (norm := noncomm_ring) -hl-hr

private theorem pair_add_left(a b h:QuantumTest):sourcePair (a+b) h=sourcePair a h+sourcePair b h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_left(a b h:QuantumTest):sourcePair (a-b) h=sourcePair a h-sourcePair b h := by
  simp only [sourcePair,map_sub,inner_sub_left]

/-- Gauge is lowered on the complete native insertion. The four forcing
orders contain the genuine compressed Gauge jet, including its raw-P defect. -/
theorem actual_gauge_current_return(S:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest):
    let R:=resolventCore F z hz
    let C:=compressionCore F
    let W:=coreWindow m ell F z hz
    let Gamma:=deltaGauge C
    let T:=R*(C*S-S*C)*R
    sourcePair (W g) (thetaAction m ell
      ((R*(C*(((4:ℂ) • S-deltaGauge S))-
        (((4:ℂ) • S-deltaGauge S))*C)*R) h))=
      (4:ℂ)*sourcePair (W g) (thetaAction m ell (T h))+
      sourcePair (W (Gauge g)) (thetaAction m ell (T h))+
      sourcePair (W g) (thetaAction m ell (T (Gauge h)))-
      sourcePair (thetaAction m ell ((R*Gamma*R) g)) (thetaAction m ell (T h))-
      sourcePair (W g) (thetaAction m ell ((R*Gamma*T) h))-
      sourcePair (W g) (thetaAction m ell ((T*Gamma*R) h))+
      sourcePair (W g) (thetaAction m ell ((R*(Gamma*S-S*Gamma)*R) h)) := by
  dsimp only
  let R:=resolventCore F z hz
  let C:=compressionCore F
  let T:=R*(C*S-S*C)*R
  have hg(A:End):Gauge*A-A*Gauge=deltaGauge A:=SourceGaugeScaleTransport.generator_commutator A
  have hR:Gauge*R-R*Gauge= -R*(Gauge*C-C*Gauge)*R:=by
    rw [hg C]
    exact gauge_inverse F z hz
  have ha:=gauge_current_algebra C R Gauge S hR
  rw [hg S,hg C] at ha
  have ht:Gauge*thetaAction m ell-thetaAction m ell*Gauge=0 := by
    rw [SourceGaugeScaleTransport.generator_commutator]
    exact ActualAffineCutoffCausalTail.actual_gauge_cutoff_zero m ell
  have hc:Gauge*thetaAction m ell=thetaAction m ell*Gauge:=sub_eq_zero.mp ht
  have hw:=LinearMap.congr_fun (actual_gauge_window_splice m ell F z hz) g
  simp only [Module.End.mul_apply,LinearMap.sub_apply] at hw
  have hmR:R*(C*(((4:ℂ) • S-deltaGauge S))-
      (((4:ℂ) • S-deltaGauge S))*C)*R=
      (4:ℂ) • T-R*(C*deltaGauge S-deltaGauge S*C)*R := by
    dsimp only [T]
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    module
  rw [hmR,ha]
  have hs:sourcePair (coreWindow m ell F z hz g) (thetaAction m ell (Gauge (T h)))=
      -sourcePair (Gauge (coreWindow m ell F z hz g)) (thetaAction m ell (T h)) := by
    rw [←Module.End.mul_apply,←hc]
    simp only [Module.End.mul_apply]
    exact (paid_shifted_response% gauge_pair) _ _
  change sourcePair (coreWindow m ell F z hz g)
    (thetaAction m ell ((Gauge*(R*(C*S-S*C)*R)) h))=
    -sourcePair (Gauge (coreWindow m ell F z hz g))
      (thetaAction m ell ((R*(C*S-S*C)*R) h)) at hs
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,
    map_sub,map_add,map_smul,(paid_phase_frequency% pair_add_right),
    (paid_phase_frequency% pair_sub_right),(paid_phase_frequency% pair_smul_right)]
  rw [hs,hw,pair_sub_left]
  dsimp only [T,R,C]
  simp only [Module.End.mul_apply,LinearMap.sub_apply,map_sub,
    (paid_phase_frequency% pair_sub_right)]
  ring



/-- The actual phase-square field consumes the complete Gauge return. -/
theorem actual_native_mixed_gauge_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest):
    let R:=resolventCore F z hz
    let C:=compressionCore F
    let W:=coreWindow m ell F z hz
    let S:=secondJet phaseHamiltonianSquare
    let Gamma:=deltaGauge C
    let T:=R*(C*S-S*C)*R
    sourcePair (W g) (thetaAction m ell
      ((R*(C*(InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge phaseHamiltonianSquare)-
        (InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge phaseHamiltonianSquare)*C)*R) h))=
      (4:ℂ)*sourcePair (W g) (thetaAction m ell (T h))+
      sourcePair (W (Gauge g)) (thetaAction m ell (T h))+
      sourcePair (W g) (thetaAction m ell (T (Gauge h)))-
      sourcePair (thetaAction m ell ((R*Gamma*R) g)) (thetaAction m ell (T h))-
      sourcePair (W g) (thetaAction m ell ((R*Gamma*T) h))-
      sourcePair (W g) (thetaAction m ell ((T*Gamma*R) h))+
      sourcePair (W g) (thetaAction m ell ((R*(Gamma*S-S*Gamma)*R) h)) := by
  have hm:InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge phaseHamiltonianSquare=
      (4:ℂ) • secondJet phaseHamiltonianSquare-deltaGauge (secondJet phaseHamiltonianSquare) := by
    exact ActualNativeOwnSquareWardPayment.actual_remaining_mixed_second
  dsimp only
  rw [hm]
  exact actual_gauge_current_return (secondJet phaseHamiltonianSquare) m ell F z hz g h


/-- Same-F bilinear lower current, before the final Gauge polynomial. -/
def nativeSecondFlux(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  let C:=compressionCore F
  let S:=secondJet phaseHamiltonianSquare
  sourcePair (coreWindow m ell F z hz f) (thetaAction m ell ((R*(C*S-S*C)*R) h))

/-- The four source forcing orders are one signed responsibility. -/
def nativeGaugeForcing(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  let C:=compressionCore F
  let W:=coreWindow m ell F z hz
  let S:=secondJet phaseHamiltonianSquare
  let Gamma:=deltaGauge C
  let T:=R*(C*S-S*C)*R
  (0:ℂ)-sourcePair (thetaAction m ell ((R*Gamma*R) f)) (thetaAction m ell (T h))-
    sourcePair (W f) (thetaAction m ell ((R*Gamma*T) h))-
    sourcePair (W f) (thetaAction m ell ((T*Gamma*R) h))+
    sourcePair (W f) (thetaAction m ell ((R*(Gamma*S-S*Gamma)*R) h))

/-- The exact native-plus-Own consumer of the bilinear Gauge return. -/
theorem actual_native_own_gauge_forcing(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F z hz g=
      (4:ℂ)*nativeSecondFlux m ell F z hz g g+
      nativeSecondFlux m ell F z hz (Gauge g) g+
      nativeSecondFlux m ell F z hz g (Gauge g)+nativeGaugeForcing m ell F z hz g g := by
  rw [ActualNativeOwnSquareWardPayment.actual_native_own_mixed_flux]
  unfold ActualNativeOwnSquareWardPayment.mixedSquareField nativeSecondFlux nativeGaugeForcing
  dsimp only
  have h:=actual_native_mixed_gauge_return m ell F z hz g g
  dsimp only at h
  linear_combination h

end LowEnergy.ActualNativeMixedMomentPayment
