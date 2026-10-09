import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWindowGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedContactReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeMatter
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk GaussCoframeForm
open SourceResolventBandLimit FullYSourceResolventGraphSplice ActualMixedCovarianceTail ActualMixedWindowGram
open SourceScalarAffineCutoffTail ActualAffineCutoffCausalTail SourceNativeCutoffContact
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem theta_pair(m ell:ℕ) : Paired (thetaAction m ell) (thetaAction m ell) :=
  fun f g=>multiply_pair _ _ f g
private theorem affine_pair(m ell:ℕ) : Paired (affineCutoff m ell) (affineCutoff m ell) :=
  (paid_mixed_gram% paired_phi) _ _ (theta_pair m ell)

private theorem actual_theta_affine_commute(m ell:ℕ) : Commute (thetaAction m ell) (affineCutoff m ell) := by
  change thetaAction m ell*affineCutoff m ell=affineCutoff m ell*thetaAction m ell
  rw [actual_affine_cutoff_return]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (theta m ell z:ℂ) • ((eulerCoefficient m ell z:ℂ) • f z+
    Complex.I • contactFiber ((SourceQuantumScalarChart.vacuum:SourceQuantumScalarChart.Scalar),0) m ell z (f z))=
      (eulerCoefficient m ell z:ℂ) • ((theta m ell z:ℂ) • f z)+
      Complex.I • contactFiber ((SourceQuantumScalarChart.vacuum:SourceQuantumScalarChart.Scalar),0) m ell z
        ((theta m ell z:ℂ) • f z)
  rw [smul_add,map_smul,smul_comm (theta m ell z:ℂ) (eulerCoefficient m ell z:ℂ),
    smul_comm (theta m ell z:ℂ) Complex.I]

private theorem gauge_theta(m ell:ℕ)(f:QuantumTest) : Gauge (thetaAction m ell f)=thetaAction m ell (Gauge f) := by
  have h:=actual_gauge_cutoff_zero m ell
  rw [←SourceGaugeScaleTransport.generator_commutator] at h
  exact LinearMap.congr_fun (sub_eq_zero.mp h) f
private theorem gauge_affine(m ell:ℕ)(f:QuantumTest) : Gauge (affineCutoff m ell f)=affineCutoff m ell (Gauge f) := by
  have h:=actual_gauge_affine_cutoff_zero m ell
  rw [←SourceGaugeScaleTransport.generator_commutator] at h
  exact LinearMap.congr_fun (sub_eq_zero.mp h) f

/-- The moving gauge derivative cancels only in the complete real source pairing.
The affine cutoff includes its original vacuum contact. -/
theorem actual_gauge_contact_pair_zero(m ell:ℕ)(q:QuantumTest) :
    (sourcePair (thetaAction m ell q) (affineCutoff m ell (Gauge q))).re=0 := by
  have hc (f:QuantumTest) : thetaAction m ell (affineCutoff m ell f)=
    affineCutoff m ell (thetaAction m ell f) := LinearMap.congr_fun (actual_theta_affine_commute m ell).eq f
  have h:sourcePair (thetaAction m ell q) (affineCutoff m ell (Gauge q))=
      -star (sourcePair (thetaAction m ell q) (affineCutoff m ell (Gauge q))) := by
    conv_lhs => rw [affine_pair m ell,(paid_mixed_gram% gauge_skew),gauge_affine,gauge_theta,←hc,
      ←theta_pair m ell]
    exact congrArg Neg.neg (GaussNativeForm.pair_conjugate _ _).symm
  have hr:=congrArg Complex.re h
  simp only [Complex.neg_re,Complex.star_def,Complex.conj_re] at hr
  linarith only [hr]

/-- The source contact on δGauge R has a fixed-source Gauge g return. No moving-input
contact estimate is assumed or inferred from a fixed-input tail. -/
theorem actual_moving_contact_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest) :
    (sourcePair (coreWindow m ell F z hz g)
      (affineCutoff m ell (deltaGauge (resolventCore F z hz) g))).re=
      -(sourcePair (coreWindow m ell F z hz g)
        (affineCutoff m ell (resolventCore F z hz (Gauge g)))).re := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,sourcePair,inner_sub_right,Complex.sub_re]
  have h:=actual_gauge_contact_pair_zero m ell (resolventCore F z hz g)
  change (sourcePair (coreWindow m ell F z hz g) (affineCutoff m ell (Gauge (resolventCore F z hz g)))).re=0 at h
  change _= _ at h
  simpa only [sourcePair,h,zero_sub] using congrArg
    (fun x:ℝ=>x-(sourcePair (coreWindow m ell F z hz g)
      (affineCutoff m ell (resolventCore F z hz (Gauge g)))).re) h

end LowEnergy.ActualMixedContactReturn
