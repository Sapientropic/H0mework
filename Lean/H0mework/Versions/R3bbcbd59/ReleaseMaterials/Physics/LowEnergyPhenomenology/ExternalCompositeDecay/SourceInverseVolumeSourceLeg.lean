import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeDiagonalEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.SourceInverseSourceLeg
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourcePhysicalKineticSquare
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarInverseNativeEnergy
open SourceScalarInverseEnergyExchange SourceInverseDiagonalEndpoint SourceScalarInverseEndpoint
open SourceMixedNativeReturn SourceGammaNativeBudget SourceMovingJetFlux SourceClosedCostNativeProbe
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceRelativePowerTail
open SourceHardyRetardedTail SourceRetardedBandCurrent MeasureTheory Filter
open scoped InnerProductSpace ENNReal
attribute [local irreducible] GaussDiagonalHistory.diagonalAction SourceScalarPositiveBulkWard.state
  SourceGammaNativeBudget.sourceGamma SourceMixedNativeReturn.sourceRead
  SourceMixedNativeReturn.primitive SourceMixedNativeReturn.scalarAction
  SourceMixedNativeReturn.thetaAction SourceScalarInverseEnergyExchange.signedPair
  SourceScalarInverseNativeEnergy.coefficientCost SourceScalarVirialBulk.vacuumJetCoefficient

private theorem resolvent_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (k f : E) :
    inner ℂ k (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k) f := by
  have hk := congrArg (fun A : E →L[ℂ] E => A k) (resolvent_right C hC (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz))
  have hf := congrArg (fun A : E →L[ℂ] E => A f) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
    star z • FullYSourceResolventGraphSplice.resolvent C (star z) k=k at hk
  change C (FullYSourceResolventGraphSplice.resolvent C z f)-
    z • FullYSourceResolventGraphSplice.resolvent C z f=f at hf
  have hs : inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k))
      (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f)) := hC.isSymmetric _ _
  calc
    _ = inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
      star z • FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (FullYSourceResolventGraphSplice.resolvent C z f) := congrArg (fun x => inner ℂ x _) hk.symm
    _ = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (C (FullYSourceResolventGraphSplice.resolvent C z f)-z • FullYSourceResolventGraphSplice.resolvent C z f) := by
      rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,hs,
        starRingEnd_apply,star_star]
    _ = _ := congrArg (fun x => inner ℂ _ x) hf


private theorem finite_pair (F : Index) (z : ℂ) (hz : z.im≠0) (k f : H) :
    inner ℂ k (finiteResolvent F z f)=inner ℂ (finiteResolvent F (star z) k) f :=
  resolvent_pair _ (GaussGradedCompression.compression_selfAdjoint F) z hz k f

/-- The actual exterior source legs share their norm, including the escape component. -/
theorem actual_conjugate_leg_norm (F : Index) (z : ℂ) (hz : z.im≠0) (k : H) :
    ‖finiteResolvent F (star z) k‖=‖finiteResolvent F z k‖ := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hc : Commute (GaussGradedCompression.compression F-z • 1)
      (GaussGradedCompression.compression F-star z • 1) := by
    show (GaussGradedCompression.compression F-z • 1)*(GaussGradedCompression.compression F-star z • 1)=
      (GaussGradedCompression.compression F-star z • 1)*(GaussGradedCompression.compression F-z • 1)
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
    module
  have hr := hc.ringInverse_ringInverse.eq
  change finiteResolvent F z*finiteResolvent F (star z)=
    finiteResolvent F (star z)*finiteResolvent F z at hr
  have h1 := finite_pair F z hz k
    (finiteResolvent F (star z) k)
  have h2 := finite_pair F (star z) hs k
    (finiteResolvent F z k)
  simp only [star_star] at h2
  have he := congrArg (fun A : H →L[ℂ] H => inner ℂ k (A k)) hr
  change inner ℂ k (finiteResolvent F z (finiteResolvent F (star z) k))=
    inner ℂ k (finiteResolvent F (star z) (finiteResolvent F z k)) at he
  rw [h1,h2] at he
  have hn : ‖finiteResolvent F (star z) k‖^2=‖finiteResolvent F z k‖^2 := by
    simpa only [inner_self_eq_norm_sq] using congrArg (fun c : ℂ => RCLike.re c) he
  nlinarith [norm_nonneg (finiteResolvent F (star z) k),norm_nonneg (finiteResolvent F z k)]

/-- Gamma plus its genuine moving current retains the actual exterior resolvent state. -/
theorem actual_gamma_source_leg_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    4*sourceTime 0*‖sourceGamma sharp m ell F g k z+Complex.I*inner ℂ (k : H)
      ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
        orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))‖^2 ≤
      ‖-96*(sourceTime 0 : ℂ)^2‖^2*‖finiteResolvent F (star z) (k : H)‖^2*coefficientCost sharp*
        ((signedPair sharp m ell (state F z hz g) (state F z hz g)).re+
          2*sourceTime 0*‖vacuum‖^2*‖embed (theta m ell (state F z hz g))‖^2) := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  let p := state F (star z) hs k
  let q := state F z hz g
  have hp : embed p=finiteResolvent F (star z) (k : H) := by
    dsimp only [p]
    unfold state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have h := original_paired_scalar_inverse_bound sharp m ell p q
  have hr := gamma_source_return sharp m ell F g k z hz
  rw [finite_pair F z hz,←hp] at hr
  have hq : coreEquiv.symm (SourceEscapeCurrent.sourceCore F z hz g)=q := by
    change coreEquiv.symm (SourceEscapeCurrent.sourceCore F z hz g)=state F z hz g
    unfold state
    rfl
  rw [hq] at hr
  have he : sourceGamma sharp m ell F g k z+Complex.I*inner ℂ (k : H)
      ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
        orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))=
      (-96*(sourceTime 0 : ℂ)^2)*sourcePair p (scalarAction sharp (thetaAction m ell q)) := by
    simp only [sourcePair]
    rw [hr]
    ring
  rw [he,norm_mul,mul_pow,original_diagonal_energy_exchange]
  rw [hp] at h
  have ht : theta m ell=thetaAction m ell := by
    simp only [theta,SourceNativeCutoffContact.theta_action_polynomial,SourceMixedNativeReturn.thetaAction]
  have ht2 : SourceScalarInverseRetardedBudget.theta m ell=thetaAction m ell := ht
  rw [ht,ht2]
  change _ ≤ ‖-96*(sourceTime 0 : ℂ)^2‖^2*‖finiteResolvent F (star z) (k : H)‖^2*coefficientCost sharp*
    (inverseForm (thetaAction m ell q)+2*sourceTime 0*‖vacuum‖^2*‖embed (thetaAction m ell q)‖^2)
  nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg ‖-96*(sourceTime 0 : ℂ)^2‖)]

end LowEnergy.SourceInverseSourceLeg
