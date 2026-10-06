import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeDefectCurrentPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseDefectCurrentResponse
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussQuantumMultiplier
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceMixedNativeReturn
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceInverseProjectionCurrentRemainder
open SourceInverseDefectCurrentPair FullYSourceResolventGraphSplice Filter
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction state sourcePair sourceRead
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction
  GaussAdjointHistory.coreStep GaussAdjointHistory.iterate matterInsertion singleDefect

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.fullAction sharp g)=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) f) g := by
  unfold SourceMixedNativeReturn.fullAction
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.thetaAction m ell g)=
      sourcePair (SourceMixedNativeReturn.thetaAction m ell f) g := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact GaussNativeForm.multiply_pair _ _ _ _

private theorem theta_full (sharp : Bool) (m ell : ℕ) :
    Commute (SourceMixedNativeReturn.thetaAction m ell) (SourceMixedNativeReturn.fullAction sharp) := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField z))
      (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z))
      (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)).symm

private theorem insertion_pair (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (SourceScalarDoubleCurrent.fullInsertion sharp m ell g)=
      sourcePair (SourceScalarDoubleCurrent.fullInsertion (!sharp) m ell f) g := by
  unfold SourceScalarDoubleCurrent.fullInsertion
  change sourcePair f (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell g))=_
  rw [full_pair,theta_pair]
  exact congrArg (fun v => sourcePair v g) (LinearMap.congr_fun (theta_full (!sharp) m ell).eq f)

/-- Both source branches of the original Hamiltonian insertion have the required independent dual. -/
theorem original_hamiltonian_insertion_pair (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell) g)=
      -sourcePair (bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion (!sharp) m ell) f) g := by
  have hr (a b c : QuantumTest) : sourcePair a (b-c)=sourcePair a b-sourcePair a c := by
    simp only [sourcePair,map_sub,inner_sub_right]
  have hl (a b c : QuantumTest) : sourcePair (a-b) c=sourcePair a c-sourcePair b c := by
    simp only [sourcePair,map_sub,inner_sub_left]
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,hr,hl]
  rw [diagonalAction_pair,insertion_pair,insertion_pair,diagonalAction_pair]
  ring

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


private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

theorem actual_read_pair (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) (A : End) :
    inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g A*finiteResolvent F z) (g : H))=
      sourcePair (state F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k) (A (state F z hz g)) := by
  have hread : sourceRead F g A (finiteResolvent F z (g : H))=embed (A (state F z hz g)) := by
    unfold state
    exact source_read_resolvent F g A z hz
  have hr := congrArg (fun v : H => inner ℂ (k : H) (finiteResolvent F z v)) hread
  have hp := finite_pair F z hz (k : H) (embed (A (state F z hz g)))
  have he : inner ℂ (finiteResolvent F (star z) (k : H)) (embed (A (state F z hz g)))=
      sourcePair (state F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k) (A (state F z hz g)) := by
    unfold sourcePair
    rw [state_embed]
  exact hr.trans (hp.trans he)

/-- The original reader is evaluated at each actual source jet, so both ends still use their own generated input span. -/
theorem actual_response_descent (A B : End)
    (hAB : ∀ f g,sourcePair f (A g)= -sourcePair (B f) g)
    (r s : ℕ) (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (z : ℂ),z.im≠0 →
      z^(r+s)*inner ℂ (k : H)
        ((finiteResolvent F z*sourceRead F g (bracket (defectAction F) A)*finiteResolvent F z) (g : H))=
      inner ℂ (GaussAdjointHistory.iterate s k : H)
        ((finiteResolvent F z*sourceRead F (GaussAdjointHistory.iterate r g)
          (bracket (defectAction F) A)*finiteResolvent F z) (GaussAdjointHistory.iterate r g : H)) := by
  filter_upwards [actual_retarded_pair_descent A B hAB r s g k] with F hF z hz
  rw [actual_read_pair F z hz,actual_read_pair F z hz]
  exact hF z hz

/-- The complete [d_F,W] response, including the independent sharp branch, consumes the double source descent. -/
theorem actual_matter_response_descent (m ell r s : ℕ) (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (sharp : Bool) (z : ℂ),z.im≠0 →
      z^(r+s)*inner ℂ (k : H)
        ((finiteResolvent F z*sourceRead F g (bracket (defectAction F) (matterInsertion sharp m ell))*
          finiteResolvent F z) (g : H))=
      inner ℂ (GaussAdjointHistory.iterate s k : H)
        ((finiteResolvent F z*sourceRead F (GaussAdjointHistory.iterate r g)
          (bracket (defectAction F) (matterInsertion sharp m ell))*finiteResolvent F z)
            (GaussAdjointHistory.iterate r g : H)) := by
  exact Filter.eventually_all.mpr (fun sharp => actual_response_descent
    (matterInsertion sharp m ell) (matterInsertion (!sharp) m ell)
    (original_matter_insertion_pair sharp m ell) r s g k)

/-- The original three-word projection flux now has an exact two-leg descent to its one-defect terminal. -/
theorem actual_projection_flux_descent (m ell r s : ℕ) (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (sharp : Bool) (z : ℂ),z.im≠0 →
      z^(r+s)*inner ℂ (k : H)
        ((finiteResolvent F z*doubleProjectionFlux sharp m ell F g*finiteResolvent F z) (g : H))=
      inner ℂ (GaussAdjointHistory.iterate s k : H)
        ((finiteResolvent F z*sourceRead F (GaussAdjointHistory.iterate r g)
          (singleDefect sharp m ell F)*finiteResolvent F z) (GaussAdjointHistory.iterate r g : H)) := by
  have hd (sharp : Bool) := actual_response_descent
    (bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell))
    (bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion (!sharp) m ell))
    (original_hamiltonian_insertion_pair sharp m ell) r s g k
  filter_upwards [actual_projection_single_defect m ell g k,Filter.eventually_all.mpr hd] with F hp hD sharp z hz
  rw [hp sharp z hz]
  simpa only [singleDefect] using! hD sharp z hz

end LowEnergy.SourceInverseDefectCurrentResponse
