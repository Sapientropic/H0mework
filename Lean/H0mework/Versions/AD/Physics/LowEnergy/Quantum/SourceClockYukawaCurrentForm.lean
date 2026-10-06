import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaCurrentForm
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceScalarPairedTransport
open SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent SourceClockYukawaHamiltonianCurrent
open FullYSourceResolventGraphSplice SourceRelativePowerTail SourceClockYukawaCurrent
open SourceQuantumConfigurationHilbert
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction state

private theorem full_pair (sharp : Bool) (p q : QuantumTest) :
    sourcePair p (SourceMixedNativeReturn.fullAction sharp q)=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) p) q := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair q p)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair p q

private theorem pair_sub_left (a b c : QuantumTest) :
    sourcePair (a-b) c=sourcePair a c-sourcePair b c := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_right (a b c : QuantumTest) :
    sourcePair a (b-c)=sourcePair a b-sourcePair a c := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_add_right (a b c : QuantumTest) :
    sourcePair a (b+c)=sourcePair a b+sourcePair a c := by
  simp only [sourcePair,map_add,inner_add_right]

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
  simp only [sourcePair,compression_embed]
  exact ((GaussGradedCompression.compression_selfAdjoint F).isSymmetric _ _).symm

private theorem compression_current_dual (sharp : Bool) (F : Index) (p q : QuantumTest) :
    sourcePair (bracket (compressionCore F) (SourceMixedNativeReturn.fullAction (!sharp)) p) q=
      -sourcePair p (bracket (compressionCore F) (SourceMixedNativeReturn.fullAction sharp) q) := by
  have h1 := (compression_pair F (SourceMixedNativeReturn.fullAction (!sharp) p) q).symm.trans
    (full_pair sharp p (compressionCore F q)).symm
  have h2 := (full_pair sharp (compressionCore F p) q).symm.trans
    (compression_pair F p (SourceMixedNativeReturn.fullAction sharp q)).symm
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_left,pair_sub_right]
  rw [h1,h2]
  ring

/-- One signed source word retains all native scalar, matter, spin and compression fields. -/
def nativeCurrentPair (sharp : Bool) (F : Index) (p q : QuantumTest) : ℂ :=
  sourcePair p (bracket matterAction (SourceMixedNativeReturn.fullAction sharp) q)+
    scalarCurrentPair sharp p q+sourcePair p (reducedSpinCurrent sharp q)-
    sourcePair p (bracket (defectAction F) (SourceMixedNativeReturn.fullAction sharp) q)

theorem original_corrected_native_form (sharp : Bool) (F : Index) (p q : QuantumTest) :
    sourcePair p (SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F q)=
      nativeCurrentPair sharp F p q := by
  unfold SourceClockYukawaHamiltonianCurrent.correctedCurrent originalCurrent nativeCurrentPair
  simp only [LinearMap.sub_apply,LinearMap.add_apply,pair_sub_right,pair_add_right,
    original_scalar_current_pair]

theorem original_corrected_native_dual (sharp : Bool) (F : Index) (p q : QuantumTest) :
    sourcePair (SourceClockYukawaHamiltonianCurrent.correctedCurrent (!sharp) F p) q=
      -nativeCurrentPair sharp F p q := by
  rw [←original_compression_yukawa_current,compression_current_dual,
    original_compression_yukawa_current,original_corrected_native_form]

/-- The theta input is returned through the same actual compression on its source core. -/
def returnedThetaState (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  state F z hz (coreEquiv (thetaAction m ell (state F z hz g)))

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem returned_theta_embed (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    embed (returnedThetaState m ell F z hz g)=
      finiteResolvent F z (relativeTail m ell (finiteResolvent F z (g:H))) := by
  rw [returnedThetaState,state_embed]
  change finiteResolvent F z (embed (thetaAction m ell (state F z hz g)))=_
  rw [←theta_core,state_embed]

private theorem resolvent_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (k f : E) :
    inner ℂ k (FullYSourceResolventGraphSplice.resolvent C z f) =
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k) f := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hk := congrArg (fun A : E →L[ℂ] E => A k) (resolvent_right C hC (star z) hs)
  have hf := congrArg (fun A : E →L[ℂ] E => A f) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C (star z) k) -
    star z • FullYSourceResolventGraphSplice.resolvent C (star z) k = k at hk
  change C (FullYSourceResolventGraphSplice.resolvent C z f) -
    z • FullYSourceResolventGraphSplice.resolvent C z f = f at hf
  have hsym : inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k))
      (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f)) := hC.isSymmetric _ _
  calc
    _ = inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k) -
        star z • FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (FullYSourceResolventGraphSplice.resolvent C z f) := congrArg (fun v => inner ℂ v _) hk.symm
    _ = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f) -
          z • FullYSourceResolventGraphSplice.resolvent C z f) := by
      rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,
        hsym,starRingEnd_apply,star_star]
    _ = _ := congrArg (fun v => inner ℂ _ v) hf

/-- The actual current amplitude is a complete native signed form on the
original advanced input and the returned theta state, with the full defect retained. -/
theorem actual_current_amplitude_native_form (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    currentAmplitude sharp m ell F z hz g k=
      -nativeCurrentPair sharp F
        (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (returnedThetaState m ell F z hz g) := by
  let hs : (star z).im≠0 := by
    simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  unfold currentAmplitude currentResponse
  have hr := resolvent_pair (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) (star z) hs
    (relativeTail m ell (finiteResolvent F z (g:H)))
    (embed (SourceClockYukawaHamiltonianCurrent.correctedCurrent (!sharp) F (state F (star z) hs k)))
  have hc := congrArg (starRingEnd ℂ) hr
  simp only [inner_conj_symm,star_star] at hc
  change inner ℂ
    (finiteResolvent F (star z) (embed
      (SourceClockYukawaHamiltonianCurrent.correctedCurrent (!sharp) F (state F (star z) hs k))))
    (relativeTail m ell (finiteResolvent F z (g:H)))=
      inner ℂ (embed
        (SourceClockYukawaHamiltonianCurrent.correctedCurrent (!sharp) F (state F (star z) hs k)))
        (finiteResolvent F z (relativeTail m ell (finiteResolvent F z (g:H)))) at hc
  change inner ℂ
    (finiteResolvent F (star z) (embed
      (SourceClockYukawaHamiltonianCurrent.correctedCurrent (!sharp) F (state F (star z) hs k))))
    (relativeTail m ell (finiteResolvent F z (g:H)))=_
  rw [hc,←returned_theta_embed]
  exact original_corrected_native_dual sharp F _ _

end LowEnergy.SourceClockYukawaCurrentForm
