import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeFirstCurrentRemainder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseProjectionCurrentRemainder
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets
open SourceInverseFirstCurrentRemainder Filter
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction sourceRead state sourcePair defectAction compressionCore
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction
  doubleProjectionFlux linearRemainder remainingForces linearDefectJet
  matterHamiltonianCurrent inverseCross inputFlux
  cutoffEuler scaleDoubleRemainder constantAction SourceScalarForceBudget.solverOperator
  SourceScalarForceBudget.oscillatorMass wardOperator

/-- This source word has one complete graded defect, acting on the fixed full Hamiltonian current. -/
def singleDefect (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (defectAction F) (bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell))

def projectionCurrent (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (compressionCore F) (bracket (defectAction F) (SourceScalarDoubleCurrent.fullInsertion sharp m ell))

private theorem double_split {R : Type*} [Ring R] (H C X : R) :
    bracket C (bracket (H-C) X)+bracket (H-C) (bracket C X)+bracket (H-C) (bracket (H-C) X)=
      bracket C (bracket (H-C) X)+bracket (H-C) (bracket H X) := by
  unfold bracket
  noncomm_ring

/-- All three original projection words remain the same source occurrence; their two inner terms combine. -/
theorem original_projection_split (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    doubleProjectionFlux sharp m ell F g=
      sourceRead F g (projectionCurrent sharp m ell F+singleDefect sharp m ell F) := by
  unfold doubleProjectionFlux projectionCurrent singleDefect defectAction
  exact congrArg (sourceRead F g) (double_split diagonalAction (compressionCore F)
    (SourceScalarDoubleCurrent.fullInsertion sharp m ell))

attribute [local irreducible] singleDefect projectionCurrent

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_pair (F : Index) (f g : QuantumTest) :
    sourcePair f (compressionCore F g)=sourcePair (compressionCore F f) g := by
  simp only [sourcePair,compression_embed]
  exact ((GaussGradedCompression.compression_selfAdjoint F).isSymmetric _ _).symm

private theorem defect_pair (F : Index) (f g : QuantumTest) :
    sourcePair f (defectAction F g)=sourcePair (defectAction F f) g := by
  unfold defectAction
  simp only [LinearMap.sub_apply,sourcePair,map_sub,inner_sub_left,inner_sub_right]
  simpa only [sourcePair] using!
    congrArg₂ (fun a b : ℂ => a-b) (diagonalAction_pair f g) (compression_pair F f g)

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

private theorem pair_add_left (a b c : QuantumTest) : sourcePair (a+b) c=sourcePair a c+sourcePair b c := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_right (a b c : QuantumTest) : sourcePair a (b+c)=sourcePair a b+sourcePair a c := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_smul_left (c : ℂ) (a b : QuantumTest) : sourcePair (c • a) b=star c*sourcePair a b := by
  simp only [sourcePair,map_smul,inner_smul_left,Complex.star_def]
private theorem pair_smul_right (c : ℂ) (a b : QuantumTest) : sourcePair a (c • b)=c*sourcePair a b := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_sub_left (a b c : QuantumTest) : sourcePair (a-b) c=sourcePair a c-sourcePair b c := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_right (a b c : QuantumTest) : sourcePair a (b-c)=sourcePair a b-sourcePair a c := by
  simp only [sourcePair,map_sub,inner_sub_right]

private theorem bracket_defect_pair (sharp : Bool) (m ell : ℕ) (F : Index) (f g : QuantumTest) :
    sourcePair f (bracket (defectAction F) (SourceScalarDoubleCurrent.fullInsertion sharp m ell) g)=
      -sourcePair (bracket (defectAction F) (SourceScalarDoubleCurrent.fullInsertion (!sharp) m ell) f) g := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_right,pair_sub_left]
  rw [defect_pair,insertion_pair,insertion_pair,defect_pair]
  ring

private theorem eventual_defect_zero (f : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),defectAction F f=0 := by
  filter_upwards [GaussGradedCompression.eventually_exact (coreEquiv f)] with F hF
  apply embed_injective
  simp only [defectAction,LinearMap.sub_apply,map_sub,map_zero,compression_embed]
  have hv : (coreEquiv f : H)=embed f := rfl
  rw [hv] at hF
  rw [hF]
  change embed (diagonalAction f)-embed (diagonalAction (coreEquiv.symm (coreEquiv f)))=0
  rw [coreEquiv.symm_apply_apply,sub_self]

private theorem eventual_bracket_zero (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),
      bracket (defectAction F) (SourceScalarDoubleCurrent.fullInsertion sharp m ell) f=0 := by
  filter_upwards [eventual_defect_zero f,
    eventual_defect_zero (SourceScalarDoubleCurrent.fullInsertion sharp m ell f)] with F hf hX
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,hf,hX,map_zero,sub_self]

private theorem compression_equation (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (state F z hz g)=coreEquiv.symm g+z • state F z hz g := by
  have hh : diagonalAction (state F z hz g)=coreEquiv.symm g+z • state F z hz g+
      defectAction F (state F z hz g) := by
    simpa only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,
      LinearMap.zero_apply,zero_add] using! actual_raised_source F z hz g (1 : End)
  simp only [defectAction,LinearMap.sub_apply] at hh
  linear_combination (norm := module) hh

private theorem compression_current (F : Index) (A : End)
    (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0) (g k : diagonal.domain) :
    sourcePair (state F zl hl k) (bracket (compressionCore F) A (state F zr hr g))=
      sourcePair (coreEquiv.symm k) (A (state F zr hr g))-
      sourcePair (state F zl hl k) (A (coreEquiv.symm g))+
      (star zl-zr)*sourcePair (state F zl hl k) (A (state F zr hr g)) := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_right]
  rw [compression_pair,compression_equation,compression_equation]
  simp only [map_add,map_smul,pair_add_left,pair_add_right,pair_smul_left,pair_smul_right]
  ring

/-- The fixed-input cofinal set preserves both frequencies; only conjugate/nonconjugate legs cancel their coefficient. -/
theorem actual_projection_current_frequencies (m ell : ℕ) (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ (sharp : Bool) (zl zr : ℂ)
      (hl : zl.im≠0) (hr : zr.im≠0),
      sourcePair (state F zl hl k) (projectionCurrent sharp m ell F (state F zr hr g))=
        (star zl-zr)*sourcePair (state F zl hl k)
          (bracket (defectAction F) (SourceScalarDoubleCurrent.fullInsertion sharp m ell) (state F zr hr g)) := by
  have h (sharp : Bool) : ∀ᶠ F in (sourceFilter : Filter Index),
      bracket (defectAction F) (SourceScalarDoubleCurrent.fullInsertion sharp m ell) (coreEquiv.symm g)=0 ∧
      bracket (defectAction F) (SourceScalarDoubleCurrent.fullInsertion (!sharp) m ell) (coreEquiv.symm k)=0 :=
    (eventual_bracket_zero sharp m ell (coreEquiv.symm g)).and
      (eventual_bracket_zero (!sharp) m ell (coreEquiv.symm k))
  filter_upwards [Filter.eventually_all.mpr h] with F hF
  intro sharp zl zr hl hr
  have hc := compression_current F
    (bracket (defectAction F) (SourceScalarDoubleCurrent.fullInsertion sharp m ell)) zl zr hl hr g k
  rw [bracket_defect_pair,(hF sharp).2,(hF sharp).1] at hc
  simp only [sourcePair,map_zero,inner_zero_left,inner_zero_right,neg_zero,sub_zero,zero_add] at hc
  simpa only [projectionCurrent,sourcePair] using! hc

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

private theorem actual_read_pair (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) (A : End) :
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

/-- For each fixed cutoff window, the entire CF-current vanishes on the original cofinal filter, for both branches and all nonreal frequencies. -/
theorem actual_projection_current_zero (m ell : ℕ) (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ (sharp : Bool) (z : ℂ), z.im≠0 →
      inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g (projectionCurrent sharp m ell F)*
        finiteResolvent F z) (g : H))=0 := by
  filter_upwards [actual_projection_current_frequencies m ell g k] with F hF
  intro sharp z hz
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have h := hF sharp (star z) z hs hz
  simp only [star_star,sub_self,zero_mul] at h
  exact (actual_read_pair F z hz g k _).trans h

private theorem pair_sandwich_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r a b : E →L[ℂ] E) (x y : E) :
    inner ℂ y ((r*(a+b)*r) x)=inner ℂ y ((r*a*r) x)+inner ℂ y ((r*b*r) x) := by
  simp only [mul_add,add_mul,add_apply,inner_add_right]

/-- The full original three-term flux now has a single-defect source response; no projection or escape leg was omitted. -/
theorem actual_projection_single_defect (m ell : ℕ) (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ (sharp : Bool) (z : ℂ), z.im≠0 →
      inner ℂ (k : H) ((finiteResolvent F z*doubleProjectionFlux sharp m ell F g*finiteResolvent F z) (g : H))=
      inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g (singleDefect sharp m ell F)*
        finiteResolvent F z) (g : H)) := by
  filter_upwards [actual_projection_current_zero m ell g k] with F hF
  intro sharp z hz
  have hs := original_projection_split sharp m ell F g
  have hs' : doubleProjectionFlux sharp m ell F g=sourceRead F g (projectionCurrent sharp m ell F)+
      sourceRead F g (singleDefect sharp m ell F) := hs.trans (map_add (sourceRead F g) _ _)
  have hp := congrArg (fun A : Op => inner ℂ (k : H) ((finiteResolvent F z*A*finiteResolvent F z) (g : H))) hs'
  have ha := pair_sandwich_add (finiteResolvent F z) (sourceRead F g (projectionCurrent sharp m ell F))
    (sourceRead F g (singleDefect sharp m ell F)) (g : H) (k : H)
  have hzero := congrArg (fun c : ℂ => c+inner ℂ (k : H)
    ((finiteResolvent F z*sourceRead F g (singleDefect sharp m ell F)*finiteResolvent F z) (g : H)))
      (hF sharp z hz)
  exact hp.trans (ha.trans (hzero.trans (zero_add _)))

/-- The original joined remainder with its three-term projection flux replaced by the generated single-defect word. -/
def singleDefectRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • (gaugeFilter (fun n => linearDefectJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => inverseCross F g z (matterHamiltonianCurrent sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (matterHamiltonianCurrent sharp m ell) 0 n)*
      finiteResolvent F z)+
    finiteResolvent F z*(sourceRead F g
      (-(2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) •
          (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
        (2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) •
          (constantAction sharp SourceQuantumScalarChart.vacuum*SourceMixedNativeReturn.thetaAction m ell)-
        (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-sourceRead F g (singleDefect sharp m ell F)-
      (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F)*
        finiteResolvent F z

private theorem single_remainder_return (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (z : ℂ) :
    singleDefectRemainder sharp m ell F g z=linearRemainder sharp m ell F g z+
      finiteResolvent F z*(doubleProjectionFlux sharp m ell F g-sourceRead F g (singleDefect sharp m ell F))*
        finiteResolvent F z := by
  simp only [singleDefectRemainder,linearRemainder,remainingForces,mul_sub,sub_mul]
  module

/-- The original whole Ward consumes both exact cofinal cancellations on the same source event. -/
theorem actual_ward_single_defect (m ell : ℕ) (g k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ (sharp : Bool) (z : ℂ), z.im≠0 →
      inner ℂ (embed k) (wardOperator sharp m ell F (coreEquiv g) z (embed g))=
        (1/6 : ℂ)*filteredProfile sharp m ell F z g k+
        inner ℂ (embed k) (singleDefectRemainder sharp m ell F (coreEquiv g) z (embed g)) := by
  filter_upwards [actual_ward_linear_remainder (coreEquiv g) g k,
    actual_projection_single_defect m ell (coreEquiv g) (coreEquiv k)] with F hW hD
  intro sharp z hz
  have h := hD sharp z hz
  change inner ℂ (embed k) ((finiteResolvent F z*doubleProjectionFlux sharp m ell F (coreEquiv g)*
    finiteResolvent F z) (embed g))=
    inner ℂ (embed k) ((finiteResolvent F z*sourceRead F (coreEquiv g) (singleDefect sharp m ell F)*
      finiteResolvent F z) (embed g)) at h
  have hr : inner ℂ (embed k) (singleDefectRemainder sharp m ell F (coreEquiv g) z (embed g))=
      inner ℂ (embed k) (linearRemainder sharp m ell F (coreEquiv g) z (embed g)) := by
    have he := congrArg (fun A : Op => inner ℂ (embed k) (A (embed g)))
      (single_remainder_return sharp m ell F (coreEquiv g) z)
    exact he.trans (by
      simp only [mul_sub,sub_mul,add_apply,sub_apply,inner_add_right,inner_sub_right]
      rw [h,sub_self,add_zero])
  exact (hW sharp m ell z hz).trans (congrArg (fun a : ℂ => (1/6 : ℂ)*filteredProfile sharp m ell F z g k+a) hr.symm)

end LowEnergy.SourceInverseProjectionCurrentRemainder
