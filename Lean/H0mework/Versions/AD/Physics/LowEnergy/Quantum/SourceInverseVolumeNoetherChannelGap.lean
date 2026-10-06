import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeNoetherCurrentSpectral
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeOriginalNoetherCost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseNoetherChannelGap
open GaussNativeForm GaussFockPair GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPositiveBulkWard SourceScalarPairedTransport SourceInverseNoetherEnergy
open SourceJointResidualEnergy SourceActualResolventEnergy SourceRetardedIncrement SourceJointScaleBudget
open SourceInverseElectricMomentChannels SourceInverseNoetherCurrentSpectral SourceResolventBandLimit
open FullYSourceResolventGraphSplice MeasureTheory
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] state sourcePair bulkAction compressionCore raisedNoetherCurrent

private theorem channel_input (F : Index) (g : diagonal.domain) (i : Channel F) :
    channel F i (g : H)∈inputSpan F g := by
  have hg : (g : H)∈inputSpan F g := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  cases i with
  | none => exact Submodule.sub_mem _ hg (Submodule.mem_sup_left ((supportSpan F).orthogonalProjectionOnto (g : H)).property)
  | some i => exact Submodule.smul_mem _ _ (Submodule.mem_sup_left ((sourceBasis F) i).property)

def channelTest (F : Index) (g : diagonal.domain) (i : Channel F) : QuantumTest :=
  coreEquiv.symm ⟨channel F i (g : H),input_span_core F g (channel_input F g i)⟩

private theorem channel_embed (F : Index) (g : diagonal.domain) (i : Channel F) :
    embed (channelTest F g i)=channel F i (g : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem basis_eigen (F : Index) (i : SpectralIndex F) :
    GaussGradedCompression.compression F ((sourceBasis F) i : H)=
      (channelValue F (some i) : ℂ) • ((sourceBasis F) i : H) := by
  have h := (show (supportAction F).toLinearMap.IsSymmetric from
    (support_action_selfAdjoint F).isSymmetric).apply_eigenvectorBasis rfl i
  simpa only [sourceBasis,SourceFiniteResolventEnergy.basis,channelValue,
    SourceFiniteResolventEnergy.eigenvalue] using! congrArg (fun x : supportSpan F => (x : H)) h

private theorem channel_eigen (F : Index) (i : Channel F) (x : H) :
    GaussGradedCompression.compression F (channel F i x)=(channelValue F i : ℂ) • channel F i x := by
  cases i with
  | none => simpa only [channel,channelValue,Complex.ofReal_zero,zero_smul] using compression_escape_zero F x
  | some i =>
    change GaussGradedCompression.compression F ((_ : ℂ) • ((sourceBasis F) i : H))=_
    rw [map_smul,basis_eigen]
    exact smul_comm _ _ _

/-- Escape and eigenchannels are returned to the original core before computing the current. -/
theorem actual_channel_eigen (F : Index) (g : diagonal.domain) (i : Channel F) :
    compressionCore F (channelTest F g i)=(channelValue F i : ℂ) • channelTest F g i := by
  apply embed_injective
  have hc (f : QuantumTest) : embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [hc,map_smul,channel_embed,channel_eigen]

/-- The whole nonreal source state is a finite sum of these same core channels. -/
theorem actual_state_channels (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    state F z hz g=∑ i : Channel F,((channelValue F i : ℂ)-z)⁻¹ • channelTest F g i := by
  apply embed_injective
  have hs : embed (state F z hz g)=finiteResolvent F z (g : H) := by
    unfold state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [hs,map_sum,map_smul,channel_embed]
  exact actual_channels F z hz (g : H)

/-- The sesquilinear current is generated from the original bulk and compression, with both source slots retained. -/
def currentPair (F : Index) (T : End) (p q : QuantumTest) : ℂ :=
  (Complex.I/2)*(sourcePair (T (compressionCore F p)) (bulkAction (T q))-
    sourcePair (bulkAction (T p)) (T (compressionCore F q)))

private theorem pair_conj (p q : QuantumTest) : sourcePair q p=star (sourcePair p q) := by
  exact (pair_conjugate p q).symm

theorem actual_diagonal_current (F : Index) (T : End) (q : QuantumTest) :
    currentPair F T q q=(raisedNoetherCurrent F T q : ℂ) := by
  rw [currentPair,pair_conj (T (compressionCore F q)) (bulkAction (T q)),original_raised_noether_compression]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

/-- A real spectral gap, not an absolute energy, multiplies every actual current transition. -/
theorem actual_channel_gap (F : Index) (T : End) (g : diagonal.domain) (u v : Channel F) :
    currentPair F T (channelTest F g u) (channelTest F g v)=
      (Complex.I/2)*((channelValue F u : ℂ)-(channelValue F v : ℂ))*
        sourcePair (T (channelTest F g u)) (bulkAction (T (channelTest F g v))) := by
  rw [currentPair,actual_channel_eigen,actual_channel_eigen,map_smul,map_smul]
  have hp (c : ℝ) (a b : QuantumTest) : sourcePair ((c : ℂ) • a) b=(c : ℂ)*sourcePair a b := by
    simp only [sourcePair,map_smul,inner_smul_left,Complex.conj_ofReal]
  have hq (c : ℝ) (a b : QuantumTest) : sourcePair a ((c : ℂ) • b)=(c : ℂ)*sourcePair a b := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hp,hq,←original_bulk_pair]
  ring

theorem actual_equal_value_current_zero (F : Index) (T : End) (g : diagonal.domain) (u v : Channel F)
    (he : channelValue F u=channelValue F v) :
    currentPair F T (channelTest F g u) (channelTest F g v)=0 := by
  rw [actual_channel_gap,he,sub_self,mul_zero,zero_mul]

private theorem pair_sum (F : Index) (T : End) (g : diagonal.domain) (a : Channel F → ℂ) :
    currentPair F T (∑ i,a i • channelTest F g i) (∑ j,a j • channelTest F g j)=
      ∑ i,∑ j,star (a i)*a j*currentPair F T (channelTest F g i) (channelTest F g j) := by
  simp only [currentPair,map_sum,map_smul,sourcePair,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_comm (f := fun x i => a x * (star (a i) *
    inner ℂ (embed (bulkAction (T (channelTest F g i)))) (embed (T (compressionCore F (channelTest F g x))))))]
  simp only [←Finset.sum_sub_distrib,mul_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- This is the complete actual retarded current: every transition keeps its source form coefficient and pole. -/
theorem actual_current_gap_expansion (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (T : End) :
    (raisedNoetherCurrent F T (state F z hz g) : ℂ)=
      ∑ u : Channel F,∑ v : Channel F,
        star (((channelValue F u : ℂ)-z)⁻¹)*((channelValue F v : ℂ)-z)⁻¹*
          ((Complex.I/2)*((channelValue F u : ℂ)-(channelValue F v : ℂ))*
            sourcePair (T (channelTest F g u)) (bulkAction (T (channelTest F g v)))) := by
  rw [←actual_diagonal_current,actual_state_channels,pair_sum]
  simp_rw [actual_channel_gap]

/-- The source gap coefficients determine the entire signed current frequency profile. -/
def gapPair (F : Index) (z : ℂ) (g : diagonal.domain) (T : End) : ℂ :=
  ∑ u : Channel F,∑ v : Channel F,
    star (((channelValue F u : ℂ)-z)⁻¹)*((channelValue F v : ℂ)-z)⁻¹*
      ((Complex.I/2)*((channelValue F u : ℂ)-(channelValue F v : ℂ))*
        sourcePair (T (channelTest F g u)) (bulkAction (T (channelTest F g v))))

def gapCurrent (F : Index) (μ : ℝ) (g k : diagonal.domain) (T : End) : ℝ :=
  ∫ w : ℝ,‖finiteResolvent F (star (line μ w)) (k : H)‖^2*(gapPair F (line μ w) g T).re

/-- The complete integrated Noether producer is this same gap profile, including all escape cross terms. -/
theorem actual_closed_gap_current (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (T : End) :
    closedCurrent F μ g k 1 T=gapCurrent F μ g k T := by
  rw [←actual_current_closed F μ hμ g k 1 T]
  unfold gapCurrent
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by
    have h := congrArg Complex.re (actual_current_gap_expansion F (line μ w)
      (by simpa only [line_im] using hμ.ne') g T)
    simp only [Complex.ofReal_re] at h
    have hs (z : ℂ) (hz : z.im≠0) : embed (state F z hz k)=finiteResolvent F z (k : H) := by
      unfold state
      exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    simpa only [currentMoment,Module.End.one_apply,hs,gapPair] using
      congrArg (fun a : ℝ => ‖finiteResolvent F (star (line μ w)) (k : H)‖^2*a) h)

/-- The original whole joint cost consumes the actual off-equal-value source transitions without an absolute-value replacement. -/
theorem actual_original_gap_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g : H) (k : H) ≤
          ε+(4*SourceScalarSignedInverseReturn.formPrice sharp/μ)*
            gapCurrent F μ g k (SourceScalarInverseRetardedBudget.theta m ell) := by
  have h := SourceInverseOriginalNoetherCost.actual_original_signed_budget sharp μ hμ g k
  simpa only [actual_closed_gap_current _ μ hμ g k] using h

end LowEnergy.SourceInverseNoetherChannelGap
