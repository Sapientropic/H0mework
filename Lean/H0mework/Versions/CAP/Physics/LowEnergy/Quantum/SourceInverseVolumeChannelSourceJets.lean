import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeNoetherChannelGap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseChannelSourceJets
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory GaussAdjointHistory
open SourceInverseNoetherChannelGap SourceJointResidualEnergy SourceActualResolventEnergy SourceRetardedIncrement
open Filter
open scoped InnerProductSpace

private theorem basis_eigen (F : Index) (i : SpectralIndex F) :
    GaussGradedCompression.compression F ((sourceBasis F) i : H)=
      (channelValue F (some i) : ℂ) • ((sourceBasis F) i : H) := by
  have h := (show (supportAction F).toLinearMap.IsSymmetric from
    (support_action_selfAdjoint F).isSymmetric).apply_eigenvectorBasis rfl i
  simpa only [sourceBasis,SourceFiniteResolventEnergy.basis,channelValue,
    SourceFiniteResolventEnergy.eigenvalue] using! congrArg (fun x : supportSpan F => (x : H)) h

private theorem channel_some (F : Index) (i : SpectralIndex F) (x : H) :
    channel F (some i) x=inner ℂ ((sourceBasis F) i : H) x • ((sourceBasis F) i : H) := by
  rw [channel,OrthonormalBasis.repr_apply_apply]
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

private theorem channel_compression (F : Index) (i : Channel F) (x : H) :
    channel F i (GaussGradedCompression.compression F x)=(channelValue F i : ℂ) • channel F i x := by
  cases i with
  | none => simpa only [channel,channelValue,Complex.ofReal_zero,zero_smul] using escape_compression_zero F x
  | some i =>
    have hp : inner ℂ ((sourceBasis F) i : H) (GaussGradedCompression.compression F x)=
        inner ℂ (GaussGradedCompression.compression F ((sourceBasis F) i : H)) x :=
      (GaussGradedCompression.compression_pair F _ _).symm
    rw [channel_some,channel_some,hp,basis_eigen,inner_smul_left,Complex.conj_ofReal,smul_smul]

private theorem source_jet_channels (n : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ i : Channel F,
      channel F i (iterate n g : H)=(channelValue F i : ℂ)^n • channel F i (g : H) := by
  induction n with
  | zero =>
    exact Filter.Eventually.of_forall (fun F i => by simp only [iterate,pow_zero,Module.End.one_apply,one_smul])
  | succ n ih =>
    filter_upwards [ih,GaussGradedCompression.eventually_exact (iterate n g)] with F hF hH i
    rw [←iterate_step,←hH,channel_compression,hF,smul_smul,pow_succ']

/-- One actual finite H0-source prefix transfers all channel powers to fixed original source jets. -/
theorem actual_channel_source_jet (n : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ i : Channel F,
      channelTest F (iterate n g) i=(channelValue F i : ℂ)^n • channelTest F g i := by
  filter_upwards [source_jet_channels n g] with F hF i
  apply embed_injective
  have he (x : diagonal.domain) (j : Channel F) : embed (channelTest F x j)=channel F j (x : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [map_smul,he,he,hF]

end LowEnergy.SourceInverseChannelSourceJets
