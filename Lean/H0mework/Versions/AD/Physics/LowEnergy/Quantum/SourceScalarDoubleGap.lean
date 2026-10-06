import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarDoubleCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarDoubleCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussYukawaCoefficient GaussRadialDomain
open SourceCoframeVolumeCurrent SourceCoframeVolume SourceCoframeDilation SourceDilationRemainder
open SourceHamiltonianScaleJet SourceKineticTranspose SourceMixedNativeReturn SourceClosedCostNativeProbe
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarPairedTransport SourcePairedRadialFlux SourcePairedMomentumFlux
open scoped ContDiff InnerProductSpace BigOperators Matrix
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

open GaussUnitaryHistory SourceJointResidualEnergy SourceActualResolventEnergy SourceRetardedIncrement

private def inputTest (F : Index) (g : diagonal.domain) (x : H) : QuantumTest :=
  coreEquiv.symm (Submodule.inclusion (SourceJointScaleBudget.input_span_core F g)
    ((SourceJointScaleBudget.inputSpan F g).orthogonalProjectionOnto x))

private theorem input_embed (F : Index) (g : diagonal.domain) (x : H) :
    embed (inputTest F g x)=((SourceJointScaleBudget.inputSpan F g).orthogonalProjectionOnto x : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_core_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_input (F : Index) (g : diagonal.domain) (x : H) :
    GaussGradedCompression.compression F ((SourceJointScaleBudget.inputSpan F g).orthogonalProjectionOnto x : H)=
      GaussGradedCompression.compression F x := by
  apply ext_inner_left ℂ
  intro y
  have hy : GaussGradedCompression.compression F y∈SourceJointScaleBudget.inputSpan F g :=
    Submodule.mem_sup_left (SourceRetardedIncrement.compression_mem_support F y)
  exact (GaussGradedCompression.compression_pair F y _).symm.trans
    ((Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨GaussGradedCompression.compression F y,hy⟩ x).trans (GaussGradedCompression.compression_pair F y x))

private theorem input_compression (F : Index) (g : diagonal.domain) (x : H) :
    embed (inputTest F g (GaussGradedCompression.compression F x))=GaussGradedCompression.compression F x := by
  rw [input_embed]
  exact congrArg Subtype.val ((SourceJointScaleBudget.inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨GaussGradedCompression.compression F x,Submodule.mem_sup_left (SourceRetardedIncrement.compression_mem_support F x)⟩)

private theorem source_read_compression_left (F : Index) (g : diagonal.domain) (A : CoreEnd) :
    sourceRead F g (compressionCore F*A)=GaussGradedCompression.compression F*sourceRead F g A := by
  apply ContinuousLinearMap.ext
  intro x
  exact compression_core_embed F (A (inputTest F g x))

private theorem source_read_compression_right (F : Index) (g : diagonal.domain) (A : CoreEnd) :
    sourceRead F g (A*compressionCore F)=sourceRead F g A*GaussGradedCompression.compression F := by
  apply ContinuousLinearMap.ext
  intro x
  have he : compressionCore F (inputTest F g x)=inputTest F g (GaussGradedCompression.compression F x) := by
    apply embed_injective
    exact (compression_core_embed F _).trans
      ((congrArg (GaussGradedCompression.compression F) (input_embed F g x)).trans
        ((compression_input F g x).trans (input_compression F g x).symm))
  exact congrArg (fun f : QuantumTest => embed (A f)) he

private theorem source_read_compression_bracket (F : Index) (g : diagonal.domain) (A : CoreEnd) :
    sourceRead F g (bracket (R := CoreEnd) (compressionCore F) A)=bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F) (sourceRead F g A) := by
  simp only [bracket,map_sub,source_read_compression_left,source_read_compression_right]

private theorem double_defect_algebra {R : Type*} [Ring R] (H C X : R) :
    bracket H (bracket H X)-bracket C (bracket C X)=
      bracket C (bracket (H-C) X)+bracket (H-C) (bracket C X)+bracket (H-C) (bracket (H-C) X) := by
  unfold bracket
  noncomm_ring

private theorem double_read_defect {R S : Type*} [Ring R] [Ring S] [Module ℂ R] [Module ℂ S]
    (l : R →ₗ[ℂ] S) (H C X : R) (C' : S)
    (h : ∀ A, l (bracket C A)=bracket C' (l A)) :
    l (bracket C (bracket (H-C) X)+bracket (H-C) (bracket C X)+
      bracket (H-C) (bracket (H-C) X))=
      l (bracket H (bracket H X))-bracket C' (bracket C' (l X)) := by
  rw [←double_defect_algebra,map_sub]
  exact congrArg (fun y : S => l (bracket H (bracket H X))-y)
    ((h (bracket C X)).trans (congrArg (bracket C') (h X)))

private theorem force_return {R S : Type*} [AddCommGroup R] [AddCommGroup S]
    [Module ℂ R] [Module ℂ S] (l : R →ₗ[ℂ] S) (J X W : R) (J' : S) (a : ℂ)
    (h : J+a • X=W) : l W-(l J-J')=J'+a • l X := by
  rw [←h,map_add,map_smul]
  abel

/-- Every grade and input-projection term is retained in the exact original double-compression flux. -/
def doubleProjectionFlux (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) : H →L[ℂ] H :=
  sourceRead F g (
    bracket (R := CoreEnd) (compressionCore F) (bracket (R := CoreEnd) (defectAction F) (fullInsertion sharp m ell))+
    bracket (R := CoreEnd) (defectAction F) (bracket (R := CoreEnd) (compressionCore F) (fullInsertion sharp m ell))+
    bracket (R := CoreEnd) (defectAction F) (bracket (R := CoreEnd) (defectAction F) (fullInsertion sharp m ell)))

theorem actual_double_projection_flux (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    doubleProjectionFlux sharp m ell F g=
      sourceRead F g (bracket (R := CoreEnd) diagonalAction (bracket (R := CoreEnd) diagonalAction (fullInsertion sharp m ell)))-
      bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F)
        (bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F) (sourceRead F g (fullInsertion sharp m ell))) := by
  simpa only [doubleProjectionFlux,defectAction] using!
    double_read_defect (R := CoreEnd) (S := H →L[ℂ] H) (sourceRead F g)
      diagonalAction (compressionCore F) (fullInsertion sharp m ell) (GaussGradedCompression.compression F)
      (fun A => source_read_compression_bracket F g A)

def compressedOscillatorForce (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) : H →L[ℂ] H :=
  sourceRead F g (oscillatorForce sharp m ell)-doubleProjectionFlux sharp m ell F g

/-- The source equation returns to the same actual compressed operator; no flux is discarded. -/
theorem actual_gapped_operator (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    compressedOscillatorForce sharp m ell F g=
      bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F)
        (bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F) (sourceRead F g (fullInsertion sharp m ell)))+
      (2*(sourceTime 0 : ℂ)^2) • sourceRead F g (fullInsertion sharp m ell) := by
  have h := force_return (R := CoreEnd) (S := H →L[ℂ] H) (sourceRead F g)
    (bracket (R := CoreEnd) diagonalAction (bracket (R := CoreEnd) diagonalAction (fullInsertion sharp m ell)))
    (fullInsertion sharp m ell) (oscillatorForce sharp m ell)
    (bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F)
      (bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F) (sourceRead F g (fullInsertion sharp m ell))))
    (2*(sourceTime 0 : ℂ)^2) (original_oscillator_equation sharp m ell)
  exact (congrArg (fun B : H →L[ℂ] H => sourceRead F g (oscillatorForce sharp m ell)-B)
    (actual_double_projection_flux sharp m ell F g)).trans h

private theorem basis_eigen (F : Index) (i : SpectralIndex F) :
    GaussGradedCompression.compression F ((SourceJointResidualEnergy.sourceBasis F) i : H)=
      (channelValue F (some i) : ℂ) • ((SourceJointResidualEnergy.sourceBasis F) i : H) := by
  have h := (show (supportAction F).toLinearMap.IsSymmetric from
    (support_action_selfAdjoint F).isSymmetric).apply_eigenvectorBasis rfl i
  simpa only [SourceJointResidualEnergy.sourceBasis,SourceFiniteResolventEnergy.basis,channelValue,
    SourceFiniteResolventEnergy.eigenvalue] using! congrArg (fun x : supportSpan F => (x : H)) h

private theorem channel_some (F : Index) (i : SpectralIndex F) (x : H) :
    channel F (some i) x=inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H) x • ((SourceJointResidualEnergy.sourceBasis F) i : H) := by
  change (SourceJointResidualEnergy.sourceBasis F).repr
    ((supportSpan F).orthogonalProjectionOnto x) i • _=_
  apply congrArg (fun c : ℂ => c • ((SourceJointResidualEnergy.sourceBasis F) i : H))
  exact ((SourceJointResidualEnergy.sourceBasis F).repr_apply_apply _ _).trans
    (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      ((SourceJointResidualEnergy.sourceBasis F) i) x)

private theorem eigen_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (C : E →L[ℂ] E) (v x : E) (a : ℝ)
    (hp : inner ℂ v (C x)=inner ℂ (C v) x) (he : C v=(a : ℂ) • v) :
    inner ℂ v (C x)=(a : ℂ)*inner ℂ v x := by
  rw [hp,he,inner_smul_left,Complex.conj_ofReal]

private theorem channel_eigen_right (F : Index) (i : Channel F) (x : H) :
    GaussGradedCompression.compression F (channel F i x)=(channelValue F i : ℂ) • channel F i x := by
  cases i with
  | none => simpa only [channel,channelValue,Complex.ofReal_zero,zero_smul] using compression_escape_zero F x
  | some i =>
    rw [channel_some,map_smul,basis_eigen]
    exact smul_comm _ _ _

private theorem channel_eigen_left (F : Index) (i : Channel F) (x : H) :
    channel F i (GaussGradedCompression.compression F x)=(channelValue F i : ℂ) • channel F i x := by
  cases i with
  | none => simpa only [channel,channelValue,Complex.ofReal_zero,zero_smul] using escape_compression_zero F x
  | some i =>
    have hp : inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H)
        (GaussGradedCompression.compression F x)=
        inner ℂ (GaussGradedCompression.compression F ((SourceJointResidualEnergy.sourceBasis F) i : H)) x := by
      simpa only using! (GaussGradedCompression.compression_pair F
        ((SourceJointResidualEnergy.sourceBasis F) i : H) x).symm
    have he := eigen_inner (E := H) (GaussGradedCompression.compression F)
      ((SourceJointResidualEnergy.sourceBasis F) i : H) x (channelValue F (some i)) hp (basis_eigen F i)
    calc
      _=inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H)
          (GaussGradedCompression.compression F x) • ((SourceJointResidualEnergy.sourceBasis F) i : H) :=
        channel_some F i _
      _=((channelValue F (some i) : ℂ)*inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H) x) •
          ((SourceJointResidualEnergy.sourceBasis F) i : H) := congrArg (fun c : ℂ => c • _) he
      _=(channelValue F (some i) : ℂ) •
          (inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H) x • ((SourceJointResidualEnergy.sourceBasis F) i : H)) :=
        (smul_smul _ _ _).symm
      _=_ := congrArg (fun y : H => (channelValue F (some i) : ℂ) • y) (channel_some F i x).symm

private theorem channel_sub (F : Index) (i : Channel F) (x y : H) :
    channel F i (x-y)=channel F i x-channel F i y := by
  cases i <;> simp only [channel,map_sub,PiLp.sub_apply,sub_smul]

private theorem channel_smul (F : Index) (i : Channel F) (c : ℂ) (x : H) :
    channel F i (c • x)=c • channel F i x := by
  cases i <;> simp only [channel,map_smul,PiLp.smul_apply,smul_eq_mul,smul_smul]


private theorem bracket_leg (F : Index) (T : H →L[ℂ] H) (g : H) (ij : Channel F × Channel F) :
    spectralLeg F (bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F) T) g ij=
      ((channelValue F ij.1 : ℂ)-(channelValue F ij.2 : ℂ)) • spectralLeg F T g ij := by
  change channel F ij.1 (GaussGradedCompression.compression F (T (channel F ij.2 g))-
    T (GaussGradedCompression.compression F (channel F ij.2 g)))=_
  rw [channel_sub,channel_eigen_left,channel_eigen_right,map_smul,channel_smul,←sub_smul]
  rfl

private theorem leg_add (F : Index) (A B : H →L[ℂ] H) (g : H) (ij : Channel F × Channel F) :
    spectralLeg F (A+B) g ij=spectralLeg F A g ij+spectralLeg F B g ij := by
  rcases ij with ⟨i,j⟩
  cases i <;> simp only [spectralLeg,channel,add_apply,map_add,PiLp.add_apply,add_smul]

private theorem leg_smul (F : Index) (c : ℂ) (A : H →L[ℂ] H) (g : H) (ij : Channel F × Channel F) :
    spectralLeg F (c • A) g ij=c • spectralLeg F A g ij :=
  channel_smul F ij.1 c (A (channel F ij.2 g))

private def legMap (F : Index) (g : H) (ij : Channel F × Channel F) : (H →L[ℂ] H) →ₗ[ℂ] H where
  toFun T := spectralLeg F T g ij
  map_add' := fun A B => leg_add F A B g ij
  map_smul' := fun c A => leg_smul F c A g ij

private theorem linear_double_leg {R V : Type*} [Ring R] [Module ℂ R]
    [AddCommGroup V] [Module ℂ V] (l : R →ₗ[ℂ] V) (C X : R) (a c : ℂ)
    (h : ∀ A, l (bracket C A)=a • l A) :
    l (bracket C (bracket C X)+c • X)=(a*a+c) • l X := by
  rw [map_add,map_smul,h,h,smul_smul,←add_smul]

private theorem restore_gap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c : ℂ) (hc : c≠0) (u v : V) (h : v=c • u) : u=c⁻¹ • v := by
  rw [h,smul_smul,inv_mul_cancel₀ hc,one_smul]

def sourceGap (F : Index) (ij : Channel F × Channel F) : ℝ :=
  (channelValue F ij.1-channelValue F ij.2)^2+2*(sourceTime 0)^2

/-- Full spectral channels, including NONE and all collisions, acquire the positive source oscillator gap. -/
theorem actual_oscillator_gap_leg (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (ij : Channel F × Channel F) :
    spectralLeg F (compressedOscillatorForce sharp m ell F g) (g : H) ij=
      (sourceGap F ij : ℂ) • spectralLeg F (sourceRead F g (fullInsertion sharp m ell)) (g : H) ij := by
  have h := linear_double_leg (R := H →L[ℂ] H) (V := H) (legMap F (g : H) ij)
    (GaussGradedCompression.compression F) (sourceRead F g (fullInsertion sharp m ell))
    ((channelValue F ij.1 : ℂ)-(channelValue F ij.2 : ℂ)) (2*(sourceTime 0 : ℂ)^2)
    (fun A => bracket_leg F A (g : H) ij)
  have hc : ((channelValue F ij.1 : ℂ)-(channelValue F ij.2 : ℂ))*
      ((channelValue F ij.1 : ℂ)-(channelValue F ij.2 : ℂ))+2*(sourceTime 0 : ℂ)^2=
      (sourceGap F ij : ℂ) := by unfold sourceGap; push_cast; ring
  exact (congrArg (legMap F (g : H) ij) (actual_gapped_operator sharp m ell F g)).trans
    (h.trans (congrArg (fun c : ℂ => c • spectralLeg F
      (sourceRead F g (fullInsertion sharp m ell)) (g : H) ij) hc))

/-- This is the actual insertion coefficient, reconstructed from its complete source force and its exact flux. -/
theorem actual_oscillator_gap_inverse (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (ij : Channel F × Channel F) :
    spectralLeg F (sourceRead F g (fullInsertion sharp m ell)) (g : H) ij=
      (sourceGap F ij : ℂ)⁻¹ • spectralLeg F (compressedOscillatorForce sharp m ell F g) (g : H) ij := by
  have hn : (sourceGap F ij : ℂ)≠0 := by
    exact_mod_cast (source_oscillator_gap_positive (channelValue F ij.1) (channelValue F ij.2)).ne'
  exact restore_gap (V := H) (sourceGap F ij : ℂ) hn _ _
    (actual_oscillator_gap_leg sharp m ell F g ij)

private theorem channel_input (F : Index) (g : diagonal.domain) (i : Channel F) :
    channel F i (g : H)∈SourceJointScaleBudget.inputSpan F g := by
  have hg : (g : H)∈SourceJointScaleBudget.inputSpan F g :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  cases i with
  | none =>
    change (g : H)-SourceRetardedIncrement.supportProjection F (g : H)∈SourceJointScaleBudget.inputSpan F g
    apply Submodule.sub_mem _ hg
    exact Submodule.mem_sup_left ((SourceRetardedIncrement.supportSpan F).orthogonalProjectionOnto (g : H)).property
  | some i =>
    change _ • ((SourceJointResidualEnergy.sourceBasis F) i : H)∈SourceJointScaleBudget.inputSpan F g
    exact Submodule.smul_mem _ _ (Submodule.mem_sup_left ((SourceJointResidualEnergy.sourceBasis F) i).property)

private theorem increment_channel (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (i : Channel F) :
    sourceRead F g (fullInsertion sharp m ell) (channel F i (g : H))=
      SourceEscapeSeedTail.actualIncrement sharp m ell (channel F i (g : H)) := by
  let y : diagonal.domain := ⟨channel F i (g : H),SourceJointScaleBudget.input_span_core F g (channel_input F g i)⟩
  have hy : embed (coreEquiv.symm y)=channel F i (g : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply y)
  have hp := (SourceJointScaleBudget.inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨channel F i (g : H),channel_input F g i⟩
  change embed (fullInsertion sharp m ell (coreEquiv.symm
    (Submodule.inclusion (SourceJointScaleBudget.input_span_core F g)
      ((SourceJointScaleBudget.inputSpan F g).orthogonalProjectionOnto (channel F i (g : H))))))=_
  rw [hp]
  have h := SourceCutoffDilationWard.literal_increment_core sharp m ell (coreEquiv.symm y)
  rw [literal_full_return,hy] at h
  exact h.symm

/-- Original J keeps the full Hardy/compression subtraction after the source oscillator gap is inverted. -/
theorem actual_joint_gap_leg (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (ij : Channel F × Channel F) :
    spectralLeg F (jointInsertion sharp m ell F) (g : H) ij=
      (sourceGap F ij : ℂ)⁻¹ • spectralLeg F (compressedOscillatorForce sharp m ell F g) (g : H) ij-
        spectralLeg F ((GaussGradedCompression.compression F).comp (SourceHardyRetardedTail.cutoffSolver sharp m ell))
          (g : H) ij := by
  have he := congrArg (channel F ij.1) (increment_channel sharp m ell F g ij.2).symm
  change channel F ij.1 (SourceEscapeSeedTail.actualIncrement sharp m ell (channel F ij.2 (g : H))-
    GaussGradedCompression.compression F (SourceHardyRetardedTail.cutoffSolver sharp m ell (channel F ij.2 (g : H))))=_
  rw [channel_sub,he]
  exact congrArg (fun x : H => x-
    spectralLeg F ((GaussGradedCompression.compression F).comp (SourceHardyRetardedTail.cutoffSolver sharp m ell)) (g : H) ij)
      (actual_oscillator_gap_inverse sharp m ell F g ij)

def gapCoefficient (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain)
    (ij : Channel F × Channel F) : ℂ :=
  inner ℂ (k : H) ((sourceGap F ij : ℂ)⁻¹ •
    spectralLeg F (compressedOscillatorForce sharp m ell F g) (g : H) ij-
    spectralLeg F ((GaussGradedCompression.compression F).comp (SourceHardyRetardedTail.cutoffSolver sharp m ell)) (g : H) ij)

/-- The exact original closed cost consumes the gapped source force on the same finite carrier, including every cross term. -/
theorem actual_closed_cost_gap (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (g k : diagonal.domain) :
    SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g : H) (k : H)=
      (∑ ij : Channel F × Channel F, ∑ kl : Channel F × Channel F,
        SourceFourPoleEnergyClosed.closedKernel μ (channelValue F ij.1) (channelValue F ij.2)
          (channelValue F kl.1) (channelValue F kl.2)*
          inner ℂ (gapCoefficient sharp m ell F g k ij) (gapCoefficient sharp m ell F g k kl)).re := by
  unfold SourceFourPoleEnergyClosed.closedJointCost
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  apply Finset.sum_congr rfl
  intro kl _
  rw [actual_joint_gap_leg,actual_joint_gap_leg]
  rfl

end LowEnergy.SourceScalarDoubleCurrent
