import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaugeBand
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeElectricMomentChannels

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalAbelZeroRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineDiracDualYukawaSpinJurisdiction SU7MotherLieAlgebra
open PreparationVacuumGaugeSourceInjection PreparationVacuumSourceFieldFamily
open PreparationVacuumActualFieldQuantization PreparationVacuumActionFieldLift
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open GaussFockLabel GaussNativeMatter GaussYukawaGrade GaussHistoryHilbert
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open GaussCoreHilbert GaussCoreDifferential GaussCoreLabel NativeHistoryGrade
open PreparationVacuumSourceActionJets PreparationVacuumRawJointFeedback PreparationVacuumFullFieldRiesz
open PreparationVacuumPhysicalZeroRead PreparationVacuumPhysicalHalfAxis
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumElectromagneticIdentity
open CanonicalGradedCurrent PreparationVacuumPhysicalFeedback SourceFiniteUnitary
open MeasureTheory Set
open scoped Matrix BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
open PreparationVacuumPhysicalGradeZeroRead SourceJointResidualEnergy SourceActualResolventEnergy
open SourceRetardedIncrement FullYSourceResolventGraphSplice SourceInverseElectricMomentChannels

private theorem exp_eigen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : E →L[ℂ] E) (x : E) (c : ℂ) (h : D x=c • x) :
    NormedSpace.exp D x=Complex.exp c • x := by
  have hp (n : ℕ) : (D^n) x=c^n • x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_apply_eq_comp,ih,map_smul,h,smul_smul,pow_succ',mul_comm]
  let ev := ContinuousLinearMap.apply ℂ E x
  change ev (NormedSpace.exp D)=_
  rw [NormedSpace.exp_eq_tsum ℂ,ev.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) D)]
  change (∑' n : ℕ,((n.factorial : ℂ)⁻¹) • ((D^n) x))=Complex.exp c • x
  rw [Complex.exp_eq_exp_ℂ,NormedSpace.exp_eq_tsum ℂ]
  let sx : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight x
  have hs := sx.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) c)
  change (∑' n : ℕ,((n.factorial : ℂ)⁻¹) • c^n) • x=
    ∑' n : ℕ,(((n.factorial : ℂ)⁻¹) • c^n) • x at hs
  rw [hs]
  apply tsum_congr
  intro n
  rw [hp,smul_smul,smul_eq_mul]

theorem sourceC0_generated (F : GaussUnitaryHistory.Index) : actualC 0 F=GaussGradedCompression.compression F :=
  CanonicalPhysicalSpatial.compression_zero F

theorem source_channel_eigen (F : GaussUnitaryHistory.Index) (i : Channel F) (x : GaussCoreHilbert.H) :
    actualC 0 F (channel F i x)=(channelValue F i : ℂ) • channel F i x := by
  rw [sourceC0_generated]
  cases i with
  | none => simpa only [channel,channelValue,Complex.ofReal_zero,zero_smul] using compression_escape_zero F x
  | some i =>
    have h := (show (supportAction F).toLinearMap.IsSymmetric from
      (support_action_selfAdjoint F).isSymmetric).apply_eigenvectorBasis rfl i
    have he : GaussGradedCompression.compression F ((SourceJointResidualEnergy.sourceBasis F) i : GaussCoreHilbert.H)=
      (channelValue F (some i) : ℂ) • ((SourceJointResidualEnergy.sourceBasis F) i : GaussCoreHilbert.H) := by
      simpa only [SourceJointResidualEnergy.sourceBasis,SourceFiniteResolventEnergy.basis,channelValue,
        SourceFiniteResolventEnergy.eigenvalue] using! congrArg (fun y : supportSpan F => (y : GaussCoreHilbert.H)) h
    change GaussGradedCompression.compression F ((_ : ℂ) • ((SourceJointResidualEnergy.sourceBasis F) i : GaussCoreHilbert.H))=_
    rw [map_smul,he]
    exact smul_comm _ _ _

theorem source_channel_resolution (F : GaussUnitaryHistory.Index) (x : GaussCoreHilbert.H) :
    ∑ i : Channel F,channel F i x=x := by
  rw [Fintype.sum_option]
  simp only [channel]
  have hs := congrArg (supportSpan F).subtypeL
    ((SourceJointResidualEnergy.sourceBasis F).sum_repr ((supportSpan F).orthogonalProjectionOnto x))
  simp only [map_sum,map_smul] at hs
  change escapeProjection F x+(∑ i,(SourceJointResidualEnergy.sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto x) i • ((SourceJointResidualEnergy.sourceBasis F) i : GaussCoreHilbert.H))=x
  change (∑ i,(SourceJointResidualEnergy.sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto x) i • ((SourceJointResidualEnergy.sourceBasis F) i : GaussCoreHilbert.H))=((supportSpan F).orthogonalProjectionOnto x : GaussCoreHilbert.H) at hs
  rw [hs]
  change (x-(supportSpan F).starProjection x)+(supportSpan F).starProjection x=x
  abel

def sourcePhase (F : GaussUnitaryHistory.Index) (i : Channel F) (t : ℝ) : ℂ :=
  Complex.exp ((-Complex.I)*(channelValue F i : ℂ)*(t : ℂ))

theorem source_time_channel (F : GaussUnitaryHistory.Index) (i : Channel F) (x : GaussCoreHilbert.H) (t : ℝ) :
    time (actualC 0 F) t (channel F i x)=sourcePhase F i t • channel F i x := by
  apply exp_eigen
  change (t : ℝ) • ((-Complex.I) • (actualC 0 F (channel F i x)))=_
  rw [source_channel_eigen,smul_smul]
  rw [←smul_assoc,Complex.real_smul]
  congr 1
  ring

theorem source_time_channels (F : GaussUnitaryHistory.Index) (x : GaussCoreHilbert.H) (t : ℝ) :
    time (actualC 0 F) t x=∑ i : Channel F,sourcePhase F i t • channel F i x := by
  conv_lhs => rw [←source_channel_resolution F x]
  simp only [map_sum,source_time_channel]

private theorem resolvent_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (x : E) (a : ℝ) (hx : C x=(a : ℂ) • x)
    (z : ℂ) (hz : z.im≠0) : FullYSourceResolventGraphSplice.resolvent C z x=((a : ℂ)-z)⁻¹ • x := by
  have hn : (a : ℂ)-z≠0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    exact hz hi
  have h := congrArg (fun A : E →L[ℂ] E=>A x) (resolvent_left C hC z hz)
  change FullYSourceResolventGraphSplice.resolvent C z (C x-z • x)=x at h
  rw [hx,←sub_smul,map_smul] at h
  have hi := congrArg (fun y : E=>((a : ℂ)-z)⁻¹ • y) h
  simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using hi

theorem source_resolvent_time_channels (F : GaussUnitaryHistory.Index) (x : GaussCoreHilbert.H) (t : ℝ)
    (z : ℂ) (hz : z.im≠0) :
    CanonicalPhysicalResolvent.finiteResolvent 0 F z (time (actualC 0 F) t x)=
      ∑ i : Channel F,(sourcePhase F i t*((channelValue F i : ℂ)-z)⁻¹) • channel F i x := by
  rw [source_time_channels]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  have h := resolvent_eigen (actualC 0 F) (CanonicalPhysicalSpatial.compression_selfAdjoint 0 F)
    (channel F i x) (channelValue F i) (source_channel_eigen F i x) z hz
  change sourcePhase F i t • (FullYSourceResolventGraphSplice.resolvent (actualC 0 F) z (channel F i x))=_
  rw [h,smul_smul]


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



private theorem time_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (t : ℝ) (x y : E) :
    inner ℂ (time C t x) y=inner ℂ x (time C (-t) y) := by
  have h := FullYSourceCutoffVolterra.time_adjoint C t
  rw [hC.adjoint_eq] at h
  rw [←h]
  exact ((time C t).adjoint_inner_right x y).symm

def sourceStaticCoefficient (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (i j : Channel q.F) : ℂ :=
  -(((channelValue q.F i : ℂ)-q.z)⁻¹*((channelValue q.F j : ℂ)-q.w)⁻¹*
    inner ℂ (channel q.F i (sourcePolePrepared q.epsilon q.precision 0 left))
      (rawReader (gaugeField mu a) 0 q.F 0 (channel q.F j (sourcePolePrepared q.epsilon q.precision 0 right))))

def sourceStaticPhase (F : GaussUnitaryHistory.Index) (i j : Channel F) (t : ℝ) : ℂ :=
  star (sourcePhase F i t)*sourcePhase F j t

set_option backward.isDefEq.respectTransparency false in
theorem sourceStaticCurrent_channels (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourcePoleActionEuler q 0 0 left right 0 t (gaugeSlot mu a)=
      ∑ i : Channel q.F,∑ j : Channel q.F,sourceStaticPhase q.F i j t*sourceStaticCoefficient q left right mu a i j := by
  rw [sourceGaugeCurrent_zeroHistory q 0 0 left right mu a t nonrealL nonrealR,sourcePoleRead_actual]
  unfold sourceGaugeZeroHistoryKernel
  simp only [mul_apply_eq_comp]
  rw [←time_pair (actualC 0 q.F) (CanonicalPhysicalSpatial.compression_selfAdjoint 0 q.F) t]
  have recognize (z : ℂ) : CanonicalPhysicalResolvent.finiteResolvent 0 q.F z=
      FullYSourceResolventGraphSplice.resolvent (actualC 0 q.F) z:=rfl
  rw [recognize q.z]
  rw [resolvent_pair (actualC 0 q.F) (CanonicalPhysicalSpatial.compression_selfAdjoint 0 q.F) q.z nonrealL]
  rw [←recognize (star q.z)]
  rw [source_resolvent_time_channels q.F _ t (star q.z)
    (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using nonrealL),
    source_resolvent_time_channels q.F _ t q.w nonrealR]
  simp only [map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceStaticPhase,sourceStaticCoefficient,star_mul,star_inv₀,star_sub,
    Complex.star_def,Complex.conj_ofReal,Complex.conj_conj]
  ring

end LowEnergy.PreparationVacuumPhysicalAbelZeroRead
