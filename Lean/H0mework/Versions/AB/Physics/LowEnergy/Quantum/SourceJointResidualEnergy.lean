import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCornerPartition
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceActualResolventEnergy
import Mathlib.MeasureTheory.Function.L2Space

/-! The actual joint residual retains all spectral channels before its frequency integral. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceJointResidualEnergy
open MeasureTheory GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceHardyRetardedTail SourceRetardedIncrement
open SourceActualResolventEnergy SourceResolventLorentzian
open SourceResolventBandLimit (line line_im)
open scoped InnerProductSpace

def jointInsertion (sharp : Bool) (m ell : ℕ) (F : Index) : H →L[ℂ] H :=
  SourceEscapeSeedTail.actualIncrement sharp m ell -
    (GaussGradedCompression.compression F).comp (cutoffSolver sharp m ell)

def jointResidual (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g k : diagonal.domain) : ℂ :=
  inner ℂ (SourceKineticTranspose.outerResidual F (star z)
    (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
    (particular sharp m ell F z (g : H))+
  inner ℂ (k : H) (finiteResolvent F z (SourceCornerPartition.complement
    (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H)))))

theorem actual_joint_as_same_compression (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    jointResidual sharp m ell F z hz g k=
      inner ℂ (k : H) (finiteResolvent F z
        (jointInsertion sharp m ell F (finiteResolvent F z (g : H)))) := by
  have hi := SourceCornerPartition.actual_full_increment_splice sharp m ell F z hz g k
  have hr := congrArg (fun T : H →L[ℂ] H =>
    T (particular sharp m ell F z (g : H)))
    (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F
    (particular sharp m ell F z (g : H)))=
      particular sharp m ell F z (g : H)+
        z • finiteResolvent F z (particular sharp m ell F z (g : H)) at hr
  rw [←hr] at hi
  unfold jointResidual jointInsertion
  simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub,
    inner_sub_right]
  change _=inner ℂ (k : H) (finiteResolvent F z
    (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H))))-
      inner ℂ (k : H) (finiteResolvent F z
        (GaussGradedCompression.compression F (particular sharp m ell F z (g : H))))
  linear_combination -hi

abbrev SpectralIndex (F : Index) := Fin (Module.finrank ℂ (supportSpan F))
abbrev Channel (F : Index) := Option (SpectralIndex F)

def sourceBasis (F : Index) : OrthonormalBasis (SpectralIndex F) ℂ (supportSpan F) :=
  SourceFiniteResolventEnergy.basis (supportAction F) (support_action_selfAdjoint F)

def channelValue (F : Index) : Channel F → ℝ
  | none => 0
  | some i => SourceFiniteResolventEnergy.eigenvalue (supportAction F)
      (support_action_selfAdjoint F) i

def channel (F : Index) (i : Channel F) (x : H) : H :=
  match i with
  | none => escapeProjection F x
  | some j => (sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto x) j •
      ((sourceBasis F) j : H)

def pole (μ a t : ℝ) : ℂ := ((a : ℂ)-line μ t)⁻¹
def polePair (μ a b t : ℝ) : ℂ := pole μ a t*pole μ b t

theorem actual_resolvent_spectral (F : Index) (μ : ℝ) (hμ : 0<μ) (t : ℝ) (x : H) :
    finiteResolvent F (line μ t) x=
      ∑ i : Channel F, pole μ (channelValue F i) t • channel F i x := by
  classical
  have hz : (line μ t).im≠0 := by simpa only [line_im] using hμ.ne'
  let y := (supportSpan F).orthogonalProjectionOnto x
  let r := FullYSourceResolventGraphSplice.resolvent (supportAction F) (line μ t) y
  have hs := congrArg (supportSpan F).subtypeL ((sourceBasis F).sum_repr r)
  simp only [map_sum,map_smul] at hs
  have hc (i : SpectralIndex F) :
      (sourceBasis F).repr r i=pole μ (channelValue F (some i)) t*(sourceBasis F).repr y i :=
    SourceFiniteResolventEnergy.coordinate_resolvent (supportAction F)
      (support_action_selfAdjoint F) (line μ t) hz y i
  simp_rw [hc,mul_smul] at hs
  change (∑ i, pole μ (channelValue F (some i)) t •
    (sourceBasis F).repr y i • ((sourceBasis F) i : H))=(r : H) at hs
  rw [resolvent_split F (line μ t) hz x]
  have he : finiteResolvent F (line μ t) (supportProjection F x)=(r : H) :=
    (support_resolvent F (line μ t) hz y).symm
  rw [he,←hs,Fintype.sum_option]
  simp only [channelValue,channel,pole,Complex.ofReal_zero,zero_sub,inv_neg]
  exact add_comm _ _

def spectralLeg (F : Index) (E : H →L[ℂ] H) (g : H)
    (ij : Channel F × Channel F) : H := channel F ij.1 (E (channel F ij.2 g))

private theorem channel_sum (F : Index) (i : Channel F) {ι : Type*} (s : Finset ι)
    (v : ι → H) : channel F i (∑ j ∈ s, v j)=∑ j ∈ s,channel F i (v j) := by
  cases i <;> simp [channel,map_sum,Finset.sum_smul]

private theorem channel_smul (F : Index) (i : Channel F) (a : ℂ) (x : H) :
    channel F i (a • x)=a • channel F i x := by
  cases i <;> simp [channel,map_smul,smul_smul]

theorem actual_two_leg_spectral (F : Index) (μ : ℝ) (hμ : 0<μ)
    (E : H →L[ℂ] H) (g : H) (t : ℝ) :
    finiteResolvent F (line μ t) (E (finiteResolvent F (line μ t) g))=
      ∑ ij : Channel F × Channel F,
        polePair μ (channelValue F ij.1) (channelValue F ij.2) t • spectralLeg F E g ij := by
  classical
  rw [actual_resolvent_spectral F μ hμ t (E _),actual_resolvent_spectral F μ hμ t g]
  simp only [map_sum,map_smul]
  simp_rw [channel_sum,channel_smul,Finset.smul_sum,smul_smul]
  rw [Fintype.sum_prod_type]
  rfl

def fourPole (μ a b c d : ℝ) : ℂ :=
  ∫ t : ℝ, star (polePair μ a b t)*polePair μ c d t

private theorem pole_ne (μ a t : ℝ) (hμ : 0<μ) : (a : ℂ)-line μ t≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.ofReal_im,line_im,Complex.zero_im,zero_sub,
    neg_eq_zero] at hi
  exact hμ.ne' hi

theorem pole_continuous (μ a : ℝ) (hμ : 0<μ) : Continuous (pole μ a) := by
  apply Continuous.inv₀ _ (fun t => pole_ne μ a t hμ)
  unfold line
  fun_prop

theorem pole_bound (μ a t : ℝ) (hμ : 0<μ) : ‖pole μ a t‖≤μ⁻¹ := by
  unfold pole
  rw [norm_inv]
  apply inv_anti₀ hμ
  have h := Complex.abs_im_le_norm ((a : ℂ)-line μ t)
  simpa only [Complex.sub_im,Complex.ofReal_im,line_im,zero_sub,abs_neg,abs_of_pos hμ] using h

theorem pole_memLp (μ a : ℝ) (hμ : 0<μ) : MemLp (pole μ a) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (pole_continuous μ a hμ).aestronglyMeasurable).mpr
  have he : (fun t : ℝ => ‖pole μ a t‖^2)=kernel μ a := by
    funext t
    simpa only [pole,line,mul_comm] using inverse_norm_square μ a t
  rw [he]
  exact kernel_integrable μ a hμ

theorem pole_pair_memLp (μ a b : ℝ) (hμ : 0<μ) : MemLp (polePair μ a b) 2 := by
  apply (pole_memLp μ a hμ).of_le_mul (c := μ⁻¹)
    ((pole_continuous μ a hμ).mul (pole_continuous μ b hμ)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  change ‖pole μ a t*pole μ b t‖≤μ⁻¹*‖pole μ a t‖
  rw [norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (pole_bound μ b t hμ) (norm_nonneg _)

theorem four_pole_integrable (μ a b c d : ℝ) (hμ : 0<μ) :
    Integrable (fun t : ℝ => star (polePair μ a b t)*polePair μ c d t) := by
  apply memLp_one_iff_integrable.mp
  exact (pole_pair_memLp μ c d hμ).mul' (pole_pair_memLp μ a b hμ).star

private theorem finite_gram_pointwise {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} [Fintype ι] (μ : ℝ) (a b : ι → ℝ) (v : ι → V) (t : ℝ) :
    ‖∑ i, polePair μ (a i) (b i) t • v i‖^2=
      (∑ i,∑ j, (star (polePair μ (a i) (b i) t)*polePair μ (a j) (b j) t)*
        inner ℂ (v i) (v j)).re := by
  classical
  change _=(RCLike.re (∑ i,∑ j, (star (polePair μ (a i) (b i) t)*polePair μ (a j) (b j) t)*
    inner ℂ (v i) (v j)))
  rw [←inner_self_eq_norm_sq (𝕜 := ℂ)]
  apply congrArg (RCLike.re : ℂ → ℝ)
  rw [sum_inner]
  simp only [inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finite_gram_integrable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} [Fintype ι] (μ : ℝ) (hμ : 0<μ) (a b : ι → ℝ) (v : ι → V) :
    Integrable (fun t : ℝ => ‖∑ i, polePair μ (a i) (b i) t • v i‖^2) := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (four_pole_integrable μ (a i) (b i) (a j) (b j) hμ).mul_const (inner ℂ (v i) (v j))))
  exact hi.re.congr (Filter.Eventually.of_forall (fun t => (finite_gram_pointwise μ a b v t).symm))

theorem finite_gram_integral {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} [Fintype ι] (μ : ℝ) (hμ : 0<μ) (a b : ι → ℝ) (v : ι → V) :
    (∫ t : ℝ, ‖∑ i, polePair μ (a i) (b i) t • v i‖^2)=
      (∑ i,∑ j, fourPole μ (a i) (b i) (a j) (b j)*inner ℂ (v i) (v j)).re := by
  classical
  have hi (i j : ι) : Integrable (fun t : ℝ =>
      (star (polePair μ (a i) (b i) t)*polePair μ (a j) (b j) t)*inner ℂ (v i) (v j)) :=
    (four_pole_integrable μ (a i) (b i) (a j) (b j) hμ).mul_const _
  simp_rw [finite_gram_pointwise μ a b v]
  change (∫ t : ℝ, RCLike.re (∑ i,∑ j,
    (star (polePair μ (a i) (b i) t)*polePair μ (a j) (b j) t)*inner ℂ (v i) (v j)))=_
  rw [integral_re (integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j)))]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j),integral_mul_const]
  rfl

def actualVectorGram (F : Index) (μ : ℝ) (E : H →L[ℂ] H) (g : H) : ℝ :=
  (∑ ij : Channel F × Channel F, ∑ kl : Channel F × Channel F,
    fourPole μ (channelValue F ij.1) (channelValue F ij.2)
      (channelValue F kl.1) (channelValue F kl.2)*
        inner ℂ (spectralLeg F E g ij) (spectralLeg F E g kl)).re

theorem actual_vector_square_integrable (F : Index) (μ : ℝ) (hμ : 0<μ)
    (E : H →L[ℂ] H) (g : H) :
    Integrable (fun t : ℝ => ‖finiteResolvent F (line μ t) (E (finiteResolvent F (line μ t) g))‖^2) := by
  simp_rw [actual_two_leg_spectral F μ hμ E g]
  exact finite_gram_integrable μ hμ _ _ _

/-- Every actual finite F is integrated before any filter; the zero-action escape channel is included. -/
theorem actual_vector_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (E : H →L[ℂ] H) (g : H) :
    (∫ t : ℝ, ‖finiteResolvent F (line μ t) (E (finiteResolvent F (line μ t) g))‖^2)=
      actualVectorGram F μ E g := by
  simp_rw [actual_two_leg_spectral F μ hμ E g]
  exact finite_gram_integral μ hμ _ _ _

def actualJointGram (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (g k : H) : ℝ :=
  (∑ ij : Channel F × Channel F, ∑ kl : Channel F × Channel F,
    fourPole μ (channelValue F ij.1) (channelValue F ij.2)
      (channelValue F kl.1) (channelValue F kl.2)*
      inner ℂ (inner ℂ k (spectralLeg F (jointInsertion sharp m ell F) g ij))
        (inner ℂ k (spectralLeg F (jointInsertion sharp m ell F) g kl))).re

theorem actual_joint_square_integrable (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    Integrable (fun t : ℝ => ‖jointResidual sharp m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g k‖^2) := by
  simp_rw [actual_joint_as_same_compression,actual_two_leg_spectral F μ hμ,
    inner_sum,inner_smul_right]
  exact finite_gram_integrable μ hμ _ _ _

/-- The original signed outer residual and source complement have one complete finite spectral Gram. -/
theorem actual_joint_energy (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    (∫ t : ℝ, ‖jointResidual sharp m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g k‖^2)=
      actualJointGram sharp m ell F μ (g : H) (k : H) := by
  simp_rw [actual_joint_as_same_compression,actual_two_leg_spectral F μ hμ,
    inner_sum,inner_smul_right]
  exact finite_gram_integral μ hμ _ _ _

theorem actual_joint_gram_nonneg (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    0≤actualJointGram sharp m ell F μ (g : H) (k : H) := by
  rw [←actual_joint_energy sharp m ell F μ hμ g k]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem actual_joint_lintegral (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ t, ENNReal.ofReal (‖jointResidual sharp m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g k‖^2))=
      ENNReal.ofReal (actualJointGram sharp m ell F μ (g : H) (k : H)) := by
  rw [←ofReal_integral_eq_lintegral_ofReal
    (actual_joint_square_integrable sharp m ell F μ hμ g k)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    actual_joint_energy sharp m ell F μ hμ g k]

end LowEnergy.SourceJointResidualEnergy
