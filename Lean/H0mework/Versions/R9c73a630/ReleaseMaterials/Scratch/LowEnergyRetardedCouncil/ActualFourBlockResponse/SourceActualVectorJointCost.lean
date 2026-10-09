import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeElectricMomentChannels
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHardyRetardedTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualVectorJointCost
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceResolventBandLimit SourceHardyRetardedTail MeasureTheory Filter
open scoped BigOperators InnerProductSpace Topology ENNReal

/-- Both causal orientations retain the original complex four-pole coefficient. -/
def causalKernel (advanced : Bool) (μ a b c d : ℝ) : ℂ :=
  if advanced then star (closedKernel μ a b c d) else closedKernel μ a b c d

def causalFrequency (advanced : Bool) (μ w : ℝ) : ℂ :=
  line (if advanced then -μ else μ) w

private theorem pole_reflect (μ a w : ℝ) : pole (-μ) a w = -pole μ (-a) (-w) := by
  unfold pole line
  have h : (a : ℂ)-((w : ℂ)+((-μ : ℝ):ℂ)*Complex.I) =
      -(((-a : ℝ):ℂ)-(((-w : ℝ):ℂ)+(μ : ℂ)*Complex.I)) := by push_cast; ring
  rw [h,inv_neg]

private theorem pair_reflect (μ a b w : ℝ) :
    polePair (-μ) a b w = polePair μ (-a) (-b) (-w) := by
  simp only [polePair,pole_reflect,neg_mul_neg]

private theorem star_nat (n : ℕ) : (starRingEnd ℂ) (n : ℂ) = n := map_natCast _ _
private theorem star_of_nat (n : ℕ) [n.AtLeastTwo] :
    (starRingEnd ℂ) (ofNat(n) : ℂ) = ofNat(n) := map_ofNat _ _

private theorem kernel_reflect (μ a b c d : ℝ) :
    closedKernel μ (-a) (-b) (-c) (-d) = star (closedKernel μ a b c d) := by
  simp only [closedKernel,gap,map_div₀,map_mul,map_add,map_sub,star_of_nat,
    Complex.star_def,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
  congr 1 <;> ring

private theorem channel_sum {ι : Type*} (F : Index) (i : Channel F)
    (s : Finset ι) (v : ι → H) : channel F i (∑ j ∈ s,v j) = ∑ j ∈ s,channel F i (v j) := by
  cases i <;> simp [channel,map_sum,Finset.sum_smul]

private theorem channel_smul (F : Index) (i : Channel F) (c : ℂ) (v : H) :
    channel F i (c • v) = c • channel F i v := by
  cases i <;> simp [channel,map_smul,smul_smul]

theorem actual_two_leg_causal_spectral (F : Index) (advanced : Bool) (μ : ℝ)
    (hμ : 0 < μ) (E : H →L[ℂ] H) (g : H) (w : ℝ) :
    finiteResolvent F (causalFrequency advanced μ w)
      (E (finiteResolvent F (causalFrequency advanced μ w) g)) =
      ∑ij : Channel F × Channel F,
        polePair (if advanced then -μ else μ) (channelValue F ij.1) (channelValue F ij.2) w •
          spectralLeg F E g ij := by
  have hz : (causalFrequency advanced μ w).im ≠ 0 := by
    cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'
  rw [SourceInverseElectricMomentChannels.actual_channels F _ hz,
    SourceInverseElectricMomentChannels.actual_channels F _ hz]
  simp only [map_sum,map_smul]
  simp_rw [channel_sum,channel_smul,Finset.smul_sum,smul_smul]
  rw [Fintype.sum_prod_type]
  rfl

private theorem causal_gram_integrable {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (a b : ι → ℝ) (v : ι → V) :
    Integrable (fun w : ℝ => ‖∑ i,
      polePair (if advanced then -μ else μ) (a i) (b i) w • v i‖^2) := by
  cases advanced
  · exact finite_gram_integrable μ hμ a b v
  · simp only [↓reduceIte,pair_reflect]
    exact (finite_gram_integrable μ hμ (fun i => -a i) (fun i => -b i) v).comp_neg

private theorem causal_gram_integral {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (a b : ι → ℝ) (v : ι → V) :
    (∫w : ℝ, ‖∑ i,polePair (if advanced then -μ else μ) (a i) (b i) w • v i‖^2) =
      (∑i,∑j,causalKernel advanced μ (a i) (b i) (a j) (b j) * inner ℂ (v i) (v j)).re := by
  cases advanced
  · simpa only [causalKernel,Bool.false_eq_true,ite_false,four_pole_closed μ _ _ _ _ hμ] using
      finite_gram_integral μ hμ a b v
  · simp only [↓reduceIte,pair_reflect]
    rw [integral_neg_eq_self (fun t : ℝ => ‖∑ i,polePair μ (-a i) (-b i) t • v i‖^2) volume]
    simpa only [causalKernel,↓reduceIte,four_pole_closed μ _ _ _ _ hμ,kernel_reflect] using
      finite_gram_integral μ hμ (fun i => -a i) (fun i => -b i) v

/-- The full vector Gram has no external scalar reader and includes the escape channel. -/
def vectorCost (advanced : Bool) (F : Index) (μ : ℝ) (E : H →L[ℂ] H) (g : H) : ℝ :=
  (∑ij : Channel F × Channel F,∑kl : Channel F × Channel F,
    causalKernel advanced μ (channelValue F ij.1) (channelValue F ij.2)
      (channelValue F kl.1) (channelValue F kl.2) *
        inner ℂ (spectralLeg F E g ij) (spectralLeg F E g kl)).re

def vectorJointCost (advanced sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (g : H) : ℝ :=
  vectorCost advanced F μ (jointInsertion sharp m ell F) g

theorem actual_vector_causal_integrable (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (E : H →L[ℂ] H) (g : H) :
    Integrable (fun w : ℝ => ‖finiteResolvent F (causalFrequency advanced μ w)
      (E (finiteResolvent F (causalFrequency advanced μ w) g))‖^2) := by
  simp_rw [actual_two_leg_causal_spectral F advanced μ hμ E g]
  exact causal_gram_integrable advanced μ hμ _ _ _

theorem actual_vector_causal_energy (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (E : H →L[ℂ] H) (g : H) :
    (∫w : ℝ, ‖finiteResolvent F (causalFrequency advanced μ w)
      (E (finiteResolvent F (causalFrequency advanced μ w) g))‖^2) =
      vectorCost advanced F μ E g := by
  simp_rw [actual_two_leg_causal_spectral F advanced μ hμ E g]
  exact causal_gram_integral advanced μ hμ _ _ _

theorem actual_vector_joint_energy (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : H) :
    (∫w : ℝ, ‖finiteResolvent F (causalFrequency advanced μ w)
      (jointInsertion sharp m ell F (finiteResolvent F (causalFrequency advanced μ w) g))‖^2) =
      vectorJointCost advanced sharp m ell F μ g :=
  actual_vector_causal_energy F advanced μ hμ _ g

theorem actual_vector_joint_nonnegative (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : H) :
    0 ≤ vectorJointCost advanced sharp m ell F μ g := by
  rw [←actual_vector_joint_energy advanced sharp m ell F μ hμ g]
  exact integral_nonneg (fun _ => sq_nonneg _)

private theorem causal_nonreal (advanced : Bool) (μ w : ℝ) (hμ : 0 < μ) :
    (causalFrequency advanced μ w).im ≠ 0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

def jointVector (advanced sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (g : H) (w : ℝ) : H :=
  finiteResolvent F (causalFrequency advanced μ w)
    (jointInsertion sharp m ell F (finiteResolvent F (causalFrequency advanced μ w) g))

def hardyVector (advanced sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (g : H) (w : ℝ) : H :=
  particular sharp m ell F (causalFrequency advanced μ w) g +
    causalFrequency advanced μ w • finiteResolvent F (causalFrequency advanced μ w)
      (particular sharp m ell F (causalFrequency advanced μ w) g)

def hardyPrice (advanced sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (g : H) : ℝ :=
  vectorCost advanced F μ
    (GaussGradedCompression.compression F * cutoffSolver sharp m ell) g

private theorem hardy_return (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : H) (w : ℝ) :
    hardyVector advanced sharp m ell F μ g w =
      finiteResolvent F (causalFrequency advanced μ w)
        ((GaussGradedCompression.compression F * cutoffSolver sharp m ell)
          (finiteResolvent F (causalFrequency advanced μ w) g)) := by
  have h := congrArg (fun A : H →L[ℂ] H =>
    A (particular sharp m ell F (causalFrequency advanced μ w) g))
      (resolvent_compression (GaussGradedCompression.compression F)
        (GaussGradedCompression.compression_selfAdjoint F)
        (causalFrequency advanced μ w) (causal_nonreal advanced μ w hμ))
  exact h.symm

theorem actual_hardy_vector_integrable (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : H) :
    Integrable (fun w : ℝ => ‖hardyVector advanced sharp m ell F μ g w‖^2) := by
  simp_rw [hardy_return advanced sharp m ell F μ hμ g]
  exact actual_vector_causal_integrable F advanced μ hμ _ g

theorem actual_hardy_vector_energy (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : H) :
    (∫w : ℝ, ‖hardyVector advanced sharp m ell F μ g w‖^2) =
      hardyPrice advanced sharp m ell F μ g := by
  simp_rw [hardy_return advanced sharp m ell F μ hμ g]
  exact actual_vector_causal_energy F advanced μ hμ _ g

/-- The unweighted original increment has its literal joint residual and
its already source-generated Hardy particular, with no dropped interference. -/
theorem actual_increment_vector_split (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : H) (w : ℝ) :
    finiteResolvent F (causalFrequency advanced μ w)
      (SourceEscapeSeedTail.actualIncrement sharp m ell
        (finiteResolvent F (causalFrequency advanced μ w) g)) =
      jointVector advanced sharp m ell F μ g w + hardyVector advanced sharp m ell F μ g w := by
  rw [hardy_return advanced sharp m ell F μ hμ g]
  simp only [jointVector,jointInsertion,sub_apply,
    ContinuousLinearMap.comp_apply,mul_apply_eq_comp,map_sub]
  abel

private theorem two_square (x y : H) : ‖x+y‖^2 ≤ 2*(‖x‖^2+‖y‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

theorem actual_first_leg_vector_price (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : H) :
    (∫w : ℝ, ‖finiteResolvent F (causalFrequency advanced μ w)
      (SourceEscapeSeedTail.actualIncrement sharp m ell
        (finiteResolvent F (causalFrequency advanced μ w) g))‖^2) ≤
      2*vectorJointCost advanced sharp m ell F μ g + 2*hardyPrice advanced sharp m ell F μ g := by
  have hi := actual_vector_causal_integrable F advanced μ hμ
    (SourceEscapeSeedTail.actualIncrement sharp m ell) g
  have hj := actual_vector_causal_integrable F advanced μ hμ (jointInsertion sharp m ell F) g
  have hh := actual_hardy_vector_integrable advanced sharp m ell F μ hμ g
  have bound (w : ℝ) :
      ‖finiteResolvent F (causalFrequency advanced μ w)
        (SourceEscapeSeedTail.actualIncrement sharp m ell
          (finiteResolvent F (causalFrequency advanced μ w) g))‖^2 ≤
      2*(‖jointVector advanced sharp m ell F μ g w‖^2 +
        ‖hardyVector advanced sharp m ell F μ g w‖^2) := by
    rw [actual_increment_vector_split advanced sharp m ell F μ hμ g w]
    exact two_square _ _
  have hj' : Integrable (fun w : ℝ => ‖jointVector advanced sharp m ell F μ g w‖^2) := hj
  calc
    _ ≤ ∫w : ℝ,2*(‖jointVector advanced sharp m ell F μ g w‖^2+
          ‖hardyVector advanced sharp m ell F μ g w‖^2) :=
      integral_mono hi ((hj'.add hh).const_mul 2) bound
    _ = _ := by
      rw [integral_const_mul,integral_add hj' hh,
        actual_hardy_vector_energy advanced sharp m ell F μ hμ g]
      change 2*((∫w : ℝ,‖jointVector advanced sharp m ell F μ g w‖^2)+_)=_
      rw [show (∫w : ℝ,‖jointVector advanced sharp m ell F μ g w‖^2)=
        vectorJointCost advanced sharp m ell F μ g from
          actual_vector_joint_energy advanced sharp m ell F μ hμ g]
      ring

/-- The positive causal line consumes the already paid Hardy tail. The
remaining vector price is computed from the original source channels. -/
theorem actual_first_leg_paid_price (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) :
    ∀ε : ℝ,0 < ε → ∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
      (∫w : ℝ, ‖finiteResolvent F (line μ w)
        (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F (line μ w) (g : H)))‖^2) ≤
      2*vectorJointCost false sharp m ell F μ (g : H)+ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_hardy_retarded_tail μ hμ sharp g (ε/2) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have hi := actual_hardy_vector_integrable false sharp m ell F μ hμ (g : H)
  have he := (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun w => sq_nonneg ‖hardyVector false sharp m ell F μ (g : H) w‖))).symm
  rw [actual_hardy_vector_energy false sharp m ell F μ hμ (g : H)] at he
  change (∫⁻w : ℝ, ENNReal.ofReal (‖hardyVector false sharp m ell F μ (g : H) w‖^2)) ≤
    ENNReal.ofReal (ε/2) at hF
  rw [he] at hF
  have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ ε/2)).mp hF
  have hb := actual_first_leg_vector_price false sharp m ell F μ hμ (g : H)
  change (∫w : ℝ,‖finiteResolvent F (line μ w)
    (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F (line μ w) (g : H)))‖^2) ≤
      2*vectorJointCost false sharp m ell F μ (g : H)+2*hardyPrice false sharp m ell F μ (g : H) at hb
  linarith

end LowEnergy.ActualVectorJointCost
