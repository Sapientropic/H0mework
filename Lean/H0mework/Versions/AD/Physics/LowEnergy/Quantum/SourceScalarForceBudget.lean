import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarDoubleGap
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarRetardedGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarForceBudget
open MeasureTheory GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy SourceCoframeVolumeCurrent
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceJointResidualEnergy
open SourceFourPoleEnergyClosed FullYSourceResolventGraphSplice
open SourceResolventBandLimit (line line_im)
open scoped InnerProductSpace BigOperators

private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
private abbrev OriginalCore : Type := diagonal.domain

def oscillatorMass : ℝ := 2*(sourceTime 0)^2
private theorem mass_pos : 0<oscillatorMass := by
  exact mul_pos (by norm_num) (sq_pos_of_ne_zero source_time_nonzero)

def solverOperator (sharp : Bool) (m ell : ℕ) (F : Index) : H →L[ℂ] H :=
  (GaussGradedCompression.compression F).comp (SourceHardyRetardedTail.cutoffSolver sharp m ell)

def doubleResponse (sharp : Bool) (m ell : ℕ) (F : Index) (g : OriginalCore) : H →L[ℂ] H :=
  bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F)
    (bracket (R := H →L[ℂ] H) (GaussGradedCompression.compression F)
      (sourceRead F g (fullInsertion sharp m ell)))

/-- The literal source force, including all three projection-flux terms, stays joined to the Hardy subtraction. -/
def balancedForce (sharp : Bool) (m ell : ℕ) (F : Index) (g : OriginalCore) : H →L[ℂ] H :=
  compressedOscillatorForce sharp m ell F g-(oscillatorMass : ℂ) • solverOperator sharp m ell F

private theorem operator_balance {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D X S : V) (a : ℂ) : (D+a • X-a • S)-D=a • (X-S) := by
  rw [smul_sub]
  abel

/-- The positive-gap inverse is cleared against the actual double-CF endpoint operator. -/
theorem actual_force_balance (sharp : Bool) (m ell : ℕ) (F : Index) (g : OriginalCore) :
    balancedForce sharp m ell F g-doubleResponse sharp m ell F g=
      (oscillatorMass : ℂ) • (sourceRead F g (fullInsertion sharp m ell)-solverOperator sharp m ell F) := by
  have hm : (2*(sourceTime 0 : ℂ)^2)=(oscillatorMass : ℂ) := by unfold oscillatorMass; push_cast; rfl
  let D : H →L[ℂ] H := doubleResponse sharp m ell F g
  let X : H →L[ℂ] H := sourceRead F g (fullInsertion sharp m ell)
  let S : H →L[ℂ] H := solverOperator sharp m ell F
  have hg : compressedOscillatorForce sharp m ell F g=D+(2*(sourceTime 0 : ℂ)^2) • X :=
    actual_gapped_operator sharp m ell F g
  have ht : (2*(sourceTime 0 : ℂ)^2) • X=(oscillatorMass : ℂ) • X :=
    congrArg (fun c : ℂ => c • X) hm
  have hf : compressedOscillatorForce sharp m ell F g=D+(oscillatorMass : ℂ) • X :=
    hg.trans (congrArg (fun A : H →L[ℂ] H => D+A) ht)
  exact (congrArg (fun A : H →L[ℂ] H => A-(oscillatorMass : ℂ) • S-D) hf).trans
    (operator_balance D X S (oscillatorMass : ℂ))

def pairCoefficient (F : Index) (A : H →L[ℂ] H) (g k : H) (ij : Channel F × Channel F) : ℂ :=
  inner ℂ k (spectralLeg F A g ij)

private theorem channel_sub (F : Index) (i : Channel F) (x y : H) :
    channel F i (x-y)=channel F i x-channel F i y := by
  cases i <;> simp only [channel,map_sub,PiLp.sub_apply,sub_smul]
private theorem channel_smul (F : Index) (i : Channel F) (c : ℂ) (x : H) :
    channel F i (c • x)=c • channel F i x := by
  cases i <;> simp only [channel,map_smul,PiLp.smul_apply,smul_eq_mul,smul_smul]
private theorem coefficient_sub (F : Index) (A B : H →L[ℂ] H) (g k : H) (ij : Channel F × Channel F) :
    pairCoefficient F (A-B) g k ij=pairCoefficient F A g k ij-pairCoefficient F B g k ij := by
  simp only [pairCoefficient,spectralLeg,sub_apply,channel_sub,inner_sub_right]
private theorem coefficient_smul (F : Index) (c : ℂ) (A : H →L[ℂ] H) (g k : H) (ij : Channel F × Channel F) :
    pairCoefficient F (c • A) g k ij=c*pairCoefficient F A g k ij := by
  simp only [pairCoefficient,spectralLeg,smul_apply,channel_smul,inner_smul_right]

def forceCoefficient (sharp : Bool) (m ell : ℕ) (F : Index) (g k : OriginalCore) : Channel F × Channel F → ℂ :=
  pairCoefficient F (balancedForce sharp m ell F g) (g : H) (k : H)
def endpointCoefficient (sharp : Bool) (m ell : ℕ) (F : Index) (g k : OriginalCore) : Channel F × Channel F → ℂ :=
  pairCoefficient F (doubleResponse sharp m ell F g) (g : H) (k : H)

/-- Every whole spectral channel, including NONE and all repeated eigenvalues, has the same exact balance. -/
theorem actual_gap_coefficient_balance (sharp : Bool) (m ell : ℕ) (F : Index) (g k : OriginalCore)
    (ij : Channel F × Channel F) :
    forceCoefficient sharp m ell F g k ij-endpointCoefficient sharp m ell F g k ij=
      (oscillatorMass : ℂ)*gapCoefficient sharp m ell F g k ij := by
  have h := congrArg (fun A : H →L[ℂ] H => pairCoefficient F A (g : H) (k : H) ij)
    (actual_force_balance sharp m ell F g)
  rw [coefficient_sub,coefficient_smul,coefficient_sub] at h
  have hx : pairCoefficient F (sourceRead F g (fullInsertion sharp m ell)) (g : H) (k : H) ij-
      pairCoefficient F (solverOperator sharp m ell F) (g : H) (k : H) ij=
      gapCoefficient sharp m ell F g k ij := by
    have hv := congrArg (fun v : H => inner ℂ (k : H) v)
      (actual_oscillator_gap_inverse sharp m ell F g ij)
    exact (congrArg (fun c : ℂ => c-pairCoefficient F (solverOperator sharp m ell F) (g : H) (k : H) ij) hv).trans
      (inner_sub_right (k : H) _ _).symm
  exact h.trans (congrArg (fun c : ℂ => (oscillatorMass : ℂ)*c) hx)

/-- Clearing the positive oscillator mass is legitimate on all spectral collisions. -/
theorem actual_gap_coefficient_inverse (sharp : Bool) (m ell : ℕ) (F : Index) (g k : OriginalCore)
    (ij : Channel F × Channel F) :
    gapCoefficient sharp m ell F g k ij=(oscillatorMass : ℂ)⁻¹*
      (forceCoefficient sharp m ell F g k ij-endpointCoefficient sharp m ell F g k ij) := by
  rw [actual_gap_coefficient_balance,←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr mass_pos.ne'),one_mul]

def wholeGram (F : Index) (μ : ℝ) (u v : Channel F × Channel F → ℂ) : ℂ :=
  ∑ ij : Channel F × Channel F,∑ kl : Channel F × Channel F,
    closedKernel μ (channelValue F ij.1) (channelValue F ij.2)
      (channelValue F kl.1) (channelValue F kl.2)*inner ℂ (u ij) (v kl)

def pairEnergy (F : Index) (μ : ℝ) (A : H →L[ℂ] H) (g k : H) : ℝ :=
  (wholeGram F μ (pairCoefficient F A g k) (pairCoefficient F A g k)).re

def response (F : Index) (z : ℂ) (A : H →L[ℂ] H) (g k : H) : ℂ :=
  inner ℂ k (finiteResolvent F z (A (finiteResolvent F z g)))

private theorem wholeGram_sub (F : Index) (μ : ℝ) (u v : Channel F × Channel F → ℂ) :
    wholeGram F μ (u-v) (u-v)=wholeGram F μ u u+wholeGram F μ v v-
      wholeGram F μ u v-wholeGram F μ v u := by
  simp only [wholeGram,Pi.sub_apply,inner_sub_left,inner_sub_right,mul_sub,
    Finset.sum_sub_distrib]
  ring

private theorem wholeGram_scale (F : Index) (μ a : ℝ) (u : Channel F × Channel F → ℂ) :
    wholeGram F μ (fun ij => (a : ℂ)*u ij) (fun ij => (a : ℂ)*u ij)=
      (a^2 : ℝ)*wholeGram F μ u u := by
  unfold wholeGram
  simp only [←smul_eq_mul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kl _
  push_cast
  ring

/-- Original closedJointCost equals the full force/endpoints Gram, with both interference terms retained. -/
theorem actual_closed_cost_force_gram (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (g k : OriginalCore) :
    oscillatorMass^2*closedJointCost sharp m ell F μ (g : H) (k : H)=
      pairEnergy F μ (balancedForce sharp m ell F g) (g : H) (k : H)+
      pairEnergy F μ (doubleResponse sharp m ell F g) (g : H) (k : H)-
      (wholeGram F μ (forceCoefficient sharp m ell F g k) (endpointCoefficient sharp m ell F g k)).re-
      (wholeGram F μ (endpointCoefficient sharp m ell F g k) (forceCoefficient sharp m ell F g k)).re := by
  have hc := actual_closed_cost_gap sharp m ell F μ g k
  change _=(wholeGram F μ (gapCoefficient sharp m ell F g k) (gapCoefficient sharp m ell F g k)).re at hc
  have hb : forceCoefficient sharp m ell F g k-endpointCoefficient sharp m ell F g k=
      fun ij => (oscillatorMass : ℂ)*gapCoefficient sharp m ell F g k ij := by
    funext ij
    exact actual_gap_coefficient_balance sharp m ell F g k ij
  have h := wholeGram_sub F μ (forceCoefficient sharp m ell F g k) (endpointCoefficient sharp m ell F g k)
  rw [hb,wholeGram_scale] at h
  have hr := congrArg Complex.re h
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.add_re,Complex.sub_re] at hr
  rw [hc]
  exact hr

private theorem response_spectral (F : Index) (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : H) (t : ℝ) :
    response F (line μ t) A g k=
      ∑ ij : Channel F × Channel F,polePair μ (channelValue F ij.1) (channelValue F ij.2) t • pairCoefficient F A g k ij := by
  simp only [response,actual_two_leg_spectral F μ hμ A g t,inner_sum,inner_smul_right,smul_eq_mul,pairCoefficient]

/-- Integrability is produced at fixed F before any cofinal limit. -/
theorem actual_response_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : H) :
    Integrable (fun t : ℝ => ‖response F (line μ t) A g k‖^2) := by
  simp_rw [response_spectral F μ hμ A g k]
  exact finite_gram_integrable μ hμ _ _ _

/-- The whole closed Gram is the actual full-frequency energy of the literal same-F response. -/
theorem actual_response_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : H) :
    (∫ t : ℝ,‖response F (line μ t) A g k‖^2)=pairEnergy F μ A g k := by
  simp_rw [response_spectral F μ hμ A g k]
  rw [finite_gram_integral μ hμ]
  simp only [pairEnergy,wholeGram,four_pole_closed μ _ _ _ _ hμ]

private theorem response_sub (F : Index) (z : ℂ) (A B : H →L[ℂ] H) (g k : H) :
    response F z (A-B) g k=response F z A g k-response F z B g k := by
  simp only [response,sub_apply,map_sub,inner_sub_right]

private theorem joint_coefficient (sharp : Bool) (m ell : ℕ) (F : Index) (g k : OriginalCore)
    (ij : Channel F × Channel F) :
    pairCoefficient F (jointInsertion sharp m ell F) (g : H) (k : H) ij=
      gapCoefficient sharp m ell F g k ij := by
  rw [pairCoefficient,actual_joint_gap_leg]
  rfl

/-- The force balance returns to the original joint residual on the entire frequency line. -/
theorem actual_force_profile_return (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : OriginalCore) (t : ℝ) :
    response F (line μ t) (balancedForce sharp m ell F g) (g : H) (k : H)-
      response F (line μ t) (doubleResponse sharp m ell F g) (g : H) (k : H)=
    (oscillatorMass : ℂ)*jointResidual sharp m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g k := by
  rw [actual_joint_as_same_compression]
  change _=(oscillatorMass : ℂ)*response F (line μ t) (jointInsertion sharp m ell F) (g : H) (k : H)
  simp only [response_spectral F μ hμ,←Finset.sum_sub_distrib,Finset.mul_sum,smul_eq_mul,joint_coefficient]
  apply Finset.sum_congr rfl
  intro ij _
  have h := actual_gap_coefficient_balance sharp m ell F g k ij
  change _=(oscillatorMass : ℂ)*(_*gapCoefficient sharp m ell F g k ij)
  rw [←mul_sub_left_distrib]
  exact (congrArg (fun c : ℂ => polePair μ (channelValue F ij.1) (channelValue F ij.2) t*c) h).trans (by ring)

/-- Exact full-frequency commuting square: source force minus paid endpoints returns the original cost. -/
theorem actual_force_difference_energy (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : OriginalCore) :
    (∫ t : ℝ,‖response F (line μ t) (balancedForce sharp m ell F g) (g : H) (k : H)-
      response F (line μ t) (doubleResponse sharp m ell F g) (g : H) (k : H)‖^2)=
      oscillatorMass^2*closedJointCost sharp m ell F μ (g : H) (k : H) := by
  simp_rw [actual_force_profile_return sharp m ell F μ hμ g k,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos mass_pos]
  rw [integral_const_mul,actual_joint_closed_energy sharp m ell F μ hμ g k]

private theorem norm_sub_square {V : Type*} [SeminormedAddCommGroup V] (x y : V) :
    ‖x-y‖^2≤2*(‖x‖^2+‖y‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

/-- A direct sufficient energy budget consumes the source force and fixed-endpoint tails; no tail is a premise. -/
theorem actual_force_energy_bound (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : OriginalCore) :
    oscillatorMass^2*closedJointCost sharp m ell F μ (g : H) (k : H)≤
      2*(pairEnergy F μ (balancedForce sharp m ell F g) (g : H) (k : H)+
        pairEnergy F μ (doubleResponse sharp m ell F g) (g : H) (k : H)) := by
  rw [←actual_force_difference_energy sharp m ell F μ hμ g k]
  have hd := actual_response_integrable F μ hμ
    (balancedForce sharp m ell F g-doubleResponse sharp m ell F g) (g : H) (k : H)
  simp only [response_sub] at hd
  have hf := actual_response_integrable F μ hμ (balancedForce sharp m ell F g) (g : H) (k : H)
  have he := actual_response_integrable F μ hμ (doubleResponse sharp m ell F g) (g : H) (k : H)
  calc
    _≤∫ t : ℝ,2*(‖response F (line μ t) (balancedForce sharp m ell F g) (g : H) (k : H)‖^2+
        ‖response F (line μ t) (doubleResponse sharp m ell F g) (g : H) (k : H)‖^2) :=
      integral_mono hd ((hf.add he).const_mul 2) (fun _ => norm_sub_square _ _)
    _=_ := by rw [integral_const_mul,integral_add hf he,actual_response_energy F μ hμ,
      actual_response_energy F μ hμ]

/-- With the endpoint paid, the force budget is equivalent to the original cost, rather than a stronger moment target. -/
theorem actual_reverse_force_energy_bound (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : OriginalCore) :
    pairEnergy F μ (balancedForce sharp m ell F g) (g : H) (k : H)≤
      2*(oscillatorMass^2*closedJointCost sharp m ell F μ (g : H) (k : H)+
        pairEnergy F μ (doubleResponse sharp m ell F g) (g : H) (k : H)) := by
  rw [←actual_response_energy F μ hμ]
  have hd := actual_response_integrable F μ hμ
    (balancedForce sharp m ell F g-doubleResponse sharp m ell F g) (g : H) (k : H)
  simp only [response_sub] at hd
  have hf := actual_response_integrable F μ hμ (balancedForce sharp m ell F g) (g : H) (k : H)
  have he := actual_response_integrable F μ hμ (doubleResponse sharp m ell F g) (g : H) (k : H)
  have hp (t : ℝ) :
      ‖response F (line μ t) (balancedForce sharp m ell F g) (g : H) (k : H)‖^2≤
      2*(‖response F (line μ t) (balancedForce sharp m ell F g) (g : H) (k : H)-
          response F (line μ t) (doubleResponse sharp m ell F g) (g : H) (k : H)‖^2+
        ‖response F (line μ t) (doubleResponse sharp m ell F g) (g : H) (k : H)‖^2) := by
    simpa only [sub_neg_eq_add,sub_add_cancel,norm_neg] using norm_sub_square
      (response F (line μ t) (balancedForce sharp m ell F g) (g : H) (k : H)-
        response F (line μ t) (doubleResponse sharp m ell F g) (g : H) (k : H))
      (-response F (line μ t) (doubleResponse sharp m ell F g) (g : H) (k : H))
  calc
    _≤∫ t : ℝ,2*(‖response F (line μ t) (balancedForce sharp m ell F g) (g : H) (k : H)-
          response F (line μ t) (doubleResponse sharp m ell F g) (g : H) (k : H)‖^2+
        ‖response F (line μ t) (doubleResponse sharp m ell F g) (g : H) (k : H)‖^2) :=
      integral_mono hf ((hd.add he).const_mul 2) hp
    _=_ := by rw [integral_const_mul,integral_add hd he,
      actual_force_difference_energy sharp m ell F μ hμ g k,actual_response_energy F μ hμ]

end LowEnergy.SourceScalarForceBudget
