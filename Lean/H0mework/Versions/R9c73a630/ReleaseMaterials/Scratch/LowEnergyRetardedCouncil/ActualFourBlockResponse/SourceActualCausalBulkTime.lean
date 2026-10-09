import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceShiftedBulkTimeBudget
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointTail
import Lean.Elab.Term

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualCausalBulkTime
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceBulkTwoTime SourceBulkParseval SourceInverseNoetherChannelGap SourceInverseNoetherEnergy
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarPositiveBulkWard
open SourceScalarInverseNativeEnergy SourceScalarOscillatorAbsorption SourceScalarPairedTransport
open SourceMovingJetFlux SourceEscapeCurrent GaussNativeEnergy SourceQuantumScalarChart
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open SourceBulkTimeBalance SourceScalarShiftedBulk SourceShiftedBulkTimeBudget ActualVectorJointCost
open Lean Meta Elab Term
open scoped Topology InnerProductSpace BigOperators ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair bulkAction compressionCore raisedNoetherCurrent inverseForm coreTime

elab "paid_bulk_time%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceBulkTimeBalance 0) "LowEnergy") "SourceBulkTimeBalance"
  let name := Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing original bulk-time payment"
  mkConstWithFreshMVarLevels name

def direction (advanced : Bool) : ℝ := if advanced then -1 else 1
private theorem direction_false : direction false=1 := rfl
private theorem direction_true : direction true= -1 := rfl

def causalCoreTime (advanced : Bool) (F : Index) (g : diagonal.domain) (t : ℝ) : QuantumTest :=
  coreTime F g (direction advanced*t)

def causalTimeEnergy (advanced : Bool) (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) : ℝ :=
  ∫t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*inverseForm (T (causalCoreTime advanced F g t))

def causalNormTime (advanced : Bool) (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) : ℝ :=
  ∫t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*‖embed (T (causalCoreTime advanced F g t))‖^2

/-- Time reflection preserves the original compression and its entire raised defect. -/
def causalRemainingTime (advanced : Bool) (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) : ℝ :=
  ∫t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*(direction advanced*remainingRaised F T (causalCoreTime advanced F g t))

private def value (advanced : Bool) (F : Index) (i : Channel F) : ℝ :=
  direction advanced*channelValue F i
private def coefficient (F : Index) (g : diagonal.domain) (A B : End) (i j : Channel F) : ℂ :=
  sourcePair (A (channelTest F g i)) (B (channelTest F g j))
private def frequencySum (advanced : Bool) (F : Index) (μ : ℝ)
    (c : Channel F → Channel F → ℂ) (w : ℝ) : ℂ :=
  ∑i,∑j,star (pole μ (value advanced F i) w)*pole μ (value advanced F j) w*c i j
private def timeSum (advanced : Bool) (F : Index) (μ : ℝ)
    (c : Channel F → Channel F → ℂ) (t : ℝ) : ℂ :=
  ∑i,∑j,Complex.exp (-gap μ (value advanced F i) (value advanced F j)*(t : ℂ))*c i j
private def gapCoefficient (F : Index) (T : End) (g : diagonal.domain) (i j : Channel F) : ℂ :=
  (Complex.I/2)*((channelValue F i : ℂ)-(channelValue F j : ℂ))*coefficient F g T (bulkAction*T) i j

private theorem nonreal (advanced : Bool) (μ w : ℝ) (hμ : 0<μ) :
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

private theorem core_channels (advanced : Bool) (F : Index) (g : diagonal.domain) (t : ℝ) :
    causalCoreTime advanced F g t=∑i,phase (value advanced F i) t • channelTest F g i := by
  unfold causalCoreTime coreTime
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold phase value
  congr 1
  push_cast
  ring

private theorem pair_sum (F : Index) (g : diagonal.domain) (A B : End) (c : Channel F → ℂ) :
    sourcePair (A (∑i,c i • channelTest F g i)) (B (∑j,c j • channelTest F g j))=
      ∑i,∑j,star (c i)*c j*coefficient F g A B i j := by
  exact (paid_bulk_time% pair_sum) F g A B c

private theorem pole_reflect (μ a w : ℝ) : pole (-μ) a w= -pole μ (-a) (-w) := by
  unfold pole line
  have h : (a : ℂ)-((w : ℂ)+((-μ : ℝ):ℂ)*Complex.I)=
      -(((-a : ℝ):ℂ)-(((-w : ℝ):ℂ)+(μ : ℂ)*Complex.I)) := by push_cast;ring
  rw [h,inv_neg]

private theorem frequency_value (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (A B : End) (w : ℝ) :
    frequencySum advanced F μ (coefficient F g A B) (direction advanced*w)=
      sourcePair (A (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g))
        (B (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g)) := by
  rw [actual_state_channels,pair_sum]
  cases advanced
  · change frequencySum false F μ (coefficient F g A B) (direction false*w)=
      ∑i,∑j,star (pole μ (channelValue F i) w)*pole μ (channelValue F j) w*coefficient F g A B i j
    simp only [frequencySum,value,direction_false,one_mul]
  · change frequencySum true F μ (coefficient F g A B) (direction true*w)=
      ∑i,∑j,star (pole (-μ) (channelValue F i) w)*pole (-μ) (channelValue F j) w*coefficient F g A B i j
    simp only [frequencySum,value,direction_true,neg_one_mul,pole_reflect,star_neg,neg_mul_neg]

private theorem time_factor (μ a b t : ℝ) :
    Complex.exp (-gap μ a b*(t : ℂ))=(Real.exp (-2*μ*t) : ℂ)*star (phase a t)*phase b t := by
  exact (paid_bulk_time% time_factor) μ a b t

private theorem pair_time (advanced : Bool) (F : Index) (μ : ℝ) (g : diagonal.domain)
    (A B : End) (t : ℝ) :
    timeSum advanced F μ (coefficient F g A B) t=(Real.exp (-2*μ*t) : ℂ)*
      sourcePair (A (causalCoreTime advanced F g t)) (B (causalCoreTime advanced F g t)) := by
  unfold timeSum
  simp_rw [time_factor]
  rw [core_channels,pair_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem decay_integrable (μ a b : ℝ) (hμ : 0<μ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-gap μ a b*(t : ℂ))) (Set.Ioi 0) :=
  (paid_bulk_time% decay_integrable) μ a b hμ
private theorem decay_integral (μ a b : ℝ) (hμ : 0<μ) :
    (∫t : ℝ in Set.Ioi 0,Complex.exp (-gap μ a b*(t : ℂ)))=(gap μ a b)⁻¹ :=
  (paid_bulk_time% decay_integral) μ a b hμ

private theorem frequency_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (c : Channel F → Channel F → ℂ) : Integrable (frequencySum advanced F μ c) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (two_pole_integrable μ (value advanced F i) (value advanced F j) hμ).mul_const _))
private theorem sum_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (c : Channel F → Channel F → ℂ) : IntegrableOn (timeSum advanced F μ c) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (value advanced F i) (value advanced F j) hμ).mul_const _))
private theorem sum_integral (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (c : Channel F → Channel F → ℂ) :
    (∫t : ℝ in Set.Ioi 0,timeSum advanced F μ c t)=
      ∑i,∑j,(gap μ (value advanced F i) (value advanced F j))⁻¹*c i j := by
  unfold timeSum
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (value advanced F i) (value advanced F j) hμ).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (decay_integrable μ (value advanced F i) (value advanced F j) hμ).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const,decay_integral μ _ _ hμ]

private theorem frequency_time (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (c : Channel F → Channel F → ℂ) :
    (∫w : ℝ,frequencySum advanced F μ c w)=(2*Real.pi : ℂ)*(∫t : ℝ in Set.Ioi 0,timeSum advanced F μ c t) := by
  rw [sum_integral advanced F μ hμ]
  unfold frequencySum
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (two_pole_integrable μ (value advanced F i) (value advanced F j) hμ).mul_const _)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (two_pole_integrable μ (value advanced F i) (value advanced F j) hμ).mul_const _),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const]
  change twoPole μ (value advanced F i) (value advanced F j)*_=_
  rw [two_pole_closed μ _ _ hμ]
  ring

private theorem pair_parseval (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (A B : End) :
    Integrable (fun w : ℝ => sourcePair
      (A (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g))
      (B (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g))) ∧
    IntegrableOn (fun t : ℝ => (Real.exp (-2*μ*t) : ℂ)*sourcePair
      (A (causalCoreTime advanced F g t)) (B (causalCoreTime advanced F g t))) (Set.Ioi 0) ∧
    (∫w : ℝ,sourcePair
      (A (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g))
      (B (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g)))=
      (2*Real.pi : ℂ)*(∫t : ℝ in Set.Ioi 0,(Real.exp (-2*μ*t) : ℂ)*sourcePair
        (A (causalCoreTime advanced F g t)) (B (causalCoreTime advanced F g t))) := by
  have hf := frequency_integrable advanced F μ hμ (coefficient F g A B)
  have ht := sum_integrable advanced F μ hμ (coefficient F g A B)
  have hfi : Integrable (fun w : ℝ => frequencySum advanced F μ (coefficient F g A B) (direction advanced*w)) := by
    cases advanced
    · simpa only [direction_false,one_mul] using hf
    · simpa only [direction_true,neg_one_mul] using hf.comp_neg
  have he : (∫w : ℝ,frequencySum advanced F μ (coefficient F g A B) (direction advanced*w))=
      ∫w : ℝ,frequencySum advanced F μ (coefficient F g A B) w := by
    cases advanced
    · simp only [direction_false,one_mul]
    · simpa only [direction_true,neg_one_mul] using integral_neg_eq_self (frequencySum true F μ (coefficient F g A B)) volume
  refine ⟨hfi.congr (Eventually.of_forall (frequency_value advanced F μ hμ g A B)),
    ht.congr (Eventually.of_forall (pair_time advanced F μ g A B)),?_⟩
  simp_rw [←frequency_value advanced F μ hμ g A B,←pair_time advanced F μ g A B]
  rw [he,frequency_time advanced F μ hμ]

/-- Both physical causal lines return their own original signed-time bulk. -/
theorem actual_causal_bulk_parseval (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => inverseForm (T (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g))) ∧
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*inverseForm (T (causalCoreTime advanced F g t))) (Set.Ioi 0) ∧
    (∫w : ℝ,inverseForm (T (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g)))=
      2*Real.pi*causalTimeEnergy advanced F μ T g := by
  obtain ⟨hf,ht,he⟩ := pair_parseval advanced F μ hμ g T (bulkAction*T)
  have hv (q : QuantumTest) : (sourcePair (T q) ((bulkAction*T) q)).re=inverseForm (T q) := original_bulk_energy _
  have htv (t : ℝ) : ((Real.exp (-2*μ*t) : ℂ)*sourcePair
      (T (causalCoreTime advanced F g t)) ((bulkAction*T) (causalCoreTime advanced F g t))).re=
      Real.exp (-2*μ*t)*inverseForm (T (causalCoreTime advanced F g t)) := by
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hv]
  refine ⟨hf.re.congr (Eventually.of_forall (fun w => hv _)),ht.re.congr (Eventually.of_forall htv),?_⟩
  have h := congrArg Complex.re he
  have hr1 : (∫w : ℝ,sourcePair
      (T (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g))
      ((bulkAction*T) (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g))).re=
      ∫w : ℝ,(sourcePair
        (T (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g))
        ((bulkAction*T) (state F (causalFrequency advanced μ w) (nonreal advanced μ w hμ) g))).re :=
    (integral_re hf).symm
  have hr2 : (∫t : ℝ in Set.Ioi 0,(Real.exp (-2*μ*t) : ℂ)*sourcePair
      (T (causalCoreTime advanced F g t)) ((bulkAction*T) (causalCoreTime advanced F g t))).re=
      ∫t : ℝ in Set.Ioi 0,((Real.exp (-2*μ*t) : ℂ)*sourcePair
        (T (causalCoreTime advanced F g t)) ((bulkAction*T) (causalCoreTime advanced F g t))).re :=
    (integral_re ht).symm
  rw [hr1,Complex.mul_re,show (2*Real.pi : ℂ).re=2*Real.pi by simp,
    show (2*Real.pi : ℂ).im=0 by simp,zero_mul,sub_zero,hr2] at h
  simpa only [hv,htv,causalTimeEnergy] using h

end LowEnergy.ActualCausalBulkTime
