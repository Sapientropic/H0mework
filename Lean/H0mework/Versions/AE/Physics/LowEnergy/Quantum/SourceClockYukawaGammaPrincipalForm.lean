import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaGammaPrincipal
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaJointRadialZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaGammaPrincipalForm
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussQuantumMultiplier GaussNativePotential
open GaussFockWeights GaussDensityCore GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceInverseNeutralSpinCurrent
open SourceClockYukawaSpinClosure SourceClockYukawaSpinJointForce SourceClockYukawaGammaPrincipal
open SourceClockYukawaRadialJoinedHessian SourceClockYukawaRadialNativeHessian SourceNativeCoframeCompatibility
open SourceClockYukawaJointRadialZero
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourcePhysicalKineticSquare
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] fullAction

private theorem gamma_true_pair (p q : QuantumTest) :
    sourcePair p (gammaAction true q)=sourcePair (gammaAction false p) q := by
  rw [sourcePair_integral,sourcePair_integral]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change inner ℂ (GaussFockWeights.weight (fun N => complexDensity N x) (p x))
    ((sourceMap (gammaGradient x)).adjoint (q x))=
      inner ℂ (GaussFockWeights.weight (fun N => complexDensity N x) (sourceMap (gammaGradient x) (p x))) (q x)
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hc : Commute (GaussFockWeights.weight (fun N => complexDensity N x)) (sourceMap (gammaGradient x)) := by
    rw [source_map_return]
    exact weight_commute _ _
  exact congrArg (fun v : FockFiber => inner ℂ v (q x))
    (congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (p x)) hc.eq).symm

private theorem gamma_base_pair (sharp : Bool) : GaussCoframeForm.Paired (gammaAction sharp) (gammaAction (!sharp)) := by
  intro p q
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (gamma_true_pair q p)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact gamma_true_pair p q

private theorem bracket_pair (J A B : End) (hJ : GaussCoframeForm.Paired J J)
    (hAB : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired (bracket J A) (-bracket J B) := by
  intro p q
  have h1 := hJ p (A q)
  have h2 := hAB (J p) q
  have h3 := hAB p (J q)
  have h4 := hJ (B p) q
  simp only [bracket,LinearMap.sub_apply,LinearMap.neg_apply,Module.End.mul_apply,
    sourcePair,map_sub,map_neg,inner_sub_right,inner_sub_left,inner_neg_left] at *
  linear_combination h1+h2-h3-h4

private theorem paired_symm {A B : End} (h : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired B A := by
  intro p q
  have h' := congrArg (starRingEnd ℂ) (h q p)
  simpa only [sourcePair,inner_conj_symm] using h'.symm

private theorem active_pair (j : Fin 4) : GaussCoframeForm.Paired (activeSpin j) (activeSpin j) :=
  GaussCoframeSpin.current_pair (activeIndex j)

private def sign (mu : Fin 8) : ℂ := if 0 < mu.val ∧ mu.val < 5 then -1 else 1

def gammaDagger (sharp : Bool) (mu : Fin 8) : End := sign mu • gammaCore (!sharp) mu

private theorem gamma_recipe (sharp : Bool) (mu : Fin 8) : gammaCore sharp mu=
    if h0 : mu.val=0 then gammaAction sharp else
    if h1 : mu.val<5 then bracket (activeSpin ⟨mu.val-1,by omega⟩) (gammaAction sharp) else
      bracket (activeSpin ⟨mu.val-5,by omega⟩) (bracket (activeSpin 3) (gammaAction sharp)) := by
  fin_cases mu <;> rfl

private theorem double_pair (j : Fin 4) (A B : End) (hAB : GaussCoframeForm.Paired A B) :
    GaussCoframeForm.Paired (bracket (activeSpin j) (bracket (activeSpin 3) A))
      (bracket (activeSpin j) (bracket (activeSpin 3) B)) := by
  have h1 := bracket_pair (activeSpin 3) A B (active_pair 3) hAB
  have h2 := bracket_pair (activeSpin j) (bracket (activeSpin 3) A)
    (-bracket (activeSpin 3) B) (active_pair j) h1
  have he : -bracket (activeSpin j) (-bracket (activeSpin 3) B)=
      bracket (activeSpin j) (bracket (activeSpin 3) B) := by unfold bracket;noncomm_ring
  rw [he] at h2
  exact h2

/-- The actual gamma coefficient has the same source adjoint parity as the original eight K coefficients. -/
theorem original_gamma_core_pair (sharp : Bool) (mu : Fin 8) :
    GaussCoframeForm.Paired (gammaCore sharp mu) (gammaDagger sharp mu) := by
  unfold gammaDagger
  rw [gamma_recipe,gamma_recipe]
  by_cases h0 : mu.val=0
  · have hs : sign mu=1 := by simp [sign,h0]
    simpa [h0,hs] using gamma_base_pair sharp
  · by_cases h1 : mu.val<5
    · have hp : 0 < mu.val := Nat.pos_of_ne_zero h0
      have hs : sign mu=-1 := by simp [sign,hp,h1]
      simpa [h0,h1,hs] using bracket_pair (activeSpin ⟨mu.val-1,by omega⟩)
        (gammaAction sharp) (gammaAction (!sharp)) (active_pair _) (gamma_base_pair sharp)
    · have hs : sign mu=1 := by unfold sign;rw [if_neg (by omega)]
      simpa [h0,h1,hs] using double_pair ⟨mu.val-5,by omega⟩
        (gammaAction sharp) (gammaAction (!sharp)) (gamma_base_pair sharp)

private theorem full_pair (sharp : Bool) : GaussCoframeForm.Paired (fullAction sharp) (fullAction (!sharp)) := by
  intro p q
  unfold SourceMixedNativeReturn.fullAction
  cases sharp
  · change sourcePair p (GaussYukawaOperator.originalAction q)=sourcePair (GaussFullHamiltonian.adjointAction p) q
    have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair q p)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using h.symm
  · change sourcePair p (GaussFullHamiltonian.adjointAction q)=sourcePair (GaussYukawaOperator.originalAction p) q
    exact GaussFullHamiltonian.yukawa_pair p q

private theorem dagger_return (sharp : Bool) (mu : Fin 8) :
    daggerCoefficient sharp mu=sign mu • spinClosureCoefficient (!sharp) mu := rfl

private theorem coefficient_pair (sharp : Bool) (mu : Fin 8) :
    GaussCoframeForm.Paired (spinClosureCoefficient sharp mu) (daggerCoefficient sharp mu) := by
  rw [dagger_return]
  unfold spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient
  by_cases h0 : mu.val=0
  · have hs : sign mu=1 := by simp [sign,h0]
    simpa [h0,hs] using full_pair sharp
  · by_cases h1 : mu.val<5
    · have hp : 0 < mu.val := Nat.pos_of_ne_zero h0
      have hs : sign mu=-1 := by simp [sign,hp,h1]
      simpa [h0,h1,hs,spinVariation] using bracket_pair (activeSpin ⟨mu.val-1,by omega⟩)
        (fullAction sharp) (fullAction (!sharp)) (active_pair _) (full_pair sharp)
    · have hs : sign mu=1 := by unfold sign;rw [if_neg (by omega)]
      simpa [h0,h1,hs,spinVariation] using double_pair ⟨mu.val-5,by omega⟩
        (fullAction sharp) (fullAction (!sharp)) (full_pair sharp)

def gammaPrincipalCore : End := ∑ mu : Fin 8,
  (bracket (daggerCoefficient false mu) (gammaCore false mu)+
    bracket (spinClosureCoefficient false mu) (gammaDagger false mu))

private theorem row_pair (A A' B B' : End) (hA : GaussCoframeForm.Paired A A')
    (hB : GaussCoframeForm.Paired B B') (u : QuantumTest) :
    (sourcePair u ((bracket A' B+bracket A B') u)).im=
      2*(sourcePair (A u) (B u)+sourcePair (A' u) (B' u)).im := by
  have h1 := paired_symm hA u (B u)
  have h2 := hB u (A' u)
  have h3 := hA u (B' u)
  have h4 := paired_symm hB u (A u)
  change (sourcePair u ((A' (B u)-B (A' u))+(A (B' u)-B' (A u)))).im=_
  simp only [sourcePair,map_add,map_sub,inner_add_right,inner_sub_right] at *
  rw [h1,h2,h3,h4]
  have hc (p q : QuantumTest) : (inner ℂ (embed p) (embed q)).im=-(inner ℂ (embed q) (embed p)).im := by
    simpa only [Complex.conj_im] using
      (congrArg Complex.im (inner_conj_symm (embed p) (embed q))).symm
  change _=2*(inner ℂ (embed (A u)) (embed (B u))+inner ℂ (embed (A' u)) (embed (B' u))).im
  simp only [Complex.add_im,Complex.sub_im]
  rw [hc (B' u) (A' u),hc (B u) (A u)]
  ring

private theorem true_pair (mu : Fin 8) (u : QuantumTest) :
    sourcePair (spinClosureCoefficient true mu u) (gammaCore true mu u)=
      sourcePair (daggerCoefficient false mu u) (gammaDagger false mu u) := by
  rw [dagger_return]
  unfold gammaDagger
  by_cases h : 0 < mu.val ∧ mu.val < 5
  · have hs : sign mu=-1 := by unfold sign;rw [if_pos h]
    simp only [hs,Bool.not_false,neg_one_smul,LinearMap.neg_apply,sourcePair,map_neg,
      inner_neg_left,inner_neg_right,neg_neg]
  · have hs : sign mu=1 := by unfold sign;rw [if_neg h]
    simp only [hs,Bool.not_false,one_smul]

/-- The original Number-weighted full source pairing consumes the same two branches before clipping. -/
theorem original_gamma_principal_form (u : QuantumTest) :
    2*(∑ mu : Fin 8,(sourcePair (spinClosureCoefficient false mu u) (gammaCore false mu u)+
      sourcePair (spinClosureCoefficient true mu u) (gammaCore true mu u))).im=
      (sourcePair u (gammaPrincipalCore u)).im := by
  unfold gammaPrincipalCore
  simp only [LinearMap.sum_apply,sourcePair,map_sum,inner_sum,Complex.im_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [show inner ℂ (embed (spinClosureCoefficient true mu u)) (embed (gammaCore true mu u))=
      sourcePair (daggerCoefficient false mu u) (gammaDagger false mu u) from true_pair mu u]
  exact (row_pair _ _ _ _ (coefficient_pair false mu) (original_gamma_core_pair false mu) u).symm

/-- Actual global coherent states retain precisely their gamma-weighted fixed error. -/
theorem actual_joint_gamma_principal_form (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (∑ mu : Fin 8,(sourcePair (jointState false m ell F z hz g mu)
        (gammaCore false mu (windowState m ell F z hz g))+
      sourcePair (jointState true m ell F z hz g mu)
        (gammaCore true mu (windowState m ell F z hz g)))).im=
      (1/2:ℝ)*(sourcePair (windowState m ell F z hz g)
        (gammaPrincipalCore (windowState m ell F z hz g))).im-
      (∑ mu : Fin 8,(sourcePair (errorColumn false m ell F z hz g mu)
          (gammaCore false mu (windowState m ell F z hz g))+
        sourcePair (errorColumn true m ell F z hz g mu)
          (gammaCore true mu (windowState m ell F z hz g)))).im := by
  have hp := original_gamma_principal_form (windowState m ell F z hz g)
  simp only [jointState,coherentColumn,sourcePair,map_sub,inner_sub_left,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Complex.add_im,Complex.sub_im] at *
  linarith only [hp]

private theorem inverse_at (f : QuantumTest) (x : SourceCoordinateSlice) :
    inverseVolumeAction f x=(reciprocalVolume x:ℂ) • f x := rfl

private theorem inverse_pair (p q : QuantumTest) :
    sourcePair p (inverseVolumeAction q)=sourcePair (inverseVolumeAction p) q := by
  unfold inverseVolumeAction
  exact multiply_pair _ _ _ _

private theorem inverse_gamma (sharp : Bool) (mu : Fin 8) : Commute inverseVolumeAction (gammaCore sharp mu) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change inverseVolumeAction (gammaCore sharp mu f) x=gammaCore sharp mu (inverseVolumeAction f) x
  rw [inverse_at,original_gamma_core_point,original_gamma_core_point,inverse_at]
  exact (map_smul _ _ _).symm

private theorem inverse_gamma_dagger (sharp : Bool) (mu : Fin 8) :
    Commute inverseVolumeAction (gammaDagger sharp mu) :=
  (inverse_gamma (!sharp) mu).smul_right _

def weightedGamma (sharp : Bool) (mu : Fin 8) : End := inverseVolumeAction*gammaCore sharp mu
def weightedGammaDagger (sharp : Bool) (mu : Fin 8) : End := inverseVolumeAction*gammaDagger sharp mu

private theorem weighted_gamma_pair (sharp : Bool) (mu : Fin 8) :
    GaussCoframeForm.Paired (weightedGamma sharp mu) (weightedGammaDagger sharp mu) := by
  intro p q
  unfold weightedGamma weightedGammaDagger
  change sourcePair p (inverseVolumeAction (gammaCore sharp mu q))=
    sourcePair (inverseVolumeAction (gammaDagger sharp mu p)) q
  rw [inverse_pair,original_gamma_core_pair sharp mu]
  exact congrArg (fun f : QuantumTest => sourcePair f q)
    (LinearMap.congr_fun (inverse_gamma_dagger sharp mu).eq p).symm

def weightedGammaPrincipalCore : End := ∑ mu : Fin 8,
  (bracket (daggerCoefficient false mu) (weightedGamma false mu)+
    bracket (spinClosureCoefficient false mu) (weightedGammaDagger false mu))

private theorem weighted_dagger_return (sharp : Bool) (mu : Fin 8) :
    weightedGammaDagger sharp mu=sign mu • weightedGamma (!sharp) mu := by
  unfold weightedGammaDagger gammaDagger weightedGamma
  exact mul_smul_comm _ _ _

private theorem weighted_true_pair (mu : Fin 8) (u : QuantumTest) :
    sourcePair (spinClosureCoefficient true mu u) (weightedGamma true mu u)=
      sourcePair (daggerCoefficient false mu u) (weightedGammaDagger false mu u) := by
  rw [dagger_return,weighted_dagger_return]
  by_cases h : 0 < mu.val ∧ mu.val < 5
  · have hs : sign mu=-1 := by unfold sign;rw [if_pos h]
    simp only [hs,Bool.not_false,neg_one_smul,LinearMap.neg_apply,sourcePair,map_neg,
      inner_neg_left,inner_neg_right,neg_neg]
  · have hs : sign mu=1 := by unfold sign;rw [if_neg h]
    simp only [hs,Bool.not_false,one_smul]

private theorem weighted_main (u : QuantumTest) :
    2*(∑ mu : Fin 8,(sourcePair (spinClosureCoefficient false mu u) (weightedGamma false mu u)+
      sourcePair (spinClosureCoefficient true mu u) (weightedGamma true mu u))).im=
      (sourcePair u (weightedGammaPrincipalCore u)).im := by
  unfold weightedGammaPrincipalCore
  simp only [LinearMap.sum_apply,sourcePair,map_sum,inner_sum,Complex.im_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [show inner ℂ (embed (spinClosureCoefficient true mu u)) (embed (weightedGamma true mu u))=
      sourcePair (daggerCoefficient false mu u) (weightedGammaDagger false mu u) from weighted_true_pair mu u]
  exact (row_pair _ _ _ _ (coefficient_pair false mu) (weighted_gamma_pair false mu) u).symm

def gammaWeightedError (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℂ := ∑ mu : Fin 8,
  (sourcePair (errorColumn false m ell F z hz g mu) (gammaWord false m ell F z hz g mu)+
    sourcePair (errorColumn true m ell F z hz g mu) (gammaWord true m ell F z hz g mu))

/-- The actual full gammaWord returns to its source principal, with its full weighted endpoint kept. -/
theorem actual_joint_gamma_word_form (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    (∑ mu : Fin 8,(sourcePair (jointState false m ell F z hz g mu) (gammaWord false m ell F z hz g mu)+
      sourcePair (jointState true m ell F z hz g mu) (gammaWord true m ell F z hz g mu))).im=
      (sourceTime 0/4)*(sourcePair (windowState m ell F z hz g)
        (weightedGammaPrincipalCore (windowState m ell F z hz g))).im-
      (gammaWeightedError m ell F z hz g).im := by
  have hp := weighted_main (windowState m ell F z hz g)
  have hw (sharp : Bool) (mu : Fin 8) : gammaWord sharp m ell F z hz g mu=
      ((sourceTime 0:ℂ)/2) • weightedGamma sharp mu (windowState m ell F z hz g) := rfl
  simp_rw [hw]
  unfold gammaWeightedError
  simp_rw [hw]
  simp only [jointState,coherentColumn,sourcePair,map_smul,map_sub,inner_sub_left,inner_smul_right,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at *
  have hn : (sourceTime 0:ℂ)/2=((sourceTime 0/2:ℝ):ℂ) := by push_cast;rfl
  simp_rw [hn]
  simp only [Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero] at *
  linear_combination (sourceTime 0/4)*hp

end LowEnergy.SourceClockYukawaGammaPrincipalForm
