import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarInverseEnergyBudget
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceHardyRetardedTail
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeNeutralRemainderClosed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarSignedInverseReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolumeCurrent GaussYukawaCoefficient
open SourceCoframeDilation SourceDilationAlgebra SourceDilationKinetic SourceDilationRemainder
open SourceHamiltonianScaleJet SourceKineticTranspose SourceEulerCore SourceGaugeCoframeJets
open SourceInverseHamiltonianForceReduction SourceScalarPairedTransport SourceGaugeCoframeWard
open SourceInverseFirstCurrentGaugeJets SourceInverseCoframeNeutralSplice FullYSourceResolventGraphSplice SourceScalarForceBudget SourceJointScaleBudget
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction sourceRead defectAction compressionCore
  SourceMixedNativeReturn.thetaAction SourceScalarDoubleCurrent.fullInsertion
  scalarNeutral scalarCurrent radialCurrent coframeReducedRemainder scalarReducedRemainder
  cubic scaleDerivative kineticMinus localAction

open SourceInverseNeutralSpinTail SourceInverseCoframeNeutralBudget SourceScalarInverseEnergyBudget
open SourceResolventBandLimit SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy SourceGammaNativeBudget SourceHardyRetardedTail MeasureTheory Filter

private theorem origin_conjugate (A : Op) : (mixedHilbert 0 0).conjStarAlgEquiv A=A := by
  have hu (x : H) : mixedHilbert 0 0 x=x := by
    simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
      SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_zero]
  apply ContinuousLinearMap.ext
  intro x
  change mixedHilbert 0 0 (A ((mixedHilbert 0 0).symm x))=A x
  have hi : (mixedHilbert 0 0).symm x=x := by
    apply (mixedHilbert 0 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hu]
  rw [hi,hu]

private theorem sandwich_origin (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) :
    sandwichJet F g z A 0 0 0 0=finiteResolvent F z*sourceRead F g A*finiteResolvent F z := by
  unfold sandwichJet
  change resolventJet F z 0 0 0 0*(readOrbitJet F g A 0 0 0 0*resolventJet F z 0 0 0 0)=_
  have hr := (actual_mixed_resolvent F z hz 0 0).trans (origin_conjugate _)
  have ha := (actual_read_orbit F g A 0 0).trans (origin_conjugate _)
  exact (congrArg₂ (fun r a : Op => r*(a*r)) hr ha).trans (mul_assoc _ _ _).symm


private theorem sandwich_sub (F : Index) (seed : diagonal.domain) (z : ℂ) (A B : End) (n : ℕ) (s : ℝ) :
    sandwichJet F seed z (A-B) n 0 s 0=sandwichJet F seed z A n 0 s 0-sandwichJet F seed z B n 0 s 0 := by
  induction n generalizing s with
  | zero =>
    have hr := congrArg (fun C : Op => resolventJet F z 0 0 s 0*(C*resolventJet F z 0 0 s 0))
      ((actual_read_orbit F seed (A-B) s 0).trans (by rw [map_sub,map_sub]))
    have ha := congrArg (fun C : Op => resolventJet F z 0 0 s 0*(C*resolventJet F z 0 0 s 0)) (actual_read_orbit F seed A s 0)
    have hb := congrArg (fun C : Op => resolventJet F z 0 0 s 0*(C*resolventJet F z 0 0 s 0)) (actual_read_orbit F seed B s 0)
    simp only [mul_sub,sub_mul] at hr
    unfold sandwichJet
    exact hr.trans (congrArg₂ (·-·) ha.symm hb.symm)
  | succ n ih =>
    have hd := (sandwich_coframe_derivative F seed z A n 0 s 0).sub (sandwich_coframe_derivative F seed z B n 0 s 0)
    exact (sandwich_coframe_derivative F seed z (A-B) n 0 s 0).unique
      (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall ih))


private theorem inverse_cross_small (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0)
    (A : End) (n : ℕ) (hn : n ≤ 3) :
    inverseCross F seed z A n 0=sandwichJet F seed z A n 0 0 0-
      finiteResolvent F z*readOrbitJet F seed A n 0 0 0*finiteResolvent F z := by
  interval_cases n <;> simp only [inverseCross,resolved_inverse_return F z hz,sandwichJet] <;> rfl

private theorem read_coframe_rest (F : Index) (seed : diagonal.domain) (A : End) :
    sourceRead F seed (cubic A-(48 : ℂ) • A)=coframeRest (fun a => readOrbitJet F seed A a 0 0 0)-
      coframeRest (fun a => inputFlux F seed A a 0) := by
  simp only [coframeRest,inputFlux,coreJet,cubic,pow_zero,pow_succ,Module.End.one_apply,Module.End.mul_apply,
    LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,map_add,map_sub,map_smul]
  module

private theorem rest_split {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S1 S2 S3 R1 R2 R3 I1 I2 I3 Z1 Z2 Z3 T : V}
    (h1 : I1=S1-R1) (h2 : I2=S2-R2) (h3 : I3=S3-R3)
    (hT : T=R3+(12 : ℂ) • R2+(44 : ℂ) • R1-(Z3+(12 : ℂ) • Z2+(44 : ℂ) • Z1)) :
    S3+(12 : ℂ) • S2+(44 : ℂ) • S1=T+((I3+Z3)+(12 : ℂ) • (I2+Z2)+(44 : ℂ) • (I1+Z1)) := by
  rw [h1,h2,h3,hT]
  module

private def sourceCorrection (F : Index) (seed : diagonal.domain) (z : ℂ) (A : End) (a : ℕ) : Op :=
  inverseCross F seed z A a 0+finiteResolvent F z*inputFlux F seed A a 0*finiteResolvent F z

private theorem current_rest (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) :
    coframeRest (fun a => sandwichJet F seed z A a 0 0 0)=
      finiteResolvent F z*sourceRead F seed (cubic A-(48 : ℂ) • A)*finiteResolvent F z+
        coframeRest (sourceCorrection F seed z A) := by
  have h1 := inverse_cross_small F seed z hz A 1 (by omega)
  have h2 := inverse_cross_small F seed z hz A 2 (by omega)
  have h3 := inverse_cross_small F seed z hz A 3 (by omega)
  have hr := congrArg (fun C : Op => finiteResolvent F z*C*finiteResolvent F z) (read_coframe_rest F seed A)
  simp only [coframeRest,mul_sub,sub_mul,mul_add,add_mul,mul_smul_comm,smul_mul_assoc] at hr
  exact rest_split h1 h2 h3 hr

private theorem commutator_sub {R : Type*} [Ring R] (A B X : R) :
    bracket (A-B) X=bracket A X-bracket B X := by unfold bracket;noncomm_ring

private theorem commutator_add {R : Type*} [Ring R] (A X Y : R) :
    bracket A (X+Y)=bracket A X+bracket A Y := by unfold bracket;noncomm_ring

private def currentWord (F : Index) (seed : diagonal.domain) (z : ℂ) (Q : End) : Op :=
  -(1/48 : ℂ) • coframeCubic (fun a => sandwichJet F seed z (bracket (defectAction F) Q) a 0 0 0)+
    (1/48 : ℂ) • coframeRest (sourceCorrection F seed z (bracket diagonalAction Q))

private theorem collect_response {V : Type*} [AddCommGroup V] [Module ℂ V]
    (J0 J1 J2 J3 H0 H1 H2 H3 C0 C1 C2 C3 Corr T : V)
    (h0 : J0=H0-C0) (h1 : J1=H1-C1) (h2 : J2=H2-C2) (h3 : J3=H3-C3)
    (hr : H3+(12 : ℂ) • H2+(44 : ℂ) • H1=T-(48 : ℂ) • H0+Corr) :
    -(1/48 : ℂ) • (J3+(12 : ℂ) • J2+(44 : ℂ) • J1+(48 : ℂ) • J0)+(1/48 : ℂ) • Corr=
      (1/48 : ℂ) • (C3+(12 : ℂ) • C2+(44 : ℂ) • C1+(48 : ℂ) • C0)-(1/48 : ℂ) • T := by
  rw [h0,h1,h2,h3]
  linear_combination (norm := module) -(1/48 : ℂ) • hr

private theorem current_word_return (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (Q : End) :
    currentWord F seed z Q=
      (1/48 : ℂ) • coframeCubic (fun a => sandwichJet F seed z (bracket (compressionCore F) Q) a 0 0 0)-
      (1/48 : ℂ) • (finiteResolvent F z*sourceRead F seed (cubic (bracket diagonalAction Q))*finiteResolvent F z) := by
  let A := bracket diagonalAction Q
  let C := bracket (compressionCore F) Q
  have hsplit : bracket (defectAction F) Q=A-C := by
    unfold defectAction
    exact commutator_sub _ _ _
  have hs (n : ℕ) : sandwichJet F seed z (bracket (defectAction F) Q) n 0 0 0=
      sandwichJet F seed z A n 0 0 0-sandwichJet F seed z C n 0 0 0 :=
    (congrArg (fun B : End => sandwichJet F seed z B n 0 0 0) hsplit).trans (sandwich_sub F seed z A C n 0)
  have ho := sandwich_origin F seed z hz A
  have h0 := (hs 0).trans (congrArg (fun B : Op => B-sandwichJet F seed z C 0 0 0 0) ho)
  have hr := current_rest F seed z hz A
  simp only [map_sub,map_smul,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc] at hr
  exact collect_response _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 (hs 1) (hs 2) (hs 3) hr


private theorem scalar_cubic (sharp : Bool) (m ell : ℕ) :
    cubic (bracket diagonalAction (scalarOnlyCurrent sharp m ell))=
      (-96*(sourceTime 0 : ℂ)^2) •
        bracket SourceScalarRadialContact.scalarEulerAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell) := by
  have hQ : neutralCurrent sharp m ell=scalarOnlyCurrent sharp m ell+
      spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell := by
    rw [original_neutral_scalar_return,scalarNeutral,scalarOnlyCurrent]
    noncomm_ring
  have h := original_neutral_coframe_ward sharp m ell
  rw [hQ,commutator_add,map_add,original_spin_window_ward,add_zero] at h
  exact h

private theorem scalar_contacts (sharp : Bool) (m ell : ℕ) :
    -(1/48 : ℂ) • cubic (bracket diagonalAction (scalarOnlyCurrent sharp m ell))+
      neutralContacts sharp m ell=(oscillatorMass : ℂ) • SourceScalarDoubleCurrent.fullInsertion sharp m ell := by
  rw [scalar_cubic,original_radial_insertion]
  unfold neutralContacts oscillatorMass SourceScalarDoubleCurrent.fullInsertion
  rw [full_scalar_split]
  simp only [add_mul]
  push_cast
  module

def scalarPolynomial (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  (1/48 : ℂ) • coframeCubic (fun a => sandwichJet F seed z
    (bracket (compressionCore F) (scalarOnlyCurrent sharp m ell)) a 0 0 0)

private theorem complete_scalar_return (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    scalarOnlyRemainder sharp m ell F seed z=scalarPolynomial sharp m ell F seed z+
      (oscillatorMass : ℂ) • (finiteResolvent F z*
        (sourceRead F seed (SourceScalarDoubleCurrent.fullInsertion sharp m ell)-solverOperator sharp m ell F)*finiteResolvent F z) := by
  have hc := current_word_return F seed z hz (scalarOnlyCurrent sharp m ell)
  have hs := congrArg (fun A : End => finiteResolvent F z*sourceRead F seed A*finiteResolvent F z)
    (scalar_contacts sharp m ell)
  simp only [map_add,map_smul,mul_add,add_mul,mul_smul_comm,smul_mul_assoc] at hs
  change currentWord F seed z (scalarOnlyCurrent sharp m ell)+
    finiteResolvent F z*(sourceRead F seed (neutralContacts sharp m ell)-
      (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z=_
  rw [hc]
  unfold scalarPolynomial
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  linear_combination (norm := module) hs

private theorem solver_retarded (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : H) :
    (finiteResolvent F z*solverOperator sharp m ell F*finiteResolvent F z) g=
      particular sharp m ell F z g+z • finiteResolvent F z (particular sharp m ell F z g) := by
  have hc := resolvent_compression (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) z hz
  change finiteResolvent F z*GaussGradedCompression.compression F=1+z • finiteResolvent F z at hc
  rw [solverOperator,←ContinuousLinearMap.mul_def,mul_assoc]
  change ((finiteResolvent F z*GaussGradedCompression.compression F)*cutoffSolver sharp m ell*finiteResolvent F z) g=_
  rw [hc]
  simp only [add_mul,one_mul,smul_mul_assoc,add_apply,smul_apply,mul_apply_eq_comp,particular]

def compressionProfile (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain) (z : ℂ) : ℂ :=
  (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (scalarPolynomial sharp m ell F g z (g : H))

def hardyVector (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g : H) : H :=
  particular sharp m ell F z g+z • finiteResolvent F z (particular sharp m ell F z g)

private theorem mass_nonzero : (oscillatorMass : ℂ)≠0 := by
  exact_mod_cast (show oscillatorMass≠0 by unfold oscillatorMass;exact mul_ne_zero (by norm_num) (pow_ne_zero _ source_time_nonzero))

private theorem pair_complete {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S R A B : E →L[ℂ] E) (m : ℂ) (hm : m≠0) (g k : E) :
    m⁻¹*inner ℂ k ((S+m • (R*(A-B)*R)) g)=
      m⁻¹*inner ℂ k (S g)+inner ℂ k ((R*A*R) g)-inner ℂ k ((R*B*R) g) := by
  simp only [add_apply,smul_apply,inner_add_right,inner_smul_right,mul_sub,sub_mul,sub_apply,inner_sub_right]
  field_simp
  ring

attribute [local irreducible] scalarOnlyRemainder scalarOnlyCurrent scalarPolynomial fullAction

/-- H minus its complete defect becomes the same graded compression. The
source Pc and contacts combine before any norm, and the Hardy term retains CF. -/
theorem actual_complete_scalar_pair (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) :
    (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (scalarOnlyRemainder sharp m ell F g z (g : H))=
      compressionProfile sharp m ell F g k z+
      sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))-
      inner ℂ (k : H) (hardyVector sharp m ell F z (g : H)) := by
  have he := congrArg (fun A : Op => (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (A (g : H)))
    (complete_scalar_return sharp m ell F g z hz)
  have hc := pair_complete (scalarPolynomial sharp m ell F g z) (finiteResolvent F z)
    (sourceRead F g (SourceScalarDoubleCurrent.fullInsertion sharp m ell)) (solverOperator sharp m ell F)
    (oscillatorMass : ℂ) mass_nonzero (g : H) (k : H)
  have hx := SourceInverseDefectCurrentResponse.actual_read_pair F z hz g k (SourceScalarDoubleCurrent.fullInsertion sharp m ell)
  have hX : SourceScalarDoubleCurrent.fullInsertion sharp m ell (state F z hz g)=
      SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)) := by
    rw [SourceScalarDoubleCurrent.fullInsertion]
    rfl
  have hx' := hx.trans (congrArg (sourcePair (state F (star z)
    (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)) hX)
  have hS := congrArg (fun x : H => inner ℂ (k : H) x) (solver_retarded sharp m ell F z hz (g : H))
  exact he.trans (hc.trans (congrArg₂ (·-·) (congrArg (fun x : ℂ => compressionProfile sharp m ell F g k z+x) hx') hS))

private theorem three_square (a b c : ℂ) : ‖a+b-c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have h := (norm_sub_le (a+b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

def vacuumPrice (sharp : Bool) : ℝ :=
  2*‖constantBounded sharp vacuum‖^2+coefficientCost sharp*‖vacuum‖^2

private theorem full_price_split (sharp : Bool) (f : QuantumTest) :
    fullPrice sharp f=coefficientCost sharp/(2*sourceTime 0)*inverseForm f+
      vacuumPrice sharp*‖embed f‖^2 := by
  unfold fullPrice vacuumPrice
  field_simp [source_time_nonzero]
  ring

/-- The complete signed remainder is paid by one localized inverse form on
the original right state, its actual advanced exterior leg, and paid endpoints. -/
theorem actual_complete_inverse_bound (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) :
    let p := state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k
    let q := state F z hz g
    let tq := SourceMixedNativeReturn.thetaAction m ell q
    ‖(oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (scalarOnlyRemainder sharp m ell F g z (g : H))‖^2 ≤
      3*(‖compressionProfile sharp m ell F g k z‖^2+
        (coefficientCost sharp/(2*sourceTime 0))*‖embed p‖^2*inverseForm tq+
        vacuumPrice sharp*‖embed p‖^2*‖embed tq‖^2+
        ‖(k : H)‖^2*‖hardyVector sharp m ell F z (g : H)‖^2) := by
  dsimp only
  rw [actual_complete_scalar_pair]
  have hy : ‖sourcePair
      (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))‖^2 ≤
      ‖embed (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)‖^2*
      ‖embed (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))‖^2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _)
      (norm_inner_le_norm (𝕜 := ℂ) _ _) 2).trans_eq (mul_pow _ _ _)
  have hf := mul_le_mul_of_nonneg_left (original_full_inverse sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))
    (sq_nonneg ‖embed (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)‖)
  rw [full_price_split] at hf
  have hh := (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (k : H) (hardyVector sharp m ell F z (g : H))) 2).trans_eq (mul_pow _ _ _)
  have h3 := three_square (compressionProfile sharp m ell F g k z)
    (sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g))))
    (inner ℂ (k : H) (hardyVector sharp m ell F z (g : H)))
  have hs := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (le_refl (‖compressionProfile sharp m ell F g k z‖^2)) (hy.trans hf)) hh)
    (by norm_num : (0:ℝ) ≤ 3)
  exact h3.trans (hs.trans_eq (by ring))

open SourceInverseCoframeCompressionBudget SourceInverseSpinCompressionBudget
open SourceInverseCoframeSpectralReturn SourceJointResidualEnergy

private def neutralPolynomial (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  (1/48 : ℂ) • coframeCubic (fun a => sandwichJet F seed z (compressionNeutral sharp m ell F) a 0 0 0)
private def totalCompressionProfile (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain) (z : ℂ) : ℂ :=
  (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (neutralPolynomial sharp m ell F g z (g : H))

private theorem neutral_contacts (sharp : Bool) (m ell : ℕ) :
    -(1/48 : ℂ) • cubic (bracket diagonalAction (neutralCurrent sharp m ell))+
      neutralContacts sharp m ell=(oscillatorMass : ℂ) • SourceScalarDoubleCurrent.fullInsertion sharp m ell := by
  rw [original_neutral_coframe_ward,original_radial_insertion]
  unfold neutralContacts oscillatorMass SourceScalarDoubleCurrent.fullInsertion
  rw [full_scalar_split]
  simp only [add_mul]
  push_cast
  module

private theorem complete_coframe_return (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    coframeReducedRemainder sharp m ell F seed z=neutralPolynomial sharp m ell F seed z+
      (oscillatorMass : ℂ) • (finiteResolvent F z*
        (sourceRead F seed (SourceScalarDoubleCurrent.fullInsertion sharp m ell)-solverOperator sharp m ell F)*finiteResolvent F z) := by
  have hc := current_word_return F seed z hz (neutralCurrent sharp m ell)
  have hs := congrArg (fun A : End => finiteResolvent F z*sourceRead F seed A*finiteResolvent F z)
    (neutral_contacts sharp m ell)
  simp only [map_add,map_smul,mul_add,add_mul,mul_smul_comm,smul_mul_assoc] at hs
  unfold coframeReducedRemainder neutralDefect hamiltonianCoframeCorrection neutralHamiltonianCurrent
  change currentWord F seed z (neutralCurrent sharp m ell)+
    finiteResolvent F z*(sourceRead F seed (neutralContacts sharp m ell)-
      (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z=_
  rw [hc]
  unfold neutralPolynomial compressionNeutral
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  linear_combination (norm := module) hs

private theorem complete_coframe_pair (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) :
    (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (coframeReducedRemainder sharp m ell F g z (g : H))=
      totalCompressionProfile sharp m ell F g k z+
      sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))-
      inner ℂ (k : H) (hardyVector sharp m ell F z (g : H)) := by
  have he := congrArg (fun A : Op => (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (A (g : H)))
    (complete_coframe_return sharp m ell F g z hz)
  have hc := pair_complete (neutralPolynomial sharp m ell F g z) (finiteResolvent F z)
    (sourceRead F g (SourceScalarDoubleCurrent.fullInsertion sharp m ell)) (solverOperator sharp m ell F)
    (oscillatorMass : ℂ) mass_nonzero (g : H) (k : H)
  have hx := SourceInverseDefectCurrentResponse.actual_read_pair F z hz g k (SourceScalarDoubleCurrent.fullInsertion sharp m ell)
  have hX : SourceScalarDoubleCurrent.fullInsertion sharp m ell (state F z hz g)=
      SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)) := by
    rw [SourceScalarDoubleCurrent.fullInsertion]
    rfl
  have hx' := hx.trans (congrArg (sourcePair (state F (star z)
    (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)) hX)
  have hS := congrArg (fun x : H => inner ℂ (k : H) x) (solver_retarded sharp m ell F z hz (g : H))
  exact he.trans (hc.trans (congrArg₂ (·-·) (congrArg (fun x : ℂ => totalCompressionProfile sharp m ell F g k z+x) hx') hS))

/-- Public access to the existing exact coframe pairing, preserving its original proof. -/
alias actual_complete_coframe_pair := complete_coframe_pair

private theorem coframe_inverse_bound (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) :
    let p := state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k
    let q := state F z hz g
    let tq := SourceMixedNativeReturn.thetaAction m ell q
    ‖(oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (coframeReducedRemainder sharp m ell F g z (g : H))‖^2 ≤
      3*(‖totalCompressionProfile sharp m ell F g k z‖^2+
        (coefficientCost sharp/(2*sourceTime 0))*‖embed p‖^2*inverseForm tq+
        vacuumPrice sharp*‖embed p‖^2*‖embed tq‖^2+
        ‖(k : H)‖^2*‖hardyVector sharp m ell F z (g : H)‖^2) := by
  dsimp only
  rw [complete_coframe_pair]
  have hy : ‖sourcePair
      (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))‖^2 ≤
      ‖embed (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)‖^2*
      ‖embed (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))‖^2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) _ _) 2).trans_eq (mul_pow _ _ _)
  have hf := mul_le_mul_of_nonneg_left (original_full_inverse sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))
    (sq_nonneg ‖embed (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)‖)
  rw [full_price_split] at hf
  have hh := (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (k : H) (hardyVector sharp m ell F z (g : H))) 2).trans_eq (mul_pow _ _ _)
  have h3 := three_square (totalCompressionProfile sharp m ell F g k z)
    (sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g))))
    (inner ℂ (k : H) (hardyVector sharp m ell F z (g : H)))
  have hs := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (le_refl (‖totalCompressionProfile sharp m ell F g k z‖^2)) (hy.trans hf)) hh)
    (by norm_num : (0:ℝ) ≤ 3)
  exact h3.trans (hs.trans_eq (by ring))

private def leafWeight (j : Fin 4) : ℂ :=
  match j.val with | 0 => 1 | 1 => 11/12 | 2 => 1/4 | _ => 1/48
private def leafInput (g : diagonal.domain) (i : Fin 4) : QuantumTest :=
  ((oscillatorMass : ℂ)⁻¹*leafWeight i) • coreEquiv.symm g
private def leafProfile (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain)
    (z : ℂ) (i : Fin 4) : ℂ :=
  coframeProfile F g z (compressionNeutral sharp m ell F) (leafInput g i) (coreEquiv.symm k) i 0

private theorem compression_leaves (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain) (z : ℂ) :
    totalCompressionProfile sharp m ell F g k z=∑ i : Fin 4,leafProfile sharp m ell F g k z i := by
  have he (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply x)
  unfold totalCompressionProfile neutralPolynomial
  simp only [coframeCubic,coframeRest,add_apply,smul_apply,inner_add_right,inner_smul_right]
  simp only [Fin.sum_univ_four,leafProfile,leafInput,coframeProfile,map_smul,inner_smul_right,he]
  norm_num [leafWeight]
  ring

private theorem leaf_continuous (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain)
    (μ : ℝ) (hμ : 0<μ) (i : Fin 4) :
    Continuous (fun w => leafProfile sharp m ell F g k (line μ w) i) := by
  simp_rw [leafProfile,actual_coframe_decode F g _ μ hμ]
  change Continuous (fun w : ℝ => ∑ ij : Channel F × Channel F,
    polePair μ (channelValue F ij.1) (channelValue F ij.2) w *
      coframeCoefficient F g (compressionNeutral sharp m ell F) (leafInput g i) (coreEquiv.symm k) i ij)
  apply continuous_finsetSum
  intro ij _
  exact ((pole_continuous μ _ hμ).mul (pole_continuous μ _ hμ)).mul continuous_const

private theorem leaf_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (i : Fin 4) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖leafProfile sharp m ell F g k (line μ w) i‖^2)) ≤ ENNReal.ofReal ε := by
  exact actual_neutral_compression_coframe_tail sharp g μ hμ i (leafInput g i) (coreEquiv.symm k)

private theorem four_square (f : Fin 4 → ℂ) :
    ‖∑ i,f i‖^2 ≤ 4*∑ i,‖f i‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ f) 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 4 => (1:ℝ)) (fun i => ‖f i‖)
  norm_num only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hc
  exact h.trans hc

private theorem compression_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖totalCompressionProfile sharp m ell F g k (line μ w)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  classical
  choose N hN using fun i : Fin 4 => leaf_tail sharp μ hμ g k i (ε/16) (by positivity)
  refine ⟨Finset.univ.sup N,fun m hm ell hell => ?_⟩
  have hE := Filter.eventually_all.mpr (fun i : Fin 4 =>
    hN i m ((Finset.le_sup (Finset.mem_univ i)).trans hm) ell hell)
  filter_upwards [hE] with F hF
  calc
    _  ≤  ∫⁻ w : ℝ,ENNReal.ofReal 4*∑ i : Fin 4,
        ENNReal.ofReal (‖leafProfile sharp m ell F g k (line μ w) i‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),←ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by rw [compression_leaves];exact four_square _)
    _ = ENNReal.ofReal 4*∑ i : Fin 4,
        ∫⁻ w : ℝ,ENNReal.ofReal (‖leafProfile sharp m ell F g k (line μ w) i‖^2) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact lintegral_finsetSum Finset.univ (fun i _ =>
        by simpa only [Pi.pow_apply] using ((leaf_continuous sharp m ell F g k μ hμ i).norm.pow 2).measurable.ennreal_ofReal)
    _  ≤  ENNReal.ofReal 4*∑ _i : Fin 4,ENNReal.ofReal (ε/16) := by gcongr with i;exact hF i
    _ = ENNReal.ofReal ε := by
      norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_ofNat,ENNReal.ofReal_ofNat]
      rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num]
      rw [←ENNReal.ofReal_mul (by norm_num),←ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

/-- The original compression profile is shared by both energy prices. -/
abbrev completeCompressionProfile := totalCompressionProfile

/-- Original finite-channel continuity, exposed for the smaller scalar price. -/
theorem actual_complete_compression_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    Continuous (fun w => completeCompressionProfile sharp m ell F g k (line μ w)) := by
  simp_rw [completeCompressionProfile,compression_leaves]
  exact continuous_finsetSum _ (fun i _ => leaf_continuous sharp m ell F g k μ hμ i)

/-- This is the already generated common cutoff/cofinal-F endpoint tail. -/
alias actual_complete_compression_tail := compression_tail

open SourceInverseNeutralRemainderClosed SourceInverseCoframeJointTailReturn SourceRetardedForcingTail
open SourceRelativePowerTail

def localizedInverseCost (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (star (line μ w)) (k : H)‖^2*
    inverseForm (SourceMixedNativeReturn.thetaAction m ell
      (state F (line μ w) (by simpa only [line_im] using hμ.ne') g)))
private def windowVector (m ell : ℕ) (F : Index) (z : ℂ) (g : H) : H :=
  relativeTail m ell (finiteResolvent F z g)
private def normPrice (sharp : Bool) (μ : ℝ) (k : diagonal.domain) : ℝ :=
  vacuumPrice sharp*μ⁻¹^2*‖(k : H)‖^2
def formPrice (sharp : Bool) : ℝ := 3*coefficientCost sharp/(2*sourceTime 0)

private theorem vacuum_price_nonnegative (sharp : Bool) : 0 ≤ vacuumPrice sharp := by
  unfold vacuumPrice coefficientCost
  positivity
private theorem form_price_nonnegative (sharp : Bool) : 0 ≤ formPrice sharp := by
  have hn : 0<sourceTime 0 := by rw [source_time_generated];exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  unfold formPrice coefficientCost
  positivity
private theorem norm_price_nonnegative (sharp : Bool) (μ : ℝ) (k : diagonal.domain) : 0 ≤ normPrice sharp μ k := by
  unfold normPrice
  exact mul_nonneg (mul_nonneg (vacuum_price_nonnegative sharp) (sq_nonneg _)) (sq_nonneg _)

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem window_embed (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (SourceMixedNativeReturn.thetaAction m ell (state F z hz g))=windowVector m ell F z (g : H) :=
  (theta_core m ell _).symm.trans (congrArg (relativeTail m ell) (state_embed F z hz g))

private theorem outer_square_bound (F : Index) (μ : ℝ) (hμ : 0<μ) (w : ℝ) (k : H) :
    ‖finiteResolvent F (star (line μ w)) k‖^2 ≤ μ⁻¹^2*‖k‖^2 := by
  have hs : (star (line μ w)).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
  have hr := finite_resolvent_norm F (star (line μ w)) hs
  simp only [Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ,one_div] at hr
  have h := ((finiteResolvent F (star (line μ w))).le_opNorm k).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg k))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (mul_pow _ _ _)

private theorem four_integral (x a : ℝ → ℂ) (b c : ℝ → H) (d : ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : ∀ w,0 ≤ d w)
    (B C D : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (he : ∀ w,‖x w‖^2 ≤ 3*(‖a w‖^2+B*‖b w‖^2+C*‖c w‖^2)+D*d w) :
    (∫⁻ w,ENNReal.ofReal (‖x w‖^2)) ≤
      ENNReal.ofReal 3*((∫⁻ w,ENNReal.ofReal (‖a w‖^2))+
        ENNReal.ofReal B*(∫⁻ w,ENNReal.ofReal (‖b w‖^2))+
        ENNReal.ofReal C*(∫⁻ w,ENNReal.ofReal (‖c w‖^2)))+
      ENNReal.ofReal D*(∫⁻ w,ENNReal.ofReal (d w)) := by
  have hma : Measurable (fun w => ENNReal.ofReal (‖a w‖^2)) := by simpa only [Pi.pow_apply] using (ha.norm.pow 2).measurable.ennreal_ofReal
  have hmb : Measurable (fun w => ENNReal.ofReal (‖b w‖^2)) := by simpa only [Pi.pow_apply] using (hb.norm.pow 2).measurable.ennreal_ofReal
  have hmc : Measurable (fun w => ENNReal.ofReal (‖c w‖^2)) := by simpa only [Pi.pow_apply] using (hc.norm.pow 2).measurable.ennreal_ofReal
  have hmB : Measurable (fun w => ENNReal.ofReal B*ENNReal.ofReal (‖b w‖^2)) := measurable_const.mul hmb
  have hmC : Measurable (fun w => ENNReal.ofReal C*ENNReal.ofReal (‖c w‖^2)) := measurable_const.mul hmc
  have hmAB : Measurable (fun w => ENNReal.ofReal (‖a w‖^2)+ENNReal.ofReal B*ENNReal.ofReal (‖b w‖^2)) := hma.add hmB
  have hm : Measurable (fun w => ENNReal.ofReal 3*(ENNReal.ofReal (‖a w‖^2)+
      ENNReal.ofReal B*ENNReal.ofReal (‖b w‖^2)+ENNReal.ofReal C*ENNReal.ofReal (‖c w‖^2))) :=
    measurable_const.mul ((hma.add hmB).add hmC)
  calc
    _ ≤ ∫⁻ w,ENNReal.ofReal 3*(ENNReal.ofReal (‖a w‖^2)+
        ENNReal.ofReal B*ENNReal.ofReal (‖b w‖^2)+ENNReal.ofReal C*ENNReal.ofReal (‖c w‖^2))+
        ENNReal.ofReal D*ENNReal.ofReal (d w) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hB,←ENNReal.ofReal_mul hC,
        ←ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hB (sq_nonneg _)),
        ←ENNReal.ofReal_add (by positivity) (mul_nonneg hC (sq_nonneg _)),
        ←ENNReal.ofReal_mul (by norm_num),←ENNReal.ofReal_mul hD,
        ←ENNReal.ofReal_add (by positivity) (mul_nonneg hD (hd w))]
      exact ENNReal.ofReal_le_ofReal (he w)
    _ = _ := by
      rw [lintegral_add_left hm,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left hmAB,lintegral_add_left hma,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem complete_integral_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ENNReal.ofReal (closedRemainderCost sharp m ell F μ g k) ≤
      ENNReal.ofReal 3*((∫⁻ w,ENNReal.ofReal (‖totalCompressionProfile sharp m ell F g k (line μ w)‖^2))+
        ENNReal.ofReal (normPrice sharp μ k)*(∫⁻ w,ENNReal.ofReal (‖windowVector m ell F (line μ w) (g : H)‖^2))+
        ENNReal.ofReal (‖(k : H)‖^2)*(∫⁻ w,ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g : H)‖^2)))+
      ENNReal.ofReal (formPrice sharp)*localizedInverseCost m ell F μ hμ g k := by
  rw [←actual_profile_closed_lintegral sharp m ell F μ hμ g k]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hA : Continuous (fun w => totalCompressionProfile sharp m ell F g k (line μ w)) := by
    simp_rw [compression_leaves]
    exact continuous_finsetSum _ (fun i _ => leaf_continuous sharp m ell F g k μ hμ i)
  have hB : Continuous (fun w => windowVector m ell F (line μ w) (g : H)) :=
    (relativeTail m ell).continuous.comp (hr.clm_apply continuous_const)
  have hp : Continuous (fun w => particular sharp m ell F (line μ w) (g : H)) :=
    (cutoffSolver sharp m ell).continuous.comp (hr.clm_apply continuous_const)
  have hC : Continuous (fun w => hardyVector sharp m ell F (line μ w) (g : H)) :=
    hp.add ((show Continuous (fun w : ℝ => line μ w) by unfold line;fun_prop).smul (hr.clm_apply hp))
  apply four_integral _ _ _ _ _ hA hB hC
    (fun w => mul_nonneg (sq_nonneg _) (original_inverse_nonnegative _))
    _ _ _ (norm_price_nonnegative sharp μ k) (sq_nonneg _) (form_price_nonnegative sharp)
  intro w
  have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
  have h := coframe_inverse_bound sharp m ell F (line μ w) hz g k
  dsimp only at h
  simp only [state_embed,window_embed] at h
  have hv := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (outer_square_bound F μ hμ w (k : H)) (vacuum_price_nonnegative sharp))
    (sq_nonneg ‖windowVector m ell F (line μ w) (g : H)‖)
  change ‖(oscillatorMass : ℂ)⁻¹*inner ℂ (k : H)
    (coframeReducedRemainder sharp m ell F g (line μ w) (g : H))‖^2 ≤ _
  have hv' : vacuumPrice sharp*‖finiteResolvent F (star (line μ w)) (k : H)‖^2*
      ‖windowVector m ell F (line μ w) (g : H)‖^2 ≤
      normPrice sharp μ k*‖windowVector m ell F (line μ w) (g : H)‖^2 :=
    hv.trans_eq (by unfold normPrice;ring)
  apply h.trans
  calc
    _ ≤ 3*(‖totalCompressionProfile sharp m ell F g k (line μ w)‖^2+
        coefficientCost sharp/(2*sourceTime 0)*‖finiteResolvent F (star (line μ w)) (k : H)‖^2*
          inverseForm (SourceMixedNativeReturn.thetaAction m ell (state F (line μ w) hz g))+
        normPrice sharp μ k*‖windowVector m ell F (line μ w) (g : H)‖^2+
        ‖(k : H)‖^2*‖hardyVector sharp m ell F (line μ w) (g : H)‖^2) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hv') le_rfl) (by norm_num)
    _ = _ := by unfold formPrice;ring

/-- The complete original signed cost consumes one actual localized inverse
form. All compression, Hardy-CF and vacuum-norm endpoints are paid on the
original common cutoff and cofinal-F event. -/
theorem actual_closed_inverse_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ᶠ F in (sourceFilter : Filter Index),
      ENNReal.ofReal (closedRemainderCost sharp m ell F μ g k) ≤
        ENNReal.ofReal ε+ENNReal.ofReal (formPrice sharp)*localizedInverseCost m ell F μ hμ g k := by
  intro ε hε
  let C := 1+normPrice sharp μ k+‖(k : H)‖^2
  let δ := ε/(3*C)
  have hC : 0<C := by have hn := norm_price_nonnegative sharp μ k;dsimp [C];positivity
  have hδ : 0<δ := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨N₁,h₁⟩ := compression_tail sharp μ hμ g k δ hδ
  obtain ⟨N₂,h₂⟩ := bounded_forcing_full_frequency_tail μ hμ (ContinuousLinearMap.id ℂ H) g δ hδ
  obtain ⟨N₃,h₃⟩ := actual_hardy_retarded_tail μ hμ sharp g δ hδ
  refine ⟨max N₁ (max N₂ N₃),fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hell,
    h₂ m ((le_max_left _ _).trans ((le_max_right _ _).trans hm)) ell hell,
    h₃ m ((le_max_right _ _).trans ((le_max_right _ _).trans hm)) ell hell] with F hF₁ hF₂ hF₃
  have hW : (∫⁻ w : ℝ,ENNReal.ofReal (‖windowVector m ell F (line μ w) (g : H)‖^2)) ≤ ENNReal.ofReal δ := by
    simpa only [windowVector,ContinuousLinearMap.id_apply] using hF₂
  have hH : (∫⁻ w : ℝ,ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g : H)‖^2)) ≤ ENNReal.ofReal δ := hF₃
  apply (complete_integral_bound sharp m ell F μ hμ g k).trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ ENNReal.ofReal 3*(ENNReal.ofReal δ+ENNReal.ofReal (normPrice sharp μ k)*ENNReal.ofReal δ+
        ENNReal.ofReal (‖(k : H)‖^2)*ENNReal.ofReal δ) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (norm_price_nonnegative sharp μ k),←ENNReal.ofReal_mul (sq_nonneg _),
        ←ENNReal.ofReal_add hδ.le (mul_nonneg (norm_price_nonnegative sharp μ k) hδ.le),
        ←ENNReal.ofReal_add (add_nonneg hδ.le (mul_nonneg (norm_price_nonnegative sharp μ k) hδ.le)) (mul_nonneg (sq_nonneg _) hδ.le),←ENNReal.ofReal_mul (by norm_num)]
      congr 1
      calc
        _ = 3*C*δ := by dsimp [C];ring
        _ = ε := by dsimp [δ];field_simp [hC.ne']

end LowEnergy.SourceScalarSignedInverseReturn
