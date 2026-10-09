import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNeutralSpinCurrent
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeSpinCompressionBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseNeutralSpinTail
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

private theorem scale_product (A B : End) :
    scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  rw [←K_commutator,←K_commutator,←K_commutator]
  noncomm_ring

private theorem scale_bracket (A B : End) :
    scaleDerivative (bracket A B)=bracket (scaleDerivative A) B+bracket A (scaleDerivative B) := by
  simp only [bracket,map_sub,scale_product]
  noncomm_ring

private theorem full_scale (sharp : Bool) : scaleDerivative (SourceMixedNativeReturn.fullAction sharp)=0 := by
  have hE : Commute eulerAction (SourceMixedNativeReturn.fullAction sharp) := by
    cases sharp
    · exact euler_invariant_multiplier _
        (fun _ => (sourceMap.contDiff.comp scalarField_smooth).contDiffAt) (fun _ _ => rfl)
    · exact euler_invariant_multiplier _
        (fun _ => (GaussFullHamiltonian.adjointMap.contDiff.comp scalarField_smooth).contDiffAt) (fun _ _ => rfl)
  have he : eulerAction*SourceMixedNativeReturn.fullAction sharp-
      SourceMixedNativeReturn.fullAction sharp*eulerAction=(0 : ℂ) • SourceMixedNativeReturn.fullAction sharp := by
    rw [hE.eq,sub_self,zero_smul]
  have hd : dilation*SourceMixedNativeReturn.fullAction sharp-
      SourceMixedNativeReturn.fullAction sharp*dilation=0 := by
    rw [dilation_operator]
    simpa only [mul_zero,zero_smul,Module.End.one_eq_id] using!
      affine_dilation _ _ _ 0 he (original_number_full sharp)
  unfold scaleDerivative
  change (3*Complex.I/2 : ℂ) • (dilation*SourceMixedNativeReturn.fullAction sharp-
    SourceMixedNativeReturn.fullAction sharp*dilation)=0
  rw [hd,smul_zero]

private theorem spin_potential_scale : scaleDerivative spinPotential=(-3 : ℂ) • spinPotential := by
  have hs := homogeneous_sum dilation (fun a : Fin 7 => GaussCoframeForm.spinSquare a) (2*Complex.I)
    spin_square_current
  have h := homogeneous_add dilation _ _ (2*Complex.I) hs number_shift_current
  change dilation*spinPotential-spinPotential*dilation=(2*Complex.I) • spinPotential at h
  unfold scaleDerivative
  change (3*Complex.I/2 : ℂ) • (dilation*spinPotential-spinPotential*dilation)=_
  rw [h,smul_smul]
  congr 1
  calc (3*Complex.I/2)*(2*Complex.I)=3*(Complex.I*Complex.I) := by ring
       _= -3 := by rw [Complex.I_mul_I];ring

private theorem spin_current_scale (sharp : Bool) : scaleDerivative (spinCurrent sharp)=(-3 : ℂ) • spinCurrent sharp := by
  unfold spinCurrent
  rw [scale_bracket,spin_potential_scale,full_scale]
  simp only [bracket,smul_mul_assoc,mul_smul_comm,mul_zero,zero_mul,sub_self,add_zero,smul_sub]

private theorem theta_scale (m ell : ℕ) : scaleDerivative (SourceMixedNativeReturn.thetaAction m ell)=0 := by
  unfold scaleDerivative
  change (3*Complex.I/2 : ℂ) • (dilation*SourceMixedNativeReturn.thetaAction m ell-
    SourceMixedNativeReturn.thetaAction m ell*dilation)=0
  rw [(theta_dilation m ell).symm.eq,sub_self,smul_zero]

private theorem spin_window_scale (sharp : Bool) (m ell : ℕ) :
    scaleDerivative (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell)=
      (-3 : ℂ) • (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell) := by
  rw [scale_product,spin_current_scale,theta_scale,mul_zero,add_zero,smul_mul_assoc]

private theorem local_spin_current (sharp : Bool) : Commute localAction (spinCurrent sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold localAction
  change (localPotential z : ℂ) • (spinCurrent sharp f z)=spinCurrent sharp (multiply localPotential local_smooth f) z
  rw [original_spin_current_apply,original_spin_current_apply]
  exact (map_smul _ _ _).symm

private theorem local_spin_window (sharp : Bool) (m ell : ℕ) :
    Commute localAction (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell) := by
  have ht : Commute localAction (SourceMixedNativeReturn.thetaAction m ell) := by
    unfold SourceMixedNativeReturn.thetaAction localAction
    exact ((Commute.one_right _).sub_right (GaussRadialHamiltonian.real_commutes _ _) |>.pow_right _).sub_right
      ((Commute.one_right _).sub_right (GaussRadialHamiltonian.real_commutes _ _) |>.pow_right _)
  exact (local_spin_current sharp).mul_right ht

private theorem bracket_weight (A B : End) (a b : ℂ)
    (hA : scaleDerivative A=a • A) (hB : scaleDerivative B=b • B) :
    scaleDerivative (bracket A B)=(a+b) • bracket A B := by
  rw [scale_bracket,hA,hB]
  simp only [bracket,smul_mul_assoc,mul_smul_comm]
  module

private theorem cubic_weight (A : End) (a : ℂ) (h : scaleDerivative A=a • A) :
    cubic A=(a^3+12*a^2+44*a+48) • A := by
  simp only [cubic,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,h,map_smul,smul_smul]
  module

private theorem source_split : diagonalAction=kineticMinus+matterAction+electricSpatial+localAction := by
  rw [original_action_split]
  unfold kineticMinus electricSpatial
  abel

private theorem kinetic_minus_scale : scaleDerivative kineticMinus=(-3 : ℂ) • kineticMinus := by
  simp only [kineticMinus,map_sub,scale_kinetic,scale_electric]
  module

/-- The original coframe Pc annihilates the complete H-current of the zero-order spin cutoff. -/
theorem original_spin_window_ward (sharp : Bool) (m ell : ℕ) :
    cubic (bracket diagonalAction (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell))=0 := by
  let Q := spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell
  have hQ : scaleDerivative Q=(-3 : ℂ) • Q := spin_window_scale sharp m ell
  have hK := cubic_weight _ (-3+-3) (bracket_weight kineticMinus Q (-3) (-3) kinetic_minus_scale hQ)
  have hM := cubic_weight _ (-1+-3) (bracket_weight matterAction Q (-1) (-3) scale_matter hQ)
  have hEweight : scaleDerivative electricSpatial=(1 : ℂ) • electricSpatial := by
    simp only [electricSpatial,map_add,scale_electric,scale_spatial,one_smul]
  have hE := cubic_weight _ (1+-3) (bracket_weight electricSpatial Q 1 (-3) hEweight hQ)
  norm_num at hK hM hE
  have hL : bracket localAction Q=0 := sub_eq_zero.mpr (local_spin_window sharp m ell).eq
  have hs : bracket diagonalAction Q=bracket kineticMinus Q+bracket matterAction Q+
      bracket electricSpatial Q+bracket localAction Q := by
    rw [source_split]
    unfold bracket
    noncomm_ring
  change cubic (bracket diagonalAction Q)=0
  rw [hs]
  simp only [map_add,hK,hM,hE,hL,map_zero,zero_add]



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
    (A : End) (n : ℕ) (hn : n≤3) :
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

private theorem sandwich_add (F : Index) (seed : diagonal.domain) (z : ℂ) (A B : End) (n : ℕ) (s : ℝ) :
    sandwichJet F seed z (A+B) n 0 s 0=sandwichJet F seed z A n 0 s 0+sandwichJet F seed z B n 0 s 0 := by
  induction n generalizing s with
  | zero =>
    have hadd : (mixedHilbert s 0).conjStarAlgEquiv (sourceRead F seed (A+B))=
        (mixedHilbert s 0).conjStarAlgEquiv (sourceRead F seed A)+
        (mixedHilbert s 0).conjStarAlgEquiv (sourceRead F seed B) :=
      (congrArg (mixedHilbert s 0).conjStarAlgEquiv (map_add (sourceRead F seed) A B)).trans
        (map_add (mixedHilbert s 0).conjStarAlgEquiv (sourceRead F seed A) (sourceRead F seed B))
    have hr := congrArg (fun C : Op => resolventJet F z 0 0 s 0*(C*resolventJet F z 0 0 s 0))
      ((actual_read_orbit F seed (A+B) s 0).trans hadd)
    have ha := congrArg (fun C : Op => resolventJet F z 0 0 s 0*(C*resolventJet F z 0 0 s 0)) (actual_read_orbit F seed A s 0)
    have hb := congrArg (fun C : Op => resolventJet F z 0 0 s 0*(C*resolventJet F z 0 0 s 0)) (actual_read_orbit F seed B s 0)
    simp only [mul_add,add_mul] at hr
    unfold sandwichJet
    exact hr.trans (congrArg₂ (·+·) ha.symm hb.symm)
  | succ n ih =>
    have hd := (sandwich_coframe_derivative F seed z A n 0 s 0).add (sandwich_coframe_derivative F seed z B n 0 s 0)
    exact (sandwich_coframe_derivative F seed z (A+B) n 0 s 0).unique
      (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall ih))

/-- Only the original scalar first current and scalar radial contact remain in this Q. -/
def scalarOnlyCurrent (sharp : Bool) (m ell : ℕ) : End :=
  scalarCurrent sharp*SourceMixedNativeReturn.thetaAction m ell+SourceMixedNativeReturn.fullAction sharp*radialCurrent m ell

/-- Every original d/H correction is retained for the scalar-only source current. -/
def scalarOnlyRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  currentWord F seed z (scalarOnlyCurrent sharp m ell)+
    finiteResolvent F z*(sourceRead F seed (neutralContacts sharp m ell)-
      (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z

private theorem scalar_spin_split (sharp : Bool) (m ell : ℕ) :
    scalarNeutral sharp m ell=scalarOnlyCurrent sharp m ell+spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell := by
  unfold scalarNeutral scalarOnlyCurrent
  noncomm_ring

private theorem cubic_response_add {V : Type*} [AddCommGroup V] [Module ℂ V] (A B C : ℕ → V)
    (h : ∀ n,A n=B n+C n) : coframeCubic A=coframeCubic B+coframeCubic C := by
  simp only [coframeCubic,coframeRest,h]
  module

/-- The complete spin defect/H correction becomes the original CF polynomial with its positive coefficient. -/
theorem actual_scalar_only_remainder (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    scalarReducedRemainder sharp m ell F seed z=scalarOnlyRemainder sharp m ell F seed z+
      (1/48 : ℂ) • coframeCubic (fun a => sandwichJet F seed z
        (bracket (compressionCore F) (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell)) a 0 0 0) := by
  have htotal := current_word_return F seed z hz (scalarNeutral sharp m ell)
  have hscalar := current_word_return F seed z hz (scalarOnlyCurrent sharp m ell)
  have hsplit := scalar_spin_split sharp m ell
  have hcore : cubic (bracket diagonalAction (scalarNeutral sharp m ell))=
      cubic (bracket diagonalAction (scalarOnlyCurrent sharp m ell)) := by
    rw [hsplit,commutator_add,map_add,original_spin_window_ward,add_zero]
  have hCF (n : ℕ) : sandwichJet F seed z (bracket (compressionCore F) (scalarNeutral sharp m ell)) n 0 0 0=
      sandwichJet F seed z (bracket (compressionCore F) (scalarOnlyCurrent sharp m ell)) n 0 0 0+
      sandwichJet F seed z (bracket (compressionCore F) (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell)) n 0 0 0 := by
    have he := congrArg (fun Q : End => bracket (compressionCore F) Q) hsplit
    rw [commutator_add] at he
    exact (congrArg (fun A : End => sandwichJet F seed z A n 0 0 0) he).trans (sandwich_add F seed z _ _ n 0)
  have hpoly := cubic_response_add _ _ _ hCF
  have hc := congrArg (fun A : End => finiteResolvent F z*sourceRead F seed A*finiteResolvent F z) hcore
  unfold scalarReducedRemainder scalarOnlyRemainder
  change currentWord F seed z (scalarNeutral sharp m ell)+_=currentWord F seed z (scalarOnlyCurrent sharp m ell)+_+_
  linear_combination (norm := module) htotal-hscalar-(1/48 : ℂ) • hc+(1/48 : ℂ) • hpoly



open MeasureTheory Filter SourceResolventBandLimit SourceInverseCoframeCompressionBudget
open scoped InnerProductSpace

private def Tail (f : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
    ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖f m ell F w‖^2))≤ENNReal.ofReal ε

private theorem tail_add (f g : ℕ → ℕ → Index → ℝ → ℂ)
    (hc : ∀ m ell F, Continuous (f m ell F))
    (hf : Tail f) (hg : Tail g) :
    Tail (fun m ell F w => f m ell F w+g m ell F w) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := hf (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := hg (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m ((Nat.le_max_left _ _).trans hm) ell hell,
    h₂ m ((Nat.le_max_right _ _).trans hm) ell hell] with F hl hr
  have hp (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
    have h := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*(ENNReal.ofReal (‖f m ell F w‖^2)+
        ENNReal.ofReal (‖g m ell F w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal (hp _ _)
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2))+
        (∫⁻ w : ℝ, ENNReal.ofReal (‖g m ell F w‖^2))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal (‖f m ell F w‖^2)) := by
        simpa only [Pi.pow_apply] using! ((hc m ell F).norm.pow 2).measurable.ennreal_ofReal
      exact congrArg (fun x : ENNReal => ENNReal.ofReal 2*x) (lintegral_add_left hmeas _)
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/4) (by positivity : 0 ≤ ε/4),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

private theorem tail_congr (f h : ℕ → ℕ → Index → ℝ → ℂ)
    (he : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),∀ w,f m ell F w=h m ell F w)
    (hh : Tail h) : Tail f := by
  intro ε hε
  obtain ⟨N,hN⟩ := hh ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell,he m ell] with F hF hEq
  simpa only [hEq] using hF


def spinPolynomial (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  coframeCubic (fun a => sandwichJet F seed z
    (bracket (compressionCore F) (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell)) a 0 0 0)

private theorem paid_spin_coefficients (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ)
    (f k : QuantumTest) :
    (1/48 : ℂ)*inner ℂ (embed k) (spinPolynomial sharp m ell F seed z (embed f))=
      coframeProfile F seed z (bracket (compressionCore F) (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell))
        ((1/48 : ℂ) • f) k 3 0+
      coframeProfile F seed z (bracket (compressionCore F) (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell))
        ((1/4 : ℂ) • f) k 2 0+
      coframeProfile F seed z (bracket (compressionCore F) (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell))
        ((11/12 : ℂ) • f) k 1 0+
      coframeProfile F seed z (bracket (compressionCore F) (spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell))
        f k 0 0 := by
  simp only [spinPolynomial,coframeCubic,coframeRest,coframeProfile,map_smul,add_apply,smul_apply,
    inner_add_right,inner_smul_right]
  ring


open SourceInverseSpinCompressionBudget

private theorem spin_polynomial_continuous (F : Index) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (sharp : Bool) (m ell : ℕ) (f k : QuantumTest) :
    Continuous (fun w : ℝ => (1/48 : ℂ)*inner ℂ (embed k) (spinPolynomial sharp m ell F seed (line μ w) (embed f))) := by
  have hc3 := spin_profile_continuous F seed μ hμ sharp m ell 3 ((1/48 : ℂ) • f) k
  have hc2 := spin_profile_continuous F seed μ hμ sharp m ell 2 ((1/4 : ℂ) • f) k
  have hc1 := spin_profile_continuous F seed μ hμ sharp m ell 1 ((11/12 : ℂ) • f) k
  have hc0 := spin_profile_continuous F seed μ hμ sharp m ell 0 f k
  apply (((hc3.add hc2).add hc1).add hc0).congr
  intro w
  simpa only [compressionSpin,spinInsertion,Pi.add_apply] using (paid_spin_coefficients sharp m ell F seed (line μ w) f k).symm

/-- The precise positive Pc/48 polynomial is paid by the same-source spin compression endpoints. -/
theorem actual_spin_polynomial_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (f k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖(1/48 : ℂ)*inner ℂ (embed k)
          (spinPolynomial sharp m ell F seed (line μ w) (embed f))‖^2))≤ENNReal.ofReal ε := by
  have h3 := actual_spin_compression_coframe_tail sharp seed μ hμ 3 ((1/48 : ℂ) • f) k
  have h2 := actual_spin_compression_coframe_tail sharp seed μ hμ 2 ((1/4 : ℂ) • f) k
  have h1 := actual_spin_compression_coframe_tail sharp seed μ hμ 1 ((11/12 : ℂ) • f) k
  have h0 := actual_spin_compression_coframe_tail sharp seed μ hμ 0 f k
  have hc3 := fun m ell F => spin_profile_continuous F seed μ hμ sharp m ell 3 ((1/48 : ℂ) • f) k
  have hc2 := fun m ell F => spin_profile_continuous F seed μ hμ sharp m ell 2 ((1/4 : ℂ) • f) k
  have hc1 := fun m ell F => spin_profile_continuous F seed μ hμ sharp m ell 1 ((11/12 : ℂ) • f) k
  have ht := tail_add _ _ (fun m ell F => ((hc3 m ell F).add (hc2 m ell F)).add (hc1 m ell F))
    (tail_add _ _ (fun m ell F => (hc3 m ell F).add (hc2 m ell F))
      (tail_add _ _ hc3 h3 h2) h1) h0
  exact tail_congr _ _ (fun m ell => Filter.Eventually.of_forall (fun F w => by
    simpa only [compressionSpin,spinInsertion,Pi.add_apply] using paid_spin_coefficients sharp m ell F seed (line μ w) f k)) ht

/-- The original whole Ward has a common full-frequency difference tail against the scalar-only remainder. -/
theorem actual_ward_scalar_only_difference_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (f k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (embed k)
          (wardOperator sharp m ell F (coreEquiv f) (line μ w) (embed f))-
          inner ℂ (embed k) (scalarOnlyRemainder sharp m ell F (coreEquiv f) (line μ w) (embed f))‖^2))≤ENNReal.ofReal ε := by
  have hspin := actual_spin_polynomial_tail sharp (coreEquiv f) μ hμ f k
  have hward := actual_ward_coframe_reduced_difference_tail sharp μ hμ f k
  have ht := tail_add _ _
    (fun m ell F => spin_polynomial_continuous F (coreEquiv f) μ hμ sharp m ell f k) hspin hward
  apply tail_congr _ _ ?_ ht
  intro m ell
  exact Filter.Eventually.of_forall (fun F w => by
    have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
    have he := congrArg (fun A : Op => inner ℂ (embed k) (A (embed f)))
      ((actual_scalar_ward_remainder sharp m ell F (coreEquiv f) (line μ w)).trans
        (actual_scalar_only_remainder sharp m ell F (coreEquiv f) (line μ w) hz))
    simp only [add_apply,smul_apply,inner_add_right,inner_smul_right] at he
    change _=(1/48 : ℂ)*inner ℂ (embed k) (spinPolynomial sharp m ell F (coreEquiv f) (line μ w) (embed f))+_
    dsimp only [spinPolynomial]
    linear_combination he)

end LowEnergy.SourceInverseNeutralSpinTail
