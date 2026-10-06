import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceMixedNativeReturn
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceMovingJetFlux
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourcePhysicalHamiltonianSquare
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussRadialHamiltonian
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceNativeCutoffContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceGammaNativeBudget
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open GaussYukawaCoefficient GaussLiveMomentum SourceClosedCostNativeProbe
open SourceMixedNativeReturn SourceMovingJetFlux SourceEscapeCurrent
open SourcePhysicalKineticSquare SourcePhysicalHamiltonianSquare
open SourceCoframeVolumeCurrent SourceDilationRemainder SourceOriginalKineticSquare
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge FullYSourceResolventGraphSplice SourceMinimalGraphParticular
open SourceRelativePowerTail
open scoped ContDiff InnerProductSpace RealInnerProductSpace

-- Share the scalar-test instance before elaborating the original core subtype.
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
private abbrev OriginalCore : Type := diagonal.domain

def gammaOperator (sharp : Bool) (m ell : ℕ) (F : Index) (g : OriginalCore) (z : ℂ) : H →L[ℂ] H :=
  omegaResponse sharp m ell F g z-leibnizResponse sharp m ell F g z+
    Complex.I • (sourceRead F g (primitive sharp m ell)*correctionWord F z-
      correctionWord F z*sourceRead F g (primitive sharp m ell))

def sourceGamma (sharp : Bool) (m ell : ℕ) (F : Index) (g k : OriginalCore) (z : ℂ) : ℂ :=
  inner ℂ (Subtype.val k) (gammaOperator sharp m ell F g z (Subtype.val g))

private theorem source_gamma_scalar (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : OriginalCore) (z : ℂ) :
    sourceGamma sharp m ell F g k z=
      inner ℂ (Subtype.val k) (gammaOperator sharp m ell F g z (Subtype.val g)) := rfl

private theorem additive_return {V : Type*} [AddCommGroup V] (a b c d e f : V)
    (h : a=b+c-d) (hb : b=e+f) : c-d+f=a-e := by rw [hb] at h; rw [h]; abel

/-- All three moving-compression corrections cancel against the same original Ward response. -/
theorem gamma_normal_form (sharp : Bool) (m ell : ℕ) (F : Index) (g : OriginalCore)
    (z : ℂ) (hz : z.im≠0) :
    gammaOperator sharp m ell F g z=
      finiteResolvent F z*rawPolynomial sharp m ell F g*finiteResolvent F z-
      Complex.I • (sourceRead F g (primitive sharp m ell)*orbitWord F z-
        orbitWord F z*sourceRead F g (primitive sharp m ell)) := by
  have h := actual_fourpoint_operator sharp m ell F g z hz
  have he := original_endpoint_moving_return sharp m ell F g z
  simpa only [gammaOperator] using! additive_return _ _ _ _ _ _ h he

def scalarColumn (a : ScalarIndex) : SourceCoframeVolumeCurrent.CoreEnd :=
  coordinateAction (scalarDirection a)

def scalarMoment (f : QuantumTest) : ℝ := ∑ a : ScalarIndex, ‖embed (scalarColumn a f)‖^2

private theorem column_square (z : SourceCoordinateSlice) :
    ∑ a : ScalarIndex, (coordinate (scalarDirection a) z)^2=‖(z.2.1 : Scalar)‖^2 :=
  scalarBasis.sum_sq_inner_left (z.2.1 : Scalar)

private theorem scalar_columns_action (f : QuantumTest) :
    GaussNativeForm.multiply (fun z => ‖(z.2.1 : Scalar)‖^2)
      (fun _ => (GaussRadialMomentum.scalarCoordinate.contDiff.norm_sq ℝ).contDiffAt) f=
      ∑ a : ScalarIndex, scalarColumn a (scalarColumn a f) := by
  apply DFunLike.ext
  intro z
  change ((‖(z.2.1 : Scalar)‖^2 : ℝ) : ℂ) • f z= _
  simp only [sum_apply]
  change _=∑ a : ScalarIndex, (coordinate (scalarDirection a) z : ℂ) •
    ((coordinate (scalarDirection a) z : ℂ) • f z)
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [column_square]

private theorem local_inverse_source (f : QuantumTest) :
    localAction (inverseVolumeAction f)=(sourceTime 0 : ℂ) •
      (∑ a : ScalarIndex, scalarColumn a (scalarColumn a f)+(3 : ℂ) • f) := by
  rw [←scalar_columns_action]
  apply DFunLike.ext
  intro z
  change (localPotential z : ℂ) • ((reciprocalVolume z : ℂ) • f z)=
    (sourceTime 0 : ℂ) • (((‖(z.2.1 : Scalar)‖^2 : ℝ) : ℂ) • f z+(3 : ℂ) • f z)
  by_cases hz : z∈physicalChart
  · have hv := (volume_pos ⟨z,hz⟩).ne'
    have hc : localPotential z*reciprocalVolume z=sourceTime 0*(‖(z.2.1 : Scalar)‖^2+3) := by
      unfold localPotential GaussCoframeForm.volumePotential reciprocalVolume
      rw [real_inner_self_eq_norm_sq]
      field_simp
    rw [smul_smul,←Complex.ofReal_mul,hc]
    push_cast
    module
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))]
    simp only [smul_zero,add_zero]

/-- The original inverse-volume square reads the unweighted scalar moment, with its exact mass term. -/
theorem local_scalar_moment (f : QuantumTest) :
    (sourcePair (inverseRootAction f) (localAction (inverseRootAction f))).re=
      sourceTime 0*(scalarMoment f+3*‖embed f‖^2) := by
  have hcomm : inverseRootAction (localAction (inverseRootAction f))=
      localAction (inverseRootAction (inverseRootAction f)) :=
    LinearMap.congr_fun (inverse_root_real _ _).eq (inverseRootAction f)
  have hp := (multiply_pair inverseRootVolume inverse_root_volume_smooth f (localAction (inverseRootAction f))).symm
  change sourcePair (inverseRootAction f) (localAction (inverseRootAction f))=
      sourcePair f (inverseRootAction (localAction (inverseRootAction f))) at hp
  rw [hcomm,inverse_root_square,local_inverse_source] at hp
  have hcol (a : ScalarIndex) :
      sourcePair f (scalarColumn a (scalarColumn a f))=
        sourcePair (scalarColumn a f) (scalarColumn a f) :=
    multiply_pair (coordinate (scalarDirection a))
      (fun _ => (GaussRadialMomentum.scalarCoordinate.contDiff.inner ℝ contDiff_const).contDiffAt) _ _
  have hreal := congrArg Complex.re hp
  simp only [sourcePair,map_smul,map_add,map_sum,inner_smul_right,inner_add_right,inner_sum] at hreal
  change (sourcePair (inverseRootAction f) (localAction (inverseRootAction f))).re=
    ((sourceTime 0 : ℂ)*((∑ a : ScalarIndex, sourcePair f (scalarColumn a (scalarColumn a f)))+
      (3 : ℂ)*sourcePair f f)).re at hreal
  simp_rw [hcol] at hreal
  have hsreal (u : QuantumTest) : (sourcePair u u).re=‖embed u‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (embed u)
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_sum,zero_mul,sub_zero] at hreal
  norm_num at hreal
  simpa only [hsreal,scalarMoment] using! hreal

/-- Exact scalar comparison extracted from the signed original Hamiltonian; matter and spatial terms remain. -/
theorem signed_scalar_moment (f : QuantumTest) :
    (3*(sourceTime 0)^2/2)*scalarMoment f=
      ‖embed (diagonalAction f)‖^2-
      ‖embed (SourceOriginalHamiltonianSquare.symmetricScale (inverseVolumeAction f))‖^2-
      4*radialCoefficient^2*‖embed (dilation (inverseVolumeAction f))‖^2-
      sourceTime 0*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re-
      (sourceTime 0/2)*(sourcePair (inverseRootAction f) (GaussMatterCore.matterAction (inverseRootAction f))).re-
      sourceTime 0*(sourcePair (inverseRootAction f) (spatialAction (inverseRootAction f))).re-
      (9*(sourceTime 0)^2/2)*‖embed f‖^2 := by
  have h := physical_hamiltonian_square f
  rw [signedCost,local_scalar_moment] at h
  nlinarith only [h]

/-- The first actual finite-source cost contains the complete projection defect, including all grade cross terms. -/
theorem actual_scalar_moment (F : Index) (z : ℂ) (hz : z.im≠0) (g : OriginalCore) :
    let f := coreEquiv.symm (sourceCore F z hz g)
    (3*(sourceTime 0)^2/2)*scalarMoment f=
      ‖(g : H)+z • finiteResolvent F z (g : H)+finiteProjectionDefect F z hz g‖^2-
      ‖embed (SourceOriginalHamiltonianSquare.symmetricScale (inverseVolumeAction f))‖^2-
      4*radialCoefficient^2*‖embed (dilation (inverseVolumeAction f))‖^2-
      sourceTime 0*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re-
      (sourceTime 0/2)*(sourcePair (inverseRootAction f) (GaussMatterCore.matterAction (inverseRootAction f))).re-
      sourceTime 0*(sourcePair (inverseRootAction f) (spatialAction (inverseRootAction f))).re-
      (9*(sourceTime 0)^2/2)*‖embed f‖^2 := by
  dsimp only
  have h := signed_scalar_moment (coreEquiv.symm (sourceCore F z hz g))
  have ha : embed (diagonalAction (coreEquiv.symm (sourceCore F z hz g)))=
      (g : H)+z • finiteResolvent F z (g : H)+finiteProjectionDefect F z hz g :=
    by simpa only using! source_core_action F z hz g
  have hn := congrArg (fun x : H => ‖x‖^2) ha
  linarith only [h,hn]

private theorem shifted_expansion (A : CoreEnd) :
    shiftedProjected A=jet 3 A+(12 : ℂ) • jet 2 A+(44 : ℂ) • jet 1 A+(48 : ℂ) • jet 0 A := by
  simp only [jet,Function.iterate_succ_apply,Function.iterate_zero_apply,
    shiftedProjected,shiftedDerivative,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,
    map_add,map_smul]
  module
private theorem nat_smul_operator (n : ℕ) (A : H →L[ℂ] H) :
    (n : ℂ) • A=(n : H →L[ℂ] H)*A :=
  (Nat.cast_smul_eq_nsmul ℂ n A).trans (nsmul_eq_mul n A)

private theorem raw_polynomial_read (sharp : Bool) (m ell : ℕ) (F : Index) (g : OriginalCore) :
    rawPolynomial sharp m ell F g=
      sourceRead F g (shiftedProjected (force diagonalAction (primitive sharp m ell))) := by
  rw [shifted_expansion]
  simp only [map_add,map_smul]
  change rawPolynomial sharp m ell F g=rawJet sharp m ell F g 3+
    (12 : ℂ) • rawJet sharp m ell F g 2+(44 : ℂ) • rawJet sharp m ell F g 1+
      (48 : ℂ) • rawJet sharp m ell F g 0
  have h12 : (12 : ℂ) • rawJet sharp m ell F g 2=12*rawJet sharp m ell F g 2 := by
    simpa only [Nat.cast_ofNat] using! nat_smul_operator 12 (rawJet sharp m ell F g 2)
  have h44 : (44 : ℂ) • rawJet sharp m ell F g 1=44*rawJet sharp m ell F g 1 := by
    simpa only [Nat.cast_ofNat] using! nat_smul_operator 44 (rawJet sharp m ell F g 1)
  have h48 : (48 : ℂ) • rawJet sharp m ell F g 0=48*rawJet sharp m ell F g 0 := by
    simpa only [Nat.cast_ofNat] using! nat_smul_operator 48 (rawJet sharp m ell F g 0)
  simpa only [rawPolynomial] using!
    congrArg₂ (fun A B : H →L[ℂ] H => A+B)
      (congrArg₂ (fun A B : H →L[ℂ] H => A+B)
        (congrArg (fun A : H →L[ℂ] H => rawJet sharp m ell F g 3+A) h12.symm)
        h44.symm) h48.symm

private theorem raw_source (sharp : Bool) (m ell : ℕ) (F : Index) (g : OriginalCore) :
    rawPolynomial sharp m ell F g=
      (-96*(sourceTime 0 : ℂ)^2) • sourceRead F g (scalarAction sharp*thetaAction m ell) := by
  have h1 := raw_polynomial_read sharp m ell F g
  have h2 := congrArg (sourceRead F g) (source_mixed_force sharp m ell)
  have h3 : sourceRead F g ((-96*(sourceTime 0 : ℂ)^2) • (scalarAction sharp*thetaAction m ell))=
      (-96*(sourceTime 0 : ℂ)^2) • sourceRead F g (scalarAction sharp*thetaAction m ell) := map_smul _ _ _
  exact h1.trans (h2.trans h3)

private theorem pair_sub_i {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (k a b : E) : inner ℂ k (a-Complex.I • b)=inner ℂ k a-Complex.I*inner ℂ k b := by
  rw [inner_sub_right,inner_smul_right]

private theorem actual_pair_sub_i (k a b : H) :
    inner ℂ k (a-Complex.I • b)=inner ℂ k a-Complex.I*inner ℂ k b := by
  simpa only using! pair_sub_i k a b

private theorem actual_pair_smul (k a : H) (c : ℂ) : inner ℂ k (c • a)=c*inner ℂ k a := by
  simpa only using! inner_smul_right k a c

private theorem gamma_applied_normal (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : OriginalCore) (z : ℂ) (hz : z.im≠0) :
    gammaOperator sharp m ell F g z (g : H)=
      finiteResolvent F z (rawPolynomial sharp m ell F g (finiteResolvent F z (g : H)))-
        Complex.I • ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
          orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H)) := by
  have hv0 := congrArg (fun A : H →L[ℂ] H => A (g : H))
    (gamma_normal_form sharp m ell F g z hz)
  have hv1 :
      (finiteResolvent F z*rawPolynomial sharp m ell F g*finiteResolvent F z-
        Complex.I • (sourceRead F g (primitive sharp m ell)*orbitWord F z-
          orbitWord F z*sourceRead F g (primitive sharp m ell))) (g : H)=
      finiteResolvent F z (rawPolynomial sharp m ell F g (finiteResolvent F z (g : H)))-
        Complex.I • ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
          orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H)) := by
    simp only [sub_apply,smul_apply,mul_apply_eq_comp]
  exact hv0.trans hv1

private theorem gamma_pair_normal (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : OriginalCore) (z : ℂ) (hz : z.im≠0) :
    sourceGamma sharp m ell F g k z=
      inner ℂ (k : H) (finiteResolvent F z
        (rawPolynomial sharp m ell F g (finiteResolvent F z (g : H))))-
      Complex.I*inner ℂ (k : H)
        ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
          orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H)) := by
  have hg : (g : H)=Subtype.val g := rfl
  have hk : (k : H)=Subtype.val k := rfl
  have hgOp := congrArg (gammaOperator sharp m ell F g z) hg
  have hv := hgOp.symm.trans (gamma_applied_normal sharp m ell F g z hz)
  have hp := congrArg (fun x : H => inner ℂ (Subtype.val k) x) hv
  have ho := actual_pair_sub_i (Subtype.val k)
    (finiteResolvent F z (rawPolynomial sharp m ell F g (finiteResolvent F z (g : H))))
    ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
      orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))
  have hkPair := congrArg (fun x : H =>
    inner ℂ x (finiteResolvent F z (rawPolynomial sharp m ell F g (finiteResolvent F z (g : H))))-
    Complex.I*inner ℂ x ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
      orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))) hk.symm
  exact (source_gamma_scalar sharp m ell F g k z).trans (hp.trans (ho.trans hkPair))

/-- The complete Gamma numerator is the original scalar insertion, with the genuine moving orbit current. -/
theorem gamma_source_return (sharp : Bool) (m ell : ℕ) (F : Index) (g k : OriginalCore)
    (z : ℂ) (hz : z.im≠0) :
    sourceGamma sharp m ell F g k z=
      (-96*(sourceTime 0 : ℂ)^2)*inner ℂ (k : H)
        (finiteResolvent F z (embed (scalarAction sharp (thetaAction m ell
          (coreEquiv.symm (sourceCore F z hz g))))))-
      Complex.I*inner ℂ (k : H)
        ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
          orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H)) := by
  have hv := gamma_pair_normal sharp m ell F g k z hz
  have hx0 := congrArg (fun A : H →L[ℂ] H => A (finiteResolvent F z (g : H)))
    (raw_source sharp m ell F g)
  have hx1 := congrArg (fun x : H => (-96*(sourceTime 0 : ℂ)^2) • x)
    (source_read_resolvent F g (scalarAction sharp*thetaAction m ell) z hz)
  have hx : rawPolynomial sharp m ell F g (finiteResolvent F z (g : H))=
      (-96*(sourceTime 0 : ℂ)^2) • embed (scalarAction sharp
        (thetaAction m ell (coreEquiv.symm (sourceCore F z hz g)))) := hx0.trans hx1
  have hi0 := congrArg (fun x : H => inner ℂ (k : H) (finiteResolvent F z x)) hx
  have hi1 := congrArg (fun x : H => inner ℂ (k : H) x)
    (map_smul (finiteResolvent F z) (-96*(sourceTime 0 : ℂ)^2)
      (embed (scalarAction sharp (thetaAction m ell (coreEquiv.symm (sourceCore F z hz g))))))
  have hi2 := actual_pair_smul (k : H)
    (finiteResolvent F z (embed (scalarAction sharp
      (thetaAction m ell (coreEquiv.symm (sourceCore F z hz g)))))) (-96*(sourceTime 0 : ℂ)^2)
  have hi := hi0.trans (hi1.trans hi2)
  exact hv.trans (congrArg (fun x : ℂ => x-Complex.I*inner ℂ (k : H)
    ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
      orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))) hi)

def scalarContact (m ell : ℕ) : SourceCoframeVolumeCurrent.CoreEnd :=
  (1/2 : ℂ) • ∑ a : ScalarIndex,
    (GaussMomentumAdjoint.adjoint (scalarDirection a)*
      GaussNativeForm.multiply scalarWeight scalarWeight_smooth*
        SourceNativeCutoffContact.contactAction (scalarDirection a) m ell+
    SourceNativeCutoffContact.contactAction (scalarDirection a) m ell*
      GaussNativeForm.multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a))

private theorem sandwich_contact {R : Type*} [Ring R] (a b w t c : R)
    (ha : a*t=t*a+c) (hb : b*t=t*b+c) (hw : w*t=t*w) :
    (a*w*b)*t=t*(a*w*b)+(a*w*c+c*w*b) := by
  calc
    _=a*w*(b*t) := by noncomm_ring
    _=a*w*(t*b+c) := by rw [hb]
    _=a*(w*t)*b+a*w*c := by noncomm_ring
    _=(a*t)*w*b+a*w*c := by rw [hw]; noncomm_ring
    _=_ := by rw [ha]; noncomm_ring

private theorem scalar_contact_source (m ell : ℕ) :
    scalarKinetic*thetaAction m ell=thetaAction m ell*scalarKinetic+scalarContact m ell := by
  have ht : SourceNativeCutoffContact.thetaAction m ell=thetaAction m ell :=
    SourceNativeCutoffContact.theta_action_polynomial m ell
  have hs (a : ScalarIndex) :
      sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth*thetaAction m ell=
      thetaAction m ell*sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth+
        (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
          SourceNativeCutoffContact.contactAction (scalarDirection a) m ell+
        SourceNativeCutoffContact.contactAction (scalarDirection a) m ell*
          multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) := by
    have ha : GaussMomentumAdjoint.adjoint (scalarDirection a)*thetaAction m ell=
        thetaAction m ell*GaussMomentumAdjoint.adjoint (scalarDirection a)+
          SourceNativeCutoffContact.contactAction (scalarDirection a) m ell := by
      apply LinearMap.ext
      intro f
      simpa only [Module.End.mul_apply,LinearMap.add_apply,←ht] using!
        SourceNativeCutoffContact.sharp_core_contact (scalarDirection a) m ell f
    have hb : covariantMomentum (scalarDirection a)*thetaAction m ell=
        thetaAction m ell*covariantMomentum (scalarDirection a)+
          SourceNativeCutoffContact.contactAction (scalarDirection a) m ell := by
      apply LinearMap.ext
      intro f
      simpa only [Module.End.mul_apply,LinearMap.add_apply,←ht] using!
        SourceNativeCutoffContact.native_core_contact (scalarDirection a) m ell f
    have hw : multiply scalarWeight scalarWeight_smooth*thetaAction m ell=
        thetaAction m ell*multiply scalarWeight scalarWeight_smooth := by
      rw [←ht]
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro z
      exact smul_comm (scalarWeight z : ℂ) (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)
    simpa only [sandwich,←Module.End.mul_eq_comp,mul_assoc] using!
      sandwich_contact (R := SourceCoframeVolumeCurrent.CoreEnd) _ _ _ _ _ ha hb hw
  simp only [scalarKinetic,scalarContact,smul_mul_assoc,Finset.sum_mul,hs,
    Finset.sum_add_distrib,←Finset.mul_sum,mul_smul_comm,smul_add]

private theorem cutoff_complement {R : Type*} [Ring R] (a b u : R) (m ell : ℕ)
    (hu : (a-b)*u=u*(a-b)) :
    (a-b)*((1-u)^(m+1)-(1-u)^(ell+1))=
      ((1-u)^(m+1)-(1-u)^(ell+1))*(a-b) :=
  ((((Commute.one_right (a-b)).sub_right hu).pow_right (m+1)).sub_right
    (((Commute.one_right (a-b)).sub_right hu).pow_right (ell+1))).eq

private theorem subtract_contact {R : Type*} [Ring R] (a b t c : R)
    (h : (a-b)*t=t*(a-b)) (hb : b*t=t*b+c) : a*t=t*a+c := by
  rw [sub_mul,mul_sub,hb] at h
  have hc : a*t-t*a=c := by
    calc
      a*t-t*a = (a*t-(t*b+c)-(t*a-t*b))+c := by abel
      _ = c := by rw [h,sub_self,zero_add]
  exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)

private theorem subtract_same_contact {R : Type*} [Ring R] (a b u c : R)
    (ha : a*u=u*a+c) (hb : b*u=u*b+c) : (a-b)*u=u*(a-b) := by
  rw [sub_mul,mul_sub,ha,hb]
  abel

/-- Every non-scalar source term commutes with this literal cutoff; the remaining contact has its original negative weight. -/
theorem full_cutoff_contact (m ell : ℕ) :
    diagonalAction*thetaAction m ell=thetaAction m ell*diagonalAction+scalarContact m ell := by
  have hr : (diagonalAction-scalarKinetic)*GaussRadialDomain.inverseAction=
      GaussRadialDomain.inverseAction*(diagonalAction-scalarKinetic) := by
    simpa only using! subtract_same_contact (R := SourceCoframeVolumeCurrent.CoreEnd)
      diagonalAction scalarKinetic GaussRadialDomain.inverseAction GaussRadialHamiltonian.radialAction
      GaussRadialHamiltonian.diagonal_commutator GaussRadialHamiltonian.scalar_commutator
  have ht : (diagonalAction-scalarKinetic)*thetaAction m ell=
      thetaAction m ell*(diagonalAction-scalarKinetic) :=
    cutoff_complement (R := SourceCoframeVolumeCurrent.CoreEnd) _ _ _ m ell hr
  exact subtract_contact (R := SourceCoframeVolumeCurrent.CoreEnd) _ _ _ _ ht
    (scalar_contact_source m ell)

/-- Cutoff applied to the actual source leaves a weighted first-order contact on q_F and the full projected defect. -/
theorem actual_cutoff_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : OriginalCore) :
    let f := coreEquiv.symm (sourceCore F z hz g)
    embed (diagonalAction (thetaAction m ell f))=
      relativeTail m ell ((g : H)+z • finiteResolvent F z (g : H)+finiteProjectionDefect F z hz g)+
        embed (scalarContact m ell f) := by
  dsimp only
  have h := congrArg embed (LinearMap.congr_fun (full_cutoff_contact m ell)
    (coreEquiv.symm (sourceCore F z hz g)))
  simp only [Module.End.mul_apply,LinearMap.add_apply,map_add,←SourceMixedNativeReturn.theta_core] at h
  rw [show embed (diagonalAction (coreEquiv.symm (sourceCore F z hz g)))=
    (g : H)+z • finiteResolvent F z (g : H)+finiteProjectionDefect F z hz g from source_core_action F z hz g] at h
  exact h

private theorem scalar_column_return (sharp : Bool) (f : QuantumTest) :
    embed (scalarAction sharp f)=∑ a : ScalarIndex,
      constantBounded sharp (scalarBasis a) (embed (scalarColumn a f)) := by
  have hcore : scalarAction sharp f=∑ a : ScalarIndex,
      constantAction sharp (scalarBasis a) (scalarColumn a f) := by
    apply DFunLike.ext
    intro z
    simp only [sum_apply]
    change branchMap sharp (z.2.1 : Scalar) (f z)=
      ∑ a : ScalarIndex,branchMap sharp (scalarBasis a)
        ((inner ℝ (z.2.1 : Scalar) (scalarBasis a) : ℂ) • f z)
    have he : ∑ a : ScalarIndex,(inner ℝ (z.2.1 : Scalar) (scalarBasis a)) • scalarBasis a=
        (z.2.1 : Scalar) := by
      simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm] using
        scalarBasis.sum_repr (z.2.1 : Scalar)
    conv_lhs => rw [←he,map_sum,sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul,map_smul]
    rfl
  rw [hcore,map_sum]
  exact Finset.sum_congr rfl (fun a _ => (constant_bounded_core sharp (scalarBasis a) _).symm)

private theorem finite_column_estimate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (a : ι → E →L[ℂ] E) (x : ι → E) :
    ‖∑ i, a i (x i)‖^2≤(∑ i, ‖a i‖^2)*(∑ i, ‖x i‖^2) := by
  have h := (norm_sum_le Finset.univ (fun i : ι => a i (x i))).trans (Finset.sum_le_sum (fun i _ => (a i).le_opNorm (x i)))
  have hp : 0≤∑ i, ‖a i‖*‖x i‖ := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq : ‖∑ i, a i (x i)‖^2≤(∑ i, ‖a i‖*‖x i‖)^2 :=
    sq_le_sq₀ (norm_nonneg _) hp |>.mpr h
  exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖a i‖) (fun i => ‖x i‖))

/-- Both original coefficient branches consume the extracted scalar moment on the original Hilbert carrier. -/
theorem scalar_insertion_estimate (sharp : Bool) (f : QuantumTest) :
    ‖embed (scalarAction sharp f)‖^2≤
      (∑ a : ScalarIndex, ‖constantBounded sharp (scalarBasis a)‖^2)*scalarMoment f := by
  have hs := finite_column_estimate
    (fun a : ScalarIndex => constantBounded sharp (scalarBasis a))
    (fun a : ScalarIndex => embed (scalarColumn a f))
  have hn := congrArg (fun x : H => ‖x‖^2) (scalar_column_return sharp f)
  change ‖∑ a : ScalarIndex, constantBounded sharp (scalarBasis a) (embed (scalarColumn a f))‖^2≤
    (∑ a : ScalarIndex, ‖constantBounded sharp (scalarBasis a)‖^2)*scalarMoment f at hs
  exact hn.trans_le hs

private theorem scalar_pair_estimate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (k x : E) (r : E →L[ℂ] E) (a : ℂ) (b : ℝ)
    (hx : ‖x‖^2≤b) : ‖a*inner ℂ k (r x)‖^2≤‖a‖^2*‖k‖^2*‖r‖^2*b := by
  have h := (norm_inner_le_norm (𝕜 := ℂ) k (r x)).trans
    (mul_le_mul_of_nonneg_left (r.le_opNorm x) (norm_nonneg k))
  have hs : ‖inner ℂ k (r x)‖^2≤‖k‖^2*‖r‖^2*‖x‖^2 := by
    have hn := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg k)
      (mul_nonneg (norm_nonneg r) (norm_nonneg x)))).mpr h
    simpa only [mul_pow,mul_assoc] using hn
  rw [norm_mul,mul_pow]
  calc
    _ ≤ ‖a‖^2*(‖k‖^2*‖r‖^2*‖x‖^2) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ ≤ ‖a‖^2*(‖k‖^2*‖r‖^2*b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (mul_nonneg (sq_nonneg _) (sq_nonneg _))) (sq_nonneg _)
    _ = _ := by ring

/-- A source-generated scalar estimate for the complete Gamma plus its already-generated moving current. -/
theorem gamma_scalar_estimate (sharp : Bool) (m ell : ℕ) (F : Index) (g k : OriginalCore)
    (z : ℂ) (hz : z.im≠0) :
    ‖sourceGamma sharp m ell F g k z+Complex.I*inner ℂ (k : H)
      ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
        orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))‖^2≤
      ‖-96*(sourceTime 0 : ℂ)^2‖^2*‖(k : H)‖^2*‖finiteResolvent F z‖^2*
        ((∑ a : ScalarIndex, ‖constantBounded sharp (scalarBasis a)‖^2)*
          scalarMoment (thetaAction m ell (coreEquiv.symm (sourceCore F z hz g)))) := by
  have h := gamma_source_return sharp m ell F g k z hz
  have hs := scalar_pair_estimate (k : H)
    (embed (scalarAction sharp (thetaAction m ell (coreEquiv.symm (sourceCore F z hz g)))))
    (finiteResolvent F z) (-96*(sourceTime 0 : ℂ)^2) _
    (scalar_insertion_estimate sharp _)
  exact (congrArg (fun w : ℂ => ‖w‖^2) (eq_sub_iff_add_eq.mp h)).trans_le hs

end LowEnergy.SourceGammaNativeBudget
