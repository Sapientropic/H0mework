import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceMixedCurrentJets
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceMixedNativeReturn
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussCoframeForm GaussDiagonalHistory
open GaussYukawaCoefficient GaussRadialDomain GaussLiveMomentum GaussQuantumMultiplier
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolumeCurrent SourceCoframeDilation SourceEulerCore
open SourceDilationRemainder SourceHamiltonianScaleJet SourceDilationAlgebra SourceCutoffDilationWard
open SourceClosedCostNativeProbe SourceJointScaleBudget SourceEscapeCurrent
open FullYSourceResolventGraphSplice GaussUnitaryHistory SourceRelativePowerTail
open scoped ContDiff InnerProductSpace RealInnerProductSpace


section JetAlgebra
variable {R : Type*} [Ring R]
private theorem jet_endpoint_return (l r a b c t u v w : R)
    (hl : l*r=1) (hr : r*l=1) :
    sandwichJet0 r (commJet0 l t)=endpointJet0 r t ∧
    sandwichJet1 r (inverseJet1 r a) (commJet0 l t) (commJet1 l a t u)=
      endpointJet1 r (inverseJet1 r a) t u ∧
    sandwichJet2 r (inverseJet1 r a) (inverseJet2 r a b)
      (commJet0 l t) (commJet1 l a t u) (commJet2 l a b t u v)=
      endpointJet2 r (inverseJet1 r a) (inverseJet2 r a b) t u v ∧
    sandwichJet3 r (inverseJet1 r a) (inverseJet2 r a b) (inverseJet3 r a b c)
      (commJet0 l t) (commJet1 l a t u) (commJet2 l a b t u v) (commJet3 l a b c t u v w)=
      endpointJet3 r (inverseJet1 r a) (inverseJet2 r a b) (inverseJet3 r a b c) t u v w := by
  have hrx (x : R) : r*(l*x)=x := by rw [←mul_assoc,hr,one_mul]
  have hlx (x : R) : l*(r*x)=x := by rw [←mul_assoc,hl,one_mul]
  constructor
  · unfold sandwichJet0 commJet0 endpointJet0
    noncomm_ring [hrx,hlx,hl]
  constructor
  · unfold sandwichJet1 commJet0 commJet1 endpointJet1 inverseJet1
    noncomm_ring [hrx,hlx,hl]
  constructor
  · unfold sandwichJet2 commJet0 commJet1 commJet2 endpointJet2 inverseJet1 inverseJet2
    noncomm_ring [hrx,hlx,hl]
  · unfold sandwichJet3 commJet0 commJet1 commJet2 commJet3 endpointJet3 inverseJet1 inverseJet2 inverseJet3
    noncomm_ring [hrx,hlx,hl]

private theorem sandwich_polynomial (r r1 r2 r3 b b1 b2 b3 : R) :
    sandwichJet3 r r1 r2 r3 b b1 b2 b3+12*sandwichJet2 r r1 r2 b b1 b2+
      44*sandwichJet1 r r1 b b1+48*sandwichJet0 r b=
    r*(b3+12*b2+44*b1+48*b)*r+leibnizOther r r1 r2 r3 b b1 b2 := by
  unfold sandwichJet3 sandwichJet2 sandwichJet1 sandwichJet0 leibnizOther
  noncomm_ring
end JetAlgebra
private theorem current_zero (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) :
    currentJet sharp m ell F g z 0=Complex.I •
      (GaussGradedCompression.compression F*sourceRead F g (primitive sharp m ell)-
        sourceRead F g (primitive sharp m ell)*GaussGradedCompression.compression F) := by
  simp only [currentJet,Matrix.cons_val_zero,commJet0,primitiveJet,pow_zero,one_smul,sub_mul,mul_sub,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  module

private theorem sandwich_split {R : Type*} [Ring R] (r b c : Fin 4 → R) :
    sandwichPolynomial r b=sandwichPolynomial r c+sandwichPolynomial r (fun j => b j-c j) := by
  unfold sandwichPolynomial sandwichJet0 sandwichJet1 sandwichJet2 sandwichJet3
  noncomm_ring

private theorem operator_sandwich_polynomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (r G : Fin 4 → E →L[ℂ] E) :
    sandwichPolynomial r G=(r 0)*(G 3+12*G 2+44*G 1+48*G 0)*(r 0)+
      leibnizOther (r 0) (r 1) (r 2) (r 3) (G 0) (G 1) (G 2) := by
  simpa only [sandwichPolynomial] using! sandwich_polynomial (R := E →L[ℂ] E)
    (r 0) (r 1) (r 2) (r 3) (G 0) (G 1) (G 2) (G 3)

private theorem forced_endpoint {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (l r a b c t u v w : R) (hl : l*r=1) (hr : r*l=1) :
    sandwichJet0 r (Complex.I • commJet0 l t)=Complex.I • endpointJet0 r t ∧
    sandwichJet1 r (inverseJet1 r a) (Complex.I • commJet0 l t) (Complex.I • commJet1 l a t u)=
      Complex.I • endpointJet1 r (inverseJet1 r a) t u ∧
    sandwichJet2 r (inverseJet1 r a) (inverseJet2 r a b)
      (Complex.I • commJet0 l t) (Complex.I • commJet1 l a t u) (Complex.I • commJet2 l a b t u v)=
      Complex.I • endpointJet2 r (inverseJet1 r a) (inverseJet2 r a b) t u v ∧
    sandwichJet3 r (inverseJet1 r a) (inverseJet2 r a b) (inverseJet3 r a b c)
      (Complex.I • commJet0 l t) (Complex.I • commJet1 l a t u)
      (Complex.I • commJet2 l a b t u v) (Complex.I • commJet3 l a b c t u v w)=
      Complex.I • endpointJet3 r (inverseJet1 r a) (inverseJet2 r a b) (inverseJet3 r a b c) t u v w := by
  have h := jet_endpoint_return l r a b c t u v w hl hr
  constructor
  · convert congrArg (fun A => Complex.I • A) h.1 using 1
    simp only [sandwichJet0,smul_mul_assoc,mul_smul_comm]
  constructor
  · convert congrArg (fun A => Complex.I • A) h.2.1 using 1
    simp only [sandwichJet1,smul_mul_assoc,mul_smul_comm,←smul_add]
  constructor
  · convert congrArg (fun A => Complex.I • A) h.2.2.1 using 1
    simp only [sandwichJet2,smul_mul_assoc,mul_smul_comm,←smul_add]
  · convert congrArg (fun A => Complex.I • A) h.2.2.2 using 1
    simp only [sandwichJet3,smul_mul_assoc,mul_smul_comm,←smul_add]

private theorem scalar_polynomial {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (c : ℂ) (a b d e : R) :
    c • a+12*(c • b)+44*(c • d)+48*(c • e)=c • (a+12*b+44*d+48*e) := by
  simp only [mul_smul_comm,←smul_add]

set_option maxHeartbeats 200000 in
theorem actual_fourpoint_operator (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z*rawPolynomial sharp m ell F g*finiteResolvent F z=
      endpointPolynomial sharp m ell F g z+omegaResponse sharp m ell F g z-
        leibnizResponse sharp m ell F g z := by
  let r := inverseJet F z
  let b := currentJet sharp m ell F g z
  let G : Fin 4 → H →L[ℂ] H := fun j => rawJet sharp m ell F g j
  let T := primitiveJet sharp m ell F g
  have h := forced_endpoint (R := H →L[ℂ] H)
    (GaussGradedCompression.compression F-z • 1) (finiteResolvent F z)
    (compressionJet F 1) (compressionJet F 2) (compressionJet F 3) (T 0) (T 1) (T 2) (T 3)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
    (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  have h0 : sandwichJet0 (r 0) (b 0)=Complex.I • endpointJet0 (r 0) (T 0) := h.1
  have h1 : sandwichJet1 (r 0) (r 1) (b 0) (b 1)=Complex.I • endpointJet1 (r 0) (r 1) (T 0) (T 1) := h.2.1
  have h2 : sandwichJet2 (r 0) (r 1) (r 2) (b 0) (b 1) (b 2)=
      Complex.I • endpointJet2 (r 0) (r 1) (r 2) (T 0) (T 1) (T 2) := h.2.2.1
  have h3 : sandwichJet3 (r 0) (r 1) (r 2) (r 3) (b 0) (b 1) (b 2) (b 3)=
      Complex.I • endpointJet3 (r 0) (r 1) (r 2) (r 3) (T 0) (T 1) (T 2) (T 3) := h.2.2.2
  have hc : sandwichPolynomial r b=endpointPolynomial sharp m ell F g z := by
    have he := congrArg₂ (fun a b : H →L[ℂ] H => a+b)
      (congrArg₂ (fun a b : H →L[ℂ] H => a+b)
        (congrArg₂ (fun a b : H →L[ℂ] H => a+b) h3 (congrArg (fun A : H →L[ℂ] H => 12*A) h2))
        (congrArg (fun A : H →L[ℂ] H => 44*A) h1))
      (congrArg (fun A : H →L[ℂ] H => 48*A) h0)
    exact he.trans (scalar_polynomial Complex.I _ _ _ _)
  have hs0 := sandwich_split (R := H →L[ℂ] H) r G b
  have ho : (fun j => G j-b j)=omegaJet sharp m ell F g z := by
    funext j
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hs1 := congrArg (fun B : Fin 4 → H →L[ℂ] H =>
    sandwichPolynomial r b+sandwichPolynomial r B) ho
  have hs2 := hs0.trans hs1
  have homega : sandwichPolynomial r (omegaJet sharp m ell F g z)=omegaResponse sharp m ell F g z := rfl
  have hs : sandwichPolynomial r G=sandwichPolynomial r b+omegaResponse sharp m ell F g z :=
    hs2.trans (congrArg (fun A : H →L[ℂ] H => sandwichPolynomial r b+A) homega)
  have hp0 := operator_sandwich_polynomial r G
  have hraw : G 3+12*G 2+44*G 1+48*G 0=rawPolynomial sharp m ell F g := rfl
  have hbase : r 0=finiteResolvent F z := rfl
  have hprod := congrArg₂ (fun A B : H →L[ℂ] H => A*B*A) hbase hraw
  have hl : leibnizOther (r 0) (r 1) (r 2) (r 3) (G 0) (G 1) (G 2)=
      leibnizResponse sharp m ell F g z := rfl
  have hp : sandwichPolynomial r G=finiteResolvent F z*rawPolynomial sharp m ell F g*finiteResolvent F z+
      leibnizResponse sharp m ell F g z :=
    hp0.trans (congrArg₂ (fun A B : H →L[ℂ] H => A+B) hprod hl)
  have he := hp.symm.trans (hs.trans (congrArg (fun A : H →L[ℂ] H => A+omegaResponse sharp m ell F g z) hc))
  exact eq_sub_iff_add_eq.mpr he

def mixedResponse (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain) (z : ℂ) : ℂ :=
  (-96*(sourceTime 0 : ℂ)^2)*inner ℂ (k : H)
    (finiteResolvent F z (constantBounded sharp vacuum (relativeTail m ell (finiteResolvent F z (g : H)))))+
  inner ℂ (k : H) ((endpointPolynomial sharp m ell F g z+omegaResponse sharp m ell F g z-
    leibnizResponse sharp m ell F g z) (g : H))-
  (-96*(sourceTime 0 : ℂ)^2)*inner ℂ (k : H)
    (SourceHardyRetardedTail.particular sharp m ell F z (g : H)+
      z • finiteResolvent F z (SourceHardyRetardedTail.particular sharp m ell F z (g : H)))

/-- The original signed J, both coefficient branches and every finite carrier channel are returned together. -/
theorem source_mixed_fourpoint_return (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    (-96*(sourceTime 0 : ℂ)^2)*SourceJointResidualEnergy.jointResidual sharp m ell F z hz g k=
      mixedResponse sharp m ell F g k z := by
  have hi := SourceCornerPartition.actual_full_increment_splice sharp m ell F z hz g k
  have hm := congrArg (fun x : H => inner ℂ (k : H) (finiteResolvent F z x))
    (actual_mixed_insertion sharp m ell F g z hz)
  simp only [map_smul,map_add,inner_smul_right,inner_add_right] at hm
  have hp := congrArg (fun A : H →L[ℂ] H => inner ℂ (k : H) (A (g : H)))
    (actual_fourpoint_operator sharp m ell F g z hz)
  have hp' : inner ℂ (k : H) (finiteResolvent F z
      (rawPolynomial sharp m ell F g (finiteResolvent F z (g : H))))=
      inner ℂ (k : H) ((endpointPolynomial sharp m ell F g z+omegaResponse sharp m ell F g z-
        leibnizResponse sharp m ell F g z) (g : H)) := by
    simpa only [mul_apply_eq_comp] using! hp
  rw [hp'] at hm
  change _=mixedResponse sharp m ell F g k z
  unfold mixedResponse
  have hi' : inner ℂ (k : H) (finiteResolvent F z
      (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H))))=
      inner ℂ (k : H) (SourceHardyRetardedTail.particular sharp m ell F z (g : H)+
        z • finiteResolvent F z (SourceHardyRetardedTail.particular sharp m ell F z (g : H)))+
      SourceJointResidualEnergy.jointResidual sharp m ell F z hz g k := by
    simpa only [SourceJointResidualEnergy.jointResidual,add_assoc] using! hi
  linear_combination hm-(-96*(sourceTime 0 : ℂ)^2)*hi'

/-- The target remains the original closedJointCost, with a completely generated signed return. -/
theorem actual_mixed_closed_energy (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    (∫ t : ℝ, ‖mixedResponse sharp m ell F g k (SourceResolventBandLimit.line μ t)‖^2)=
      ‖(-96*(sourceTime 0 : ℂ)^2)‖^2*
        SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g : H) (k : H) := by
  have he (t : ℝ) := source_mixed_fourpoint_return sharp m ell F g k
    (SourceResolventBandLimit.line μ t) (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne')
  simp_rw [←he,norm_mul,mul_pow]
  rw [MeasureTheory.integral_const_mul,
    SourceFourPoleEnergyClosed.actual_joint_closed_energy sharp m ell F μ hμ g k]


open SourceJointResidualEnergy SourceActualResolventEnergy SourceRetardedIncrement

private theorem basis_eigen (F : Index) (i : SpectralIndex F) :
    GaussGradedCompression.compression F ((SourceJointResidualEnergy.sourceBasis F) i : H)=
      (channelValue F (some i) : ℂ) • ((SourceJointResidualEnergy.sourceBasis F) i : H) := by
  have h := (show (supportAction F).toLinearMap.IsSymmetric from
    (support_action_selfAdjoint F).isSymmetric).apply_eigenvectorBasis rfl i
  simpa only [SourceJointResidualEnergy.sourceBasis,SourceFiniteResolventEnergy.basis,channelValue,
    SourceFiniteResolventEnergy.eigenvalue] using! congrArg (fun x : supportSpan F => (x : H)) h

private theorem channel_some (F : Index) (i : SpectralIndex F) (x : H) :
    channel F (some i) x=inner ℂ ((SourceJointResidualEnergy.sourceBasis F) i : H) x • ((SourceJointResidualEnergy.sourceBasis F) i : H) := by
  rw [channel,OrthonormalBasis.repr_apply_apply]
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

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
    rw [channel_some,channel_some,hp,basis_eigen,inner_smul_left]
    have hc : (starRingEnd ℂ) (channelValue F (some i) : ℂ)=(channelValue F (some i) : ℂ) :=
      Complex.conj_ofReal _
    rw [hc,smul_smul]

private theorem channel_sub (F : Index) (i : Channel F) (x y : H) :
    channel F i (x-y)=channel F i x-channel F i y := by
  cases i <;> simp only [channel,map_sub,PiLp.sub_apply,sub_smul]

private theorem channel_smul (F : Index) (i : Channel F) (c : ℂ) (x : H) :
    channel F i (c • x)=c • channel F i x := by
  cases i <;> simp only [channel,map_smul,PiLp.smul_apply,smul_eq_mul,smul_smul]

private theorem commutator_leg (F : Index) (T : H →L[ℂ] H) (g : H)
    (ij : Channel F × Channel F) :
    spectralLeg F (Complex.I • (GaussGradedCompression.compression F*T-T*GaussGradedCompression.compression F)) g ij=
      (Complex.I*((channelValue F ij.1 : ℂ)-(channelValue F ij.2 : ℂ))) • spectralLeg F T g ij := by
  change channel F ij.1 (Complex.I • (GaussGradedCompression.compression F (T (channel F ij.2 g))-
    T (GaussGradedCompression.compression F (channel F ij.2 g))))=_
  rw [channel_smul,channel_sub,channel_eigen_left,channel_eigen_right,map_smul,channel_smul]
  change Complex.I • ((channelValue F ij.1 : ℂ) • spectralLeg F T g ij-
    (channelValue F ij.2 : ℂ) • spectralLeg F T g ij)=_
  rw [←sub_smul,smul_smul]

/-- The actual graded Hamiltonian gives each complete cross-grade coefficient its real energy gap. -/
theorem actual_current_leg (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (ij : Channel F × Channel F) :
    spectralLeg F (currentJet sharp m ell F g z 0) (g : H) ij=
      (Complex.I*((channelValue F ij.1 : ℂ)-(channelValue F ij.2 : ℂ))) •
        spectralLeg F (sourceRead F g (primitive sharp m ell)) (g : H) ij := by
  rw [current_zero]
  simpa only using! commutator_leg F (sourceRead F g (primitive sharp m ell)) (g : H) ij

private theorem scalar_gap_cross (μ a b c d : ℝ) (hμ : 0<μ) (u v : ℂ) :
    SourceFourPoleEnergyClosed.closedKernel μ a b c d*
      inner ℂ ((Complex.I*((a : ℂ)-(b : ℂ))) • u) ((Complex.I*((c : ℂ)-(d : ℂ))) • v)=
    2*(Real.pi : ℂ)*((SourceFourPoleEnergyClosed.gap μ a c)⁻¹-(SourceFourPoleEnergyClosed.gap μ a d)⁻¹-
      (SourceFourPoleEnergyClosed.gap μ b c)⁻¹+(SourceFourPoleEnergyClosed.gap μ b d)⁻¹)*inner ℂ u v := by
  rw [inner_smul_left,inner_smul_right]
  have hc : (starRingEnd ℂ) (Complex.I*((a : ℂ)-(b : ℂ)))*(Complex.I*((c : ℂ)-(d : ℂ)))=
      ((a : ℂ)-(b : ℂ))*((c : ℂ)-(d : ℂ)) := by
    simp only [map_mul,map_sub,Complex.conj_ofReal,Complex.conj_I]
    calc _= -(Complex.I*Complex.I)*(((a : ℂ)-(b : ℂ))*((c : ℂ)-(d : ℂ))) := by ring
         _=_ := by rw [Complex.I_mul_I]; ring
  calc
    _ = (((a : ℂ)-(b : ℂ))*((c : ℂ)-(d : ℂ))*
      SourceFourPoleEnergyClosed.closedKernel μ a b c d)*inner ℂ u v := by rw [←hc]; ring
    _ = _ := by rw [closed_kernel_gap_reduction μ a b c d hμ]

/-- Actual current cross Gram, including all collisions and the whole NONE channel, consumes the gap producer. -/
theorem actual_current_cross_gram (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) (μ : ℝ) (hμ : 0<μ)
    (ij kl : Channel F × Channel F) :
    SourceFourPoleEnergyClosed.closedKernel μ (channelValue F ij.1) (channelValue F ij.2)
      (channelValue F kl.1) (channelValue F kl.2)*
      inner ℂ (inner ℂ (k : H) (spectralLeg F (currentJet sharp m ell F g z 0) (g : H) ij))
        (inner ℂ (k : H) (spectralLeg F (currentJet sharp m ell F g z 0) (g : H) kl))=
    2*(Real.pi : ℂ)*
      ((SourceFourPoleEnergyClosed.gap μ (channelValue F ij.1) (channelValue F kl.1))⁻¹-
        (SourceFourPoleEnergyClosed.gap μ (channelValue F ij.1) (channelValue F kl.2))⁻¹-
        (SourceFourPoleEnergyClosed.gap μ (channelValue F ij.2) (channelValue F kl.1))⁻¹+
        (SourceFourPoleEnergyClosed.gap μ (channelValue F ij.2) (channelValue F kl.2))⁻¹)*
      inner ℂ (inner ℂ (k : H) (spectralLeg F (sourceRead F g (primitive sharp m ell)) (g : H) ij))
        (inner ℂ (k : H) (spectralLeg F (sourceRead F g (primitive sharp m ell)) (g : H) kl)) := by
  have hi := congrArg (fun x : H => inner ℂ (k : H) x) (actual_current_leg sharp m ell F g z ij)
  have hk := congrArg (fun x : H => inner ℂ (k : H) x) (actual_current_leg sharp m ell F g z kl)
  simp only [inner_smul_right] at hi hk
  have h := scalar_gap_cross μ (channelValue F ij.1) (channelValue F ij.2)
    (channelValue F kl.1) (channelValue F kl.2) hμ
    (inner ℂ (k : H) (spectralLeg F (sourceRead F g (primitive sharp m ell)) (g : H) ij))
    (inner ℂ (k : H) (spectralLeg F (sourceRead F g (primitive sharp m ell)) (g : H) kl))
  rw [hi,hk]
  exact h

end LowEnergy.SourceMixedNativeReturn
