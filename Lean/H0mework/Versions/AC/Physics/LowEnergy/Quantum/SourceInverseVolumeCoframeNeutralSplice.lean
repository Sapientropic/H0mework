import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeCoframeCompressionBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseCoframeNeutralSplice
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceScalarPairedTransport
open SourceInverseCoframeCompressionBudget
open SourceInverseCompressionCurrent SourceInverseGaugeSingleDefectJoin SourceInverseHamiltonianForceReduction
open SourceInverseCoframeNeutralBudget SourceInverseProjectionCurrentRemainder SourceInverseCompressionGaugeBudget
open SourceGaugeCoframeWard SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets
open SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular SourceEscapeCurrent
open SourceQuantumScalarChart SourceHamiltonianScaleJet SourceScalarForceBudget
open MeasureTheory Filter SourceResolventBandLimit
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction sourceRead state sourcePair defectAction compressionCore
  firstHamiltonianCurrent matterInsertion matterHamiltonianCurrent neutralCurrent compressionMatter singleDefect
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction
  neutralScaleRemainder cutoffEuler constantAction oscillatorMass solverOperator doubleProjectionFlux
  wardOperator sandwichJet inverseCross inputFlux readOrbitJet resolventJet cubic scaleDerivative

def neutralDefect (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (defectAction F) (neutralCurrent sharp m ell)

def neutralRest (sharp : Bool) (m ell : ℕ) : End :=
  -(2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
    (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*SourceMixedNativeReturn.thetaAction m ell)-
    (1/48 : ℂ) • neutralScaleRemainder sharp m ell

/-- One neutral source family replaces the separate B/W defects in the literal actual Ward remainder. -/
def neutralRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  finiteResolvent F z*(-sourceRead F g (neutralDefect sharp m ell F)+sourceRead F g (neutralRest sharp m ell)-
    (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z

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

private theorem matter_defect_join (sharp : Bool) (m ell : ℕ) (F : Index) :
    matterHamiltonianCurrent sharp m ell=
      compressionMatter sharp m ell F+singleDefect sharp m ell F-neutralDefect sharp m ell F := by
  unfold matterHamiltonianCurrent compressionMatter singleDefect neutralDefect neutralCurrent firstHamiltonianCurrent defectAction bracket
  noncomm_ring

private theorem force_join {V : Type*} [AddCommGroup V] (C P U T D S : V) :
    (C+P-U+T)-D-S=C+(P-D)+(-U+T-S) := by abel

private theorem remove_projection (a b c d a' : ℂ) (hbc : c=b) (ha : a'=a) :
    a+(b-c)+d=a'+d := by rw [hbc,sub_self,add_zero,ha]

/-- The actual source force and the complete projection correction join through the same Q=B−W. -/
theorem actual_neutral_balance (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    balancedForce sharp m ell F g=
      sourceRead F g (compressionMatter sharp m ell F)+
      (sourceRead F g (singleDefect sharp m ell F)-doubleProjectionFlux sharp m ell F g)+
      (-sourceRead F g (neutralDefect sharp m ell F)+sourceRead F g (neutralRest sharp m ell)-
        (oscillatorMass : ℂ) • solverOperator sharp m ell F) := by
  have hs : neutralForce sharp m ell=matterHamiltonianCurrent sharp m ell+neutralRest sharp m ell := by
    unfold neutralForce neutralRest
    module
  have hf := hs.trans (congrArg (fun A : End => A+neutralRest sharp m ell) (matter_defect_join sharp m ell F))
  have hr := congrArg (sourceRead F g) hf
  simp only [map_add,map_sub] at hr
  have hb := congrArg (fun A : Op => A-(oscillatorMass : ℂ) • solverOperator sharp m ell F)
    (actual_compressed_neutral_force sharp m ell F g)
  change balancedForce sharp m ell F g=sourceRead F g (neutralForce sharp m ell)-doubleProjectionFlux sharp m ell F g-
    (oscillatorMass : ℂ) • solverOperator sharp m ell F at hb
  have ht := congrArg (fun A : Op => A-doubleProjectionFlux sharp m ell F g-
    (oscillatorMass : ℂ) • solverOperator sharp m ell F) hr
  exact hb.trans (ht.trans (force_join _ _ _ _ _ _))

private theorem pair_sandwich_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r A B C D : E →L[ℂ] E) (f k : E) :
    inner ℂ k ((r*(A+(B-C)+D)*r) f)=
      inner ℂ k ((r*A*r) f)+(inner ℂ k ((r*B*r) f)-inner ℂ k ((r*C*r) f))+
        inner ℂ k ((r*D*r) f) := by
  simp only [mul_add,add_mul,mul_sub,sub_mul,add_apply,sub_apply,inner_add_right,inner_sub_right]

/-- The whole original Ward is one paid matter-current response plus the genuine neutral remainder on its exact cofinal event. -/
theorem actual_ward_neutral (m ell : ℕ) (f k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (sharp : Bool) (z : ℂ),z.im≠0 →
      inner ℂ (embed k) (wardOperator sharp m ell F (coreEquiv f) z (embed f))=
        gaugeProfile F (coreEquiv f) z (compressionMatter sharp m ell F) f k 0 0+
          inner ℂ (embed k) (neutralRemainder sharp m ell F (coreEquiv f) z (embed f)) := by
  filter_upwards [actual_projection_single_defect m ell (coreEquiv f) (coreEquiv k)] with F hF
  intro sharp z hz
  have hp := hF sharp z hz
  change inner ℂ (embed k) ((finiteResolvent F z*doubleProjectionFlux sharp m ell F (coreEquiv f)*finiteResolvent F z) (embed f))=
    inner ℂ (embed k) ((finiteResolvent F z*sourceRead F (coreEquiv f) (singleDefect sharp m ell F)*finiteResolvent F z) (embed f)) at hp
  have hs := congrArg (fun A : Op => inner ℂ (embed k) ((finiteResolvent F z*A*finiteResolvent F z) (embed f)))
    (actual_neutral_balance sharp m ell F (coreEquiv f))
  have ha := pair_sandwich_sum (finiteResolvent F z)
    (sourceRead F (coreEquiv f) (compressionMatter sharp m ell F))
    (sourceRead F (coreEquiv f) (singleDefect sharp m ell F))
    (doubleProjectionFlux sharp m ell F (coreEquiv f))
    (-sourceRead F (coreEquiv f) (neutralDefect sharp m ell F)+sourceRead F (coreEquiv f) (neutralRest sharp m ell)-
      (oscillatorMass : ℂ) • solverOperator sharp m ell F) (embed f) (embed k)
  have ho : gaugeProfile F (coreEquiv f) z (compressionMatter sharp m ell F) f k 0 0=
      inner ℂ (embed k) ((finiteResolvent F z*sourceRead F (coreEquiv f) (compressionMatter sharp m ell F)*finiteResolvent F z) (embed f)) :=
    congrArg (fun A : Op => inner ℂ (embed k) (A (embed f))) (sandwich_origin F (coreEquiv f) z hz _)
  have hw := congrArg (fun A : Op => inner ℂ (embed k) (A (embed f)))
    (actual_balanced_ward sharp m ell F (coreEquiv f) z hz)
  exact hw.symm.trans (hs.trans (ha.trans (remove_projection _ _ _ _ _ hp ho)))

/-- The original full-frequency common tail consumes this single-neutral-family replacement directly. -/
theorem actual_ward_neutral_difference_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (f k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (embed k)
          (wardOperator sharp m ell F (coreEquiv f) (line μ w) (embed f))-
          inner ℂ (embed k) (neutralRemainder sharp m ell F (coreEquiv f) (line μ w) (embed f))‖^2))≤ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_matter_compression_gauge_tail sharp (coreEquiv f) μ hμ 0 f k ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell,actual_ward_neutral m ell f k] with F hF hEq
  have he (w : ℝ) : inner ℂ (embed k)
      (wardOperator sharp m ell F (coreEquiv f) (line μ w) (embed f))-
      inner ℂ (embed k) (neutralRemainder sharp m ell F (coreEquiv f) (line μ w) (embed f))=
      gaugeProfile F (coreEquiv f) (line μ w) (compressionMatter sharp m ell F) f k 0 0 := by
    rw [hEq sharp (line μ w) (by simpa only [line_im] using hμ.ne'),add_sub_cancel_right]
  simpa only [he] using hF

def neutralHamiltonianCurrent (sharp : Bool) (m ell : ℕ) : End := bracket diagonalAction (neutralCurrent sharp m ell)

def coframeRest {V : Type*} [AddCommGroup V] [Module ℂ V] (J : ℕ → V) : V :=
  J 3+(12 : ℂ) • J 2+(44 : ℂ) • J 1

def coframeCubic {V : Type*} [AddCommGroup V] [Module ℂ V] (J : ℕ → V) : V := coframeRest J+(48 : ℂ) • J 0

def neutralContacts (sharp : Bool) (m ell : ℕ) : End :=
  -(2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
    (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*SourceMixedNativeReturn.thetaAction m ell)

def hamiltonianCoframeCorrection (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) (a : ℕ) : Op :=
  inverseCross F seed z (neutralHamiltonianCurrent sharp m ell) a 0+
    finiteResolvent F z*inputFlux F seed (neutralHamiltonianCurrent sharp m ell) a 0*finiteResolvent F z

/-- The original Pc now acts on one neutral defect response, retaining all actual H inverse/input corrections. -/
def coframeReducedRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  -(1/48 : ℂ) • coframeCubic (fun a => sandwichJet F seed z (neutralDefect sharp m ell F) a 0 0 0)+
    (1/48 : ℂ) • coframeRest (hamiltonianCoframeCorrection sharp m ell F seed z)+
    finiteResolvent F z*(sourceRead F seed (neutralContacts sharp m ell)-
      (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z

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

private theorem neutral_response_split (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (n : ℕ) (s : ℝ) :
    sandwichJet F seed z (neutralDefect sharp m ell F) n 0 s 0=
      sandwichJet F seed z (neutralHamiltonianCurrent sharp m ell) n 0 s 0-
        sandwichJet F seed z (compressionNeutral sharp m ell F) n 0 s 0 := by
  have hs : neutralDefect sharp m ell F=neutralHamiltonianCurrent sharp m ell-compressionNeutral sharp m ell F := by
    unfold neutralDefect neutralHamiltonianCurrent compressionNeutral defectAction bracket
    noncomm_ring
  exact (congrArg (fun A : End => sandwichJet F seed z A n 0 s 0) hs).trans (sandwich_sub F seed z _ _ n s)

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

private theorem actual_hamiltonian_rest (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    coframeRest (fun a => sandwichJet F seed z (neutralHamiltonianCurrent sharp m ell) a 0 0 0)=
      finiteResolvent F z*sourceRead F seed (neutralScaleRemainder sharp m ell)*finiteResolvent F z+
        coframeRest (hamiltonianCoframeCorrection sharp m ell F seed z) := by
  let A := neutralHamiltonianCurrent sharp m ell
  have h1 := inverse_cross_small F seed z hz A 1 (by omega)
  have h2 := inverse_cross_small F seed z hz A 2 (by omega)
  have h3 := inverse_cross_small F seed z hz A 3 (by omega)
  have hr := congrArg (fun C : Op => finiteResolvent F z*C*finiteResolvent F z) (read_coframe_rest F seed A)
  simp only [coframeRest,mul_sub,sub_mul,mul_add,add_mul,mul_smul_comm,smul_mul_assoc] at hr
  have hN : cubic A-(48 : ℂ) • A=neutralScaleRemainder sharp m ell := by
    unfold neutralScaleRemainder
    rfl
  have he := congrArg (fun B : End => finiteResolvent F z*sourceRead F seed B*finiteResolvent F z) hN
  exact rest_split h1 h2 h3 (he.symm.trans hr)

private theorem rest_consume {V : Type*} [AddCommGroup V] [Module ℂ V]
    {U0 U1 U2 U3 H1 H2 H3 A1 A2 A3 T C X : V}
    (h1 : U1=H1-A1) (h2 : U2=H2-A2) (h3 : U3=H3-A3)
    (hT : H3+(12 : ℂ) • H2+(44 : ℂ) • H1=T+C) :
    -U0-(1/48 : ℂ) • T+X=
      -(1/48 : ℂ) • (U3+(12 : ℂ) • U2+(44 : ℂ) • U1+(48 : ℂ) • U0)+
      (1/48 : ℂ) • C+X-(1/48 : ℂ) • (A3+(12 : ℂ) • A2+(44 : ℂ) • A1) := by
  linear_combination (norm := module) (1/48 : ℂ) • hT+(1/48 : ℂ) • h3+(1/4 : ℂ) • h2+(11/12 : ℂ) • h1

private theorem surround_rest {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (r u c t mass : R) :
    r*(-u+(c-(1/48 : ℂ) • t)-mass)*r=
      -(r*u*r)-(1/48 : ℂ) • (r*t*r)+r*(c-mass)*r := by
  simp only [mul_neg,neg_mul,mul_add,add_mul,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  module

/-- The neutral compression coframe block is one generated polynomial of its paid response. -/
theorem actual_neutral_coframe_remainder (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    neutralRemainder sharp m ell F seed z=coframeReducedRemainder sharp m ell F seed z-
      (1/48 : ℂ) • coframeRest (fun a => sandwichJet F seed z (compressionNeutral sharp m ell F) a 0 0 0) := by
  have hr := actual_hamiltonian_rest sharp m ell F seed z hz
  have h1 := neutral_response_split sharp m ell F seed z 1 0
  have h2 := neutral_response_split sharp m ell F seed z 2 0
  have h3 := neutral_response_split sharp m ell F seed z 3 0
  have ho := sandwich_origin F seed z hz (neutralDefect sharp m ell F)
  have hs : neutralRest sharp m ell=neutralContacts sharp m ell-(1/48 : ℂ) • neutralScaleRemainder sharp m ell := rfl
  have hs' := congrArg (sourceRead F seed) hs
  simp only [map_sub,map_smul] at hs'
  have hn := congrArg (fun C : Op => finiteResolvent F z*(-sourceRead F seed (neutralDefect sharp m ell F)+C-
    (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z) hs'
  have hn' := surround_rest (finiteResolvent F z) (sourceRead F seed (neutralDefect sharp m ell F))
    (sourceRead F seed (neutralContacts sharp m ell)) (sourceRead F seed (neutralScaleRemainder sharp m ell))
    ((oscillatorMass : ℂ) • solverOperator sharp m ell F)
  have hlin := rest_consume (U0 := sandwichJet F seed z (neutralDefect sharp m ell F) 0 0 0 0)
    (X := finiteResolvent F z*(sourceRead F seed (neutralContacts sharp m ell)-
      (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z) h1 h2 h3 hr
  exact hn.trans (hn'.trans (by simpa only [ho,coframeReducedRemainder,coframeCubic,coframeRest] using hlin))

def paidCoframePolynomial (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  correctedCoframeCompressionJet sharp m ell F seed z 2 0+
    (9 : ℂ) • correctedCoframeCompressionJet sharp m ell F seed z 1 0+
    (17 : ℂ) • correctedCoframeCompressionJet sharp m ell F seed z 0 0-
    (51 : ℂ) • sandwichJet F seed z (compressionNeutral sharp m ell F) 0 0 0 0

private theorem paid_polynomial_return (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) :
    paidCoframePolynomial sharp m ell F seed z=
      coframeRest (fun a => sandwichJet F seed z (compressionNeutral sharp m ell F) a 0 0 0) := by
  simp only [paidCoframePolynomial,correctedCoframeCompressionJet,coframeRest]
  module

def neutralCoframeForce (sharp : Bool) (m ell : ℕ) : End :=
  bracket (scaleDerivative diagonalAction) (neutralCurrent sharp m ell)

/-- The complete neutral defect derivative exposes the actual H-force and both H inverse/input legs, minus the paid CF correction. -/
theorem actual_neutral_corrected_coframe (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    sandwichJet F seed z (neutralDefect sharp m ell F) 1 0 0 0+
      (3 : ℂ) • sandwichJet F seed z (neutralDefect sharp m ell F) 0 0 0 0=
      finiteResolvent F z*sourceRead F seed (neutralCoframeForce sharp m ell)*finiteResolvent F z+
        hamiltonianCoframeCorrection sharp m ell F seed z 1-correctedCoframeCompressionJet sharp m ell F seed z 0 0 := by
  let A := neutralHamiltonianCurrent sharp m ell
  have hsource : scaleDerivative A=neutralCoframeForce sharp m ell-(3 : ℂ) • A := by
    have hb (C D : End) : scaleDerivative (bracket C D)=bracket (scaleDerivative C) D+bracket C (scaleDerivative D) := by
      rw [←K_commutator,←K_commutator,←K_commutator]
      unfold bracket
      noncomm_ring
    dsimp only [A,neutralHamiltonianCurrent,neutralCoframeForce]
    rw [hb,original_neutral_coframe]
    simp only [bracket,smul_mul_assoc,mul_smul_comm]
    module
  have hi := inverse_cross_small F seed z hz A 1 (by omega)
  have ho := sandwich_origin F seed z hz A
  have hg := congrArg (sourceRead F seed) hsource
  simp only [map_sub,map_smul] at hg
  have hf : inputFlux F seed A 1 0=readOrbitJet F seed A 1 0 0 0-sourceRead F seed (scaleDerivative A) := by
    simp only [inputFlux,coreJet,pow_zero,pow_one,Module.End.one_apply]
  have hfr := congrArg (fun B : Op => finiteResolvent F z*B*finiteResolvent F z) hf
  have hgr := congrArg (fun B : Op => finiteResolvent F z*B*finiteResolvent F z) hg
  simp only [mul_sub,sub_mul] at hfr
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc] at hgr
  have hu1 := neutral_response_split sharp m ell F seed z 1 0
  have hu0 := neutral_response_split sharp m ell F seed z 0 0
  unfold hamiltonianCoframeCorrection correctedCoframeCompressionJet
  dsimp only [A] at hi ho hfr hgr
  linear_combination (norm := module) hu1+(3 : ℂ) • hu0-hi+(3 : ℂ) • ho-hfr+hgr

private def gp (A B : ℕ → ℝ → Op) : ℕ → ℕ → ℕ → ℝ → Op
  | 0,r,u,w => A r w*B u w
  | n+1,r,u,w => gp A B n (r+1) u w+gp A B n r (u+1) w

private theorem gp_continuous (A B : ℕ → ℝ → Op) (hA : ∀ r,Continuous (A r))
    (hB : ∀ u,Continuous (B u)) (n r u : ℕ) : Continuous (gp A B n r u) := by
  induction n generalizing r u with
  | zero => exact (hA r).mul (hB u)
  | succ n ih => exact (ih (r+1) u).add (ih r (u+1))

private theorem inverse_jet_continuous (F : Index) (μ : ℝ) (hμ : 0<μ) (j : ℕ) :
    Continuous (fun w : ℝ => resolventJet F (line μ w) j 0 0 0) := by
  have hz (w : ℝ) : line μ w≠0 := by
    intro he
    have hi := congrArg Complex.im he
    exact hμ.ne' (by simpa only [line_im,Complex.zero_im] using hi)
  have hd (r w : ℝ) : (r : ℂ)-line μ w≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,line_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    exact hμ.ne' hi
  have hl : Continuous (line μ) := by unfold line; fun_prop
  have hzi := hl.inv₀ hz
  have hdi (r : ℝ) := (continuous_const.sub hl).inv₀ (hd r)
  unfold resolventJet
  have hs : Continuous (fun w : ℝ => ∑ i : SourceJointResidualEnergy.SpectralIndex F,
      ((((SourceJointResidualEnergy.channelValue F (some i) : ℂ)-line μ w)⁻¹+(line μ w)⁻¹) •
        SourceGaugeCoframeJets.rankJet j 0 (SourceMovingJetFlux.eigenTest F i) (SourceMovingJetFlux.eigenTest F i) 0 0)) := by
    apply continuous_finsetSum
    intro i _
    exact ((hdi _).add hzi).smul continuous_const
  split_ifs
  · exact (hzi.neg.smul continuous_const).add hs
  · exact continuous_const.add hs

private theorem small_sandwich (F : Index) (seed : diagonal.domain) (A : End) (μ w : ℝ) (n : ℕ) (hn : n≤3) :
    sandwichJet F seed (line μ w) A n 0 0 0=
      gp (fun j w => resolventJet F (line μ w) j 0 0 0)
        (fun j w => gp (fun a _ => readOrbitJet F seed A a 0 0 0)
          (fun a w => resolventJet F (line μ w) a 0 0 0) j 0 0 w) n 0 0 w := by
  unfold sandwichJet
  interval_cases n <;> rfl

private theorem small_sandwich_continuous (F : Index) (seed : diagonal.domain) (A : End)
    (μ : ℝ) (hμ : 0<μ) (n : ℕ) (hn : n≤3) :
    Continuous (fun w : ℝ => sandwichJet F seed (line μ w) A n 0 0 0) := by
  have hc := gp_continuous (fun j w => resolventJet F (line μ w) j 0 0 0)
    (fun j w => gp (fun a _ => readOrbitJet F seed A a 0 0 0)
      (fun a w => resolventJet F (line μ w) a 0 0 0) j 0 0 w)
    (inverse_jet_continuous F μ hμ)
    (fun j => gp_continuous _ _ (fun _ => continuous_const) (inverse_jet_continuous F μ hμ) j 0 0) n 0 0
  exact hc.congr (fun w => (small_sandwich F seed A μ w n hn).symm)

private theorem corrected_continuous (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (μ : ℝ) (hμ : 0<μ) (n : ℕ) (hn : n≤2) (f k : QuantumTest) :
    Continuous (fun w : ℝ => inner ℂ (embed k)
      (correctedCoframeCompressionJet sharp m ell F seed (line μ w) n 0 (embed f))) := by
  unfold correctedCoframeCompressionJet
  have h1 := small_sandwich_continuous F seed (compressionNeutral sharp m ell F) μ hμ (n+1) (by omega)
  have h0 := small_sandwich_continuous F seed (compressionNeutral sharp m ell F) μ hμ n (by omega)
  exact continuous_const.inner ((h1.add (h0.const_smul (3 : ℂ))).clm_apply continuous_const)

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

private theorem paid_coefficients (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ)
    (f k : QuantumTest) :
    -(1/48 : ℂ)*inner ℂ (embed k) (paidCoframePolynomial sharp m ell F seed z (embed f))=
      inner ℂ (embed k) (correctedCoframeCompressionJet sharp m ell F seed z 2 0 (embed (-(1/48 : ℂ) • f)))+
      inner ℂ (embed k) (correctedCoframeCompressionJet sharp m ell F seed z 1 0 (embed (-(3/16 : ℂ) • f)))+
      inner ℂ (embed k) (correctedCoframeCompressionJet sharp m ell F seed z 0 0 (embed (-(17/48 : ℂ) • f)))+
      coframeProfile F seed z (compressionNeutral sharp m ell F) ((17/16 : ℂ) • f) k 0 0 := by
  simp only [paidCoframePolynomial,coframeProfile,map_smul,add_apply,sub_apply,smul_apply,
    inner_add_right,inner_sub_right,inner_smul_right]
  ring

/-- The precise coframe coefficients consume the complete corrected-CF budgets and the original neutral zeroth current. -/
theorem actual_paid_coframe_polynomial_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (f k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖-(1/48 : ℂ)*inner ℂ (embed k)
          (paidCoframePolynomial sharp m ell F seed (line μ w) (embed f))‖^2))≤ENNReal.ofReal ε := by
  have h2 := actual_corrected_coframe_compression_tail sharp seed μ hμ 2 (-(1/48 : ℂ) • f) k
  have h1 := actual_corrected_coframe_compression_tail sharp seed μ hμ 1 (-(3/16 : ℂ) • f) k
  have h0 := actual_corrected_coframe_compression_tail sharp seed μ hμ 0 (-(17/48 : ℂ) • f) k
  have hN := actual_neutral_compression_coframe_tail sharp seed μ hμ 0 ((17/16 : ℂ) • f) k
  have hc2 := fun m ell F => corrected_continuous sharp m ell F seed μ hμ 2 (by omega) (-(1/48 : ℂ) • f) k
  have hc1 := fun m ell F => corrected_continuous sharp m ell F seed μ hμ 1 (by omega) (-(3/16 : ℂ) • f) k
  have hc0 := fun m ell F => corrected_continuous sharp m ell F seed μ hμ 0 (by omega) (-(17/48 : ℂ) • f) k
  have ht := tail_add _ _ (fun m ell F => ((hc2 m ell F).add (hc1 m ell F)).add (hc0 m ell F))
    (tail_add _ _ (fun m ell F => (hc2 m ell F).add (hc1 m ell F))
      (tail_add _ _ hc2 h2 h1) h0) hN
  exact tail_congr _ _ (fun m ell => Filter.Eventually.of_forall (fun F w =>
    paid_coefficients sharp m ell F seed (line μ w) f k)) ht

private theorem matter_continuous (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (μ : ℝ) (hμ : 0<μ) (f k : QuantumTest) :
    Continuous (fun w : ℝ => gaugeProfile F seed (line μ w) (compressionMatter sharp m ell F) f k 0 0) :=
  continuous_const.inner ((small_sandwich_continuous F seed (compressionMatter sharp m ell F) μ hμ 0 (by omega)).clm_apply continuous_const)

/-- Whole Ward consumes the new CF coframe polynomial, leaving a single Pc-neutral defect family with every original H correction. -/
theorem actual_ward_coframe_reduced_difference_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (f k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (embed k)
          (wardOperator sharp m ell F (coreEquiv f) (line μ w) (embed f))-
          inner ℂ (embed k) (coframeReducedRemainder sharp m ell F (coreEquiv f) (line μ w) (embed f))‖^2))≤ENNReal.ofReal ε := by
  have hm := actual_matter_compression_gauge_tail sharp (coreEquiv f) μ hμ 0 f k
  have hc := actual_paid_coframe_polynomial_tail sharp (coreEquiv f) μ hμ f k
  have ht := tail_add _ _ (fun m ell F => matter_continuous sharp m ell F (coreEquiv f) μ hμ f k) hm hc
  apply tail_congr _ _ ?_ ht
  intro m ell
  filter_upwards [actual_ward_neutral m ell f k] with F hF
  intro w
  have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
  have hr := congrArg (fun A : Op => inner ℂ (embed k) (A (embed f)))
    (actual_neutral_coframe_remainder sharp m ell F (coreEquiv f) (line μ w) hz)
  have hp := congrArg (fun A : Op => inner ℂ (embed k) (A (embed f)))
    (paid_polynomial_return sharp m ell F (coreEquiv f) (line μ w))
  simp only [sub_apply,smul_apply,inner_sub_right,inner_smul_right] at hr
  have hw := hF sharp (line μ w) hz
  linear_combination hw+hr+(1/48 : ℂ)*hp

end LowEnergy.SourceInverseCoframeNeutralSplice
