import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeCoframeSpectralReturn
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeCoframeJointTailReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseNeutralRemainderSpectral
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceMixedNativeReturn SourceGaugeCoframeWard SourceGaugeCoframeJets SourceScalarForceBudget
open SourceInverseCoframeNeutralSplice SourceInverseCoframeCompressionBudget SourceInverseCoframeSpectralReturn
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceJointResidualEnergy
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] sourceRead neutralDefect neutralHamiltonianCurrent neutralContacts solverOperator
  coframeCoefficient coefficient decode sandwichJet resolventJet readOrbitJet inverseCross inputFlux

private theorem inverse_small (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) (a : Fin 4) :
    inverseCross F seed z A a 0=sandwichJet F seed z A a 0 0 0-
      finiteResolvent F z*readOrbitJet F seed A a 0 0 0*finiteResolvent F z := by
  fin_cases a <;> simp only [inverseCross,resolved_inverse_return F z hz,sandwichJet] <;> rfl

/-- The actual inverse and input corrections cancel their shared read-orbit term as one signed combination. -/
theorem actual_correction_normal (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) (a : Fin 4) :
    hamiltonianCoframeCorrection sharp m ell F seed z a=
      sandwichJet F seed z (neutralHamiltonianCurrent sharp m ell) a 0 0 0-
        finiteResolvent F z*sourceRead F seed (coreJet a 0 (neutralHamiltonianCurrent sharp m ell))*finiteResolvent F z := by
  have hi := inverse_small F seed z hz (neutralHamiltonianCurrent sharp m ell) a
  have hf : inputFlux F seed (neutralHamiltonianCurrent sharp m ell) a 0=
      readOrbitJet F seed (neutralHamiltonianCurrent sharp m ell) a 0 0 0-
        sourceRead F seed (coreJet a 0 (neutralHamiltonianCurrent sharp m ell)) := by unfold inputFlux;rfl
  unfold hamiltonianCoframeCorrection
  rw [hi,hf]
  simp only [mul_sub,sub_mul]
  abel

def correctionCoefficient (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (f k : QuantumTest) (a : ℕ) : Coeff F :=
  coframeCoefficient F seed (neutralHamiltonianCurrent sharp m ell) f k a-
    coefficient F (sourceRead F seed (coreJet a 0 (neutralHamiltonianCurrent sharp m ell))) (embed f) (embed k)

private theorem correction_decode (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (f k : QuantumTest) (μ : ℝ) (hμ : 0<μ) (w : ℝ) (a : Fin 4) :
    inner ℂ (embed k) (hamiltonianCoframeCorrection sharp m ell F seed (line μ w) a (embed f))=
      decode F μ w (correctionCoefficient sharp m ell F seed f k a) := by
  rw [actual_correction_normal sharp m ell F seed (line μ w) (by simpa only [line_im] using hμ.ne') a]
  simp only [sub_apply,inner_sub_right,correctionCoefficient,map_sub]
  have hc := actual_coframe_decode F seed (neutralHamiltonianCurrent sharp m ell) μ hμ w a f k
  change inner ℂ (embed k) (sandwichJet F seed (line μ w) (neutralHamiltonianCurrent sharp m ell) a 0 0 0 (embed f))=_ at hc
  rw [hc,actual_decode F μ hμ w]

def contactOperator (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) : Op :=
  sourceRead F seed (neutralContacts sharp m ell)-(oscillatorMass : ℂ) • solverOperator sharp m ell F

/-- One frequency-independent source array contains the complete signed R_Q, including H/d_F and both corrections. -/
def remainderCoefficient (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (f k : QuantumTest) : Coeff F :=
  -(1/48 : ℂ) • coframeCubic (fun a => coframeCoefficient F seed (neutralDefect sharp m ell F) f k a)+
    (1/48 : ℂ) • coframeRest (correctionCoefficient sharp m ell F seed f k)+
      coefficient F (contactOperator sharp m ell F seed) (embed f) (embed k)

/-- The full remainder has only the original two retarded poles after source-leg differentiation. -/
theorem actual_remainder_decode (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (f k : QuantumTest) (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    inner ℂ (embed k) (coframeReducedRemainder sharp m ell F seed (line μ w) (embed f))=
      decode F μ w (remainderCoefficient sharp m ell F seed f k) := by
  have hd (a : ℕ) := actual_coframe_decode F seed (neutralDefect sharp m ell F) μ hμ w a f k
  have hc (a : Fin 4) := correction_decode sharp m ell F seed f k μ hμ w a
  have hs := actual_decode F μ hμ w (contactOperator sharp m ell F seed) (embed f) (embed k)
  change inner ℂ (embed k) ((finiteResolvent F (line μ w)*
    (sourceRead F seed (neutralContacts sharp m ell)-(oscillatorMass : ℂ) • solverOperator sharp m ell F)*
    finiteResolvent F (line μ w)) (embed f))=_ at hs
  simp only [coframeReducedRemainder,remainderCoefficient,coframeCubic,coframeRest,add_apply,smul_apply,
    inner_add_right,inner_smul_right,map_add,map_smul,smul_eq_mul]
  rw [hs]
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  change inner ℂ (embed k) (sandwichJet F seed (line μ w) (neutralDefect sharp m ell F) 0 0 0 0 (embed f))=_ at hd0
  change inner ℂ (embed k) (sandwichJet F seed (line μ w) (neutralDefect sharp m ell F) 1 0 0 0 (embed f))=_ at hd1
  change inner ℂ (embed k) (sandwichJet F seed (line μ w) (neutralDefect sharp m ell F) 2 0 0 0 (embed f))=_ at hd2
  change inner ℂ (embed k) (sandwichJet F seed (line μ w) (neutralDefect sharp m ell F) 3 0 0 0 (embed f))=_ at hd3
  have hc1 : inner ℂ (embed k) (hamiltonianCoframeCorrection sharp m ell F seed (line μ w) 1 (embed f))=
      decode F μ w (correctionCoefficient sharp m ell F seed f k 1) := hc ⟨1,by omega⟩
  have hc2 : inner ℂ (embed k) (hamiltonianCoframeCorrection sharp m ell F seed (line μ w) 2 (embed f))=
      decode F μ w (correctionCoefficient sharp m ell F seed f k 2) := hc ⟨2,by omega⟩
  have hc3 : inner ℂ (embed k) (hamiltonianCoframeCorrection sharp m ell F seed (line μ w) 3 (embed f))=
      decode F μ w (correctionCoefficient sharp m ell F seed f k 3) := hc ⟨3,by omega⟩
  rw [hd0,hd1,hd2,hd3,hc1,hc2,hc3]

end LowEnergy.SourceInverseNeutralRemainderSpectral
