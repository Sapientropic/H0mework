import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCoframeCovariantSquare
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCoframeVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceCoframeClockGram
open GaussNativeEnergy GaussHistoryHilbert SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussFockPair SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped InnerProductSpace
local instance : InnerProductSpace ℝ FockFiber := InnerProductSpace.rclikeToReal ℂ FockFiber

def clockPolynomial (q : Coframe) (i j : Fin 6) : ℝ :=
  q i*q j-GaussCoframeKinetic.polynomial q i j

def clockQuadratic (q : Coframe) (p : Fin 6 → FockFiber) : ℝ :=
  ∑ i : Fin 6,∑ j : Fin 6,clockPolynomial q i j*(inner ℝ (p i) (p j))

def clockGram (q : Coframe) (p : Fin 6 → FockFiber) : ℝ :=
  2*‖q 0 • p 0‖^2+2*‖q 1 • p 1+q 2 • p 2‖^2+
  2*‖q 3 • p 3+q 4 • p 4+q 5 • p 5‖^2+
  4*‖q 0 • p 1‖^2+4*‖q 0 • p 3‖^2+4*‖q 1 • p 3+q 2 • p 4‖^2

/-- The original clock trace reversal is six positive Gram rows on the complete complex Fock fiber. -/
theorem original_clock_fiber_square (q : Coframe) (p : Fin 6 → FockFiber) :
    clockQuadratic q p=clockGram q p := by
  simp only [clockGram,norm_add_sq_real,inner_add_left,
    real_inner_smul_left,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simp [clockQuadratic,clockPolynomial,GaussCoframeKinetic.polynomial,Fin.sum_univ_succ]
  rw [real_inner_comm (p 2) (p 1),real_inner_comm (p 4) (p 3),
    real_inner_comm (p 5) (p 3),real_inner_comm (p 5) (p 4)]
  ring

private theorem diagonal_ne (z : physicalChart) :
    z.val.1 0≠0 ∧ z.val.1 2≠0 ∧ z.val.1 5≠0 := by
  have h := (volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5≠0 at h
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2,(mul_ne_zero_iff.mp h).2⟩

/-- The source chart itself pays strict positivity; the six rows use all coframe directions. -/
theorem original_clock_fiber_positive (z : physicalChart) (p : Fin 6 → FockFiber) :
    0≤clockQuadratic z.val.1 p ∧ (clockQuadratic z.val.1 p=0 ↔ p=0) := by
  rw [original_clock_fiber_square]
  refine ⟨by unfold clockGram;positivity,?_⟩
  constructor
  · intro hz
    obtain ⟨h0,h2,h5⟩ := diagonal_ne z
    unfold clockGram at hz
    have ha : z.val.1 0 • p 0=0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖z.val.1 1 • p 1+z.val.1 2 • p 2‖,
        sq_nonneg ‖z.val.1 3 • p 3+z.val.1 4 • p 4+z.val.1 5 • p 5‖,
        sq_nonneg ‖z.val.1 0 • p 1‖,sq_nonneg ‖z.val.1 0 • p 3‖,
        sq_nonneg ‖z.val.1 1 • p 3+z.val.1 2 • p 4‖,norm_nonneg (z.val.1 0 • p 0)]
    have hb : z.val.1 1 • p 1+z.val.1 2 • p 2=0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖z.val.1 0 • p 0‖,
        sq_nonneg ‖z.val.1 3 • p 3+z.val.1 4 • p 4+z.val.1 5 • p 5‖,
        sq_nonneg ‖z.val.1 0 • p 1‖,sq_nonneg ‖z.val.1 0 • p 3‖,
        sq_nonneg ‖z.val.1 1 • p 3+z.val.1 2 • p 4‖,
        norm_nonneg (z.val.1 1 • p 1+z.val.1 2 • p 2)]
    have hc : z.val.1 3 • p 3+z.val.1 4 • p 4+z.val.1 5 • p 5=0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖z.val.1 0 • p 0‖,sq_nonneg ‖z.val.1 1 • p 1+z.val.1 2 • p 2‖,
        sq_nonneg ‖z.val.1 0 • p 1‖,sq_nonneg ‖z.val.1 0 • p 3‖,
        sq_nonneg ‖z.val.1 1 • p 3+z.val.1 2 • p 4‖,
        norm_nonneg (z.val.1 3 • p 3+z.val.1 4 • p 4+z.val.1 5 • p 5)]
    have hd : z.val.1 0 • p 1=0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖z.val.1 0 • p 0‖,sq_nonneg ‖z.val.1 1 • p 1+z.val.1 2 • p 2‖,
        sq_nonneg ‖z.val.1 3 • p 3+z.val.1 4 • p 4+z.val.1 5 • p 5‖,
        sq_nonneg ‖z.val.1 0 • p 3‖,sq_nonneg ‖z.val.1 1 • p 3+z.val.1 2 • p 4‖,
        norm_nonneg (z.val.1 0 • p 1)]
    have he : z.val.1 0 • p 3=0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖z.val.1 0 • p 0‖,sq_nonneg ‖z.val.1 1 • p 1+z.val.1 2 • p 2‖,
        sq_nonneg ‖z.val.1 3 • p 3+z.val.1 4 • p 4+z.val.1 5 • p 5‖,
        sq_nonneg ‖z.val.1 0 • p 1‖,sq_nonneg ‖z.val.1 1 • p 3+z.val.1 2 • p 4‖,
        norm_nonneg (z.val.1 0 • p 3)]
    have hf : z.val.1 1 • p 3+z.val.1 2 • p 4=0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖z.val.1 0 • p 0‖,sq_nonneg ‖z.val.1 1 • p 1+z.val.1 2 • p 2‖,
        sq_nonneg ‖z.val.1 3 • p 3+z.val.1 4 • p 4+z.val.1 5 • p 5‖,
        sq_nonneg ‖z.val.1 0 • p 1‖,sq_nonneg ‖z.val.1 0 • p 3‖,
        norm_nonneg (z.val.1 1 • p 3+z.val.1 2 • p 4)]
    have hp0 : p 0=0 := (smul_eq_zero.mp ha).resolve_left h0
    have hp1 : p 1=0 := (smul_eq_zero.mp hd).resolve_left h0
    have hp3 : p 3=0 := (smul_eq_zero.mp he).resolve_left h0
    have hp2 : p 2=0 := by
      rw [hp1,smul_zero,zero_add] at hb
      exact (smul_eq_zero.mp hb).resolve_left h2
    have hp4 : p 4=0 := by
      rw [hp3,smul_zero,zero_add] at hf
      exact (smul_eq_zero.mp hf).resolve_left h2
    have hp5 : p 5=0 := by
      rw [hp3,hp4,smul_zero,smul_zero,zero_add,zero_add] at hc
      exact (smul_eq_zero.mp hc).resolve_left h5
    funext i
    fin_cases i <;> assumption
  · intro h
    rw [h]
    simp [clockGram]

/-- The original complex source rows, including the generated spin connection, consume the same Gram. -/
theorem original_covariant_clock_gram (f : QuantumTest) (z : physicalChart) :
    (∑ i : Fin 6,∑ j : Fin 6,
      clockPolynomial z.val.1 i j*
        (inner ℂ ((SourceCoframeCovariantAction.covariantMomentum i f) z.val)
          ((SourceCoframeCovariantAction.covariantMomentum j f) z.val)).re)=
      clockGram z.val.1 (fun i => (SourceCoframeCovariantAction.covariantMomentum i f) z.val) := by
  have h := original_clock_fiber_square z.val.1
    (fun i => (SourceCoframeCovariantAction.covariantMomentum i f) z.val)
  simpa only [clockQuadratic,real_inner_eq_re_inner ℂ,RCLike.re_to_complex] using h

end LowEnergy.SourceCoframeClockGram
