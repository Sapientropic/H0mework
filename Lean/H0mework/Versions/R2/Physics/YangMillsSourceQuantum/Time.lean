import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingTime
import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingOrigin
import H0mework.Quantum.Generator.SelfAdjoint
import H0mework.Quantum.Time.Center

/-! Raw time input from the original full mother action and its physical pairing.
The unitary is the existing clock action; its Hamiltonian is its actual derivative. -/

set_option autoImplicit false
open scoped InnerProductSpace

namespace SaturationMonoid.PhysicsCore.YangMills.NativeSource
open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF
open Stage10.GaugeSpectrum FullPairing
noncomputable section

def clock (t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  operator (diracMatrixMatterAction (clockMatrix (Dynamics.timeDisplacement t)))

theorem clock_apply (t : ℝ) (v : Hilbert) (i : FullPairing.Index) :
    clock t v i = phase (spinRate i.1) (Dynamics.timeDisplacement t) * v i := by
  have read := operator_coordinates
    (diracMatrixMatterAction (clockMatrix (Dynamics.timeDisplacement t)))
    (naturalCoordinates.symm v)
  rw [LinearEquiv.apply_symm_apply] at read
  rw [clock, read]
  conv_rhs => rw [← naturalCoordinates.apply_symm_apply v]
  rw [naturalCoordinates_apply, naturalCoordinates_apply]
  simp [diracMatrixMatterAction, clockMatrix, Matrix.diagonal_apply]

theorem clock_zero (v : Hilbert) : clock 0 v = v := by
  apply PiLp.ext
  intro i
  rw [clock_apply]
  simp [Dynamics.timeDisplacement, phase]

theorem clock_add (s t : ℝ) (v : Hilbert) : clock (s + t) v = clock s (clock t v) := by
  apply PiLp.ext
  intro i
  rw [clock_apply, clock_apply, clock_apply]
  rw [Dynamics.timeDisplacement, add_smul, Dynamics.phase_add]
  exact mul_assoc _ _ _

def time : Multiplicative ℝ →* (Hilbert ≃ₗᵢ[ℂ] Hilbert) where
  toFun t :=
    { toFun := clock t.toAdd
      invFun := clock (-t.toAdd)
      left_inv v := by rw [← clock_add, neg_add_cancel, clock_zero]
      right_inv v := by rw [← clock_add, add_neg_cancel, clock_zero]
      map_add' := (clock t.toAdd).map_add
      map_smul' := (clock t.toAdd).map_smul
      norm_map' v := by
        have same := congrArg Complex.re
          (clock_inner (Dynamics.timeDisplacement t.toAdd) v v)
        change RCLike.re (inner ℂ (clock t.toAdd v) (clock t.toAdd v)) = RCLike.re (inner ℂ v v) at same
        rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at same
        change ‖clock t.toAdd v‖ = ‖v‖
        nlinarith [norm_nonneg (clock t.toAdd v), norm_nonneg v] }
  map_one' := by apply LinearIsometryEquiv.ext; intro v; exact clock_zero v
  map_mul' s t := by apply LinearIsometryEquiv.ext; intro v; exact clock_add s.toAdd t.toAdd v

theorem time_prepared (p : BasePoint) (t : ℝ) :
    time (Multiplicative.ofAdd t) (prepared p) = prepared (p + Dynamics.timeDisplacement t) :=
  prepared_time p (Dynamics.timeDisplacement t)

def velocity : Hilbert →L[ℂ] Hilbert := operator Compatibility.temporalAction

theorem velocity_apply (v : Hilbert) (i : FullPairing.Index) :
    velocity v i = ((spinRate i.1 : ℝ) : ℂ) * Complex.I * v i := by
  have read := operator_coordinates Compatibility.temporalAction (naturalCoordinates.symm v)
  rw [LinearEquiv.apply_symm_apply] at read
  rw [velocity, read]
  conv_rhs => rw [← naturalCoordinates.apply_symm_apply v]
  rw [naturalCoordinates_apply, naturalCoordinates_apply]
  rcases i with ⟨spin, sector⟩
  fin_cases spin <;>
    simp [Compatibility.temporalAction, spinRate, Dynamics.rate, diracMatrixMatterAction,
      Fin.sum_univ_four] <;> ring_nf <;> simp

theorem orbit_derivative (v : Hilbert) (t : ℝ) :
    HasDerivAt (Quantum.Generator.orbit time v) (velocity (time (Multiplicative.ofAdd t) v)) t := by
  let e : (FullPairing.Index → ℂ) ≃L[ℂ] Hilbert :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : FullPairing.Index => ℂ)).symm
  have derivative : HasDerivAt
      (fun s : ℝ => fun i : FullPairing.Index => phase (spinRate i.1) (Dynamics.timeDisplacement s) * v i)
      (fun i => ((spinRate i.1 : ℝ) : ℂ) * Complex.I *
        (phase (spinRate i.1) (Dynamics.timeDisplacement t) * v i)) t := by
    rw [hasDerivAt_pi]
    intro i
    have d := (Dynamics.phaseCoefficient_hasDerivAt t (i.1, 0)).mul_const (v i)
    change HasDerivAt (fun s => phase (spinRate i.1) (Dynamics.timeDisplacement s) * v i)
      ((phase (spinRate i.1) (Dynamics.timeDisplacement t) *
        (((spinRate i.1 : ℝ) : ℂ) * Complex.I)) * v i) t at d
    exact d.congr_deriv (by ring)
  have carried := (e.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t derivative
  convert! carried using 1
  · funext s
    apply PiLp.ext
    intro i
    exact clock_apply s v i
  · apply PiLp.ext
    intro i
    rw [velocity_apply]
    exact congrArg (fun z => ((spinRate i.1 : ℝ) : ℂ) * Complex.I * z) (clock_apply t v i)

theorem time_continuous (v : Hilbert) : Continuous (Quantum.Generator.orbit time v) :=
  (show Differentiable ℝ (Quantum.Generator.orbit time v) from
    fun t => (orbit_derivative v t).differentiableAt).continuous

def point (v : Hilbert) : Quantum.Generator.domain time :=
  ⟨v, (orbit_derivative v 0).differentiableAt⟩

theorem hamiltonian_point (v : Hilbert) :
    Quantum.Generator.hamiltonianOperator time (point v) = Complex.I • velocity v := by
  change Complex.I • deriv (Quantum.Generator.orbit time v) 0 = _
  rw [(orbit_derivative v 0).deriv]
  change Complex.I • velocity (clock 0 v) = _
  rw [clock_zero]

def quantumFeature : (Source.Index → ℂ) →L[ℂ] Hilbert :=
  (naturalCoordinates.toLinearMap.comp Compatibility.embed).toContinuousLinearMap

theorem original_physical_input (p : BasePoint) (t : ℝ) :
    HasDerivAt
      (fun s => quantumFeature (Stage10.Runtime.tick.answer (p + Dynamics.timeDisplacement s)))
      (quantumFeature (fun i => Stage10.Runtime.tick.answer (p + Dynamics.timeDisplacement t) i *
        Dynamics.generator i)) t := by
  have generated := Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.quantumClosure.physicalTime p t
  rw [Runtime.firstQuantumTick_answer, Runtime.fieldAt_eq_vector] at generated
  rw [Stage10.Runtime.tick_vector]
  exact (quantumFeature.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t generated

theorem source_velocity (p : BasePoint) :
    velocity (prepared p) =
      quantumFeature (fun i => Stage10.Runtime.tick.answer p i * Dynamics.generator i) := by
  have original := original_physical_input p 0
  rw [Stage10.Runtime.tick_vector] at original
  have same : (fun s => quantumFeature (Source.vector (p + Dynamics.timeDisplacement s))) =
      Quantum.Generator.orbit time (prepared p) := by
    funext s
    exact (time_prepared p s).symm
  rw [same] at original
  have generated := (orbit_derivative (prepared p) 0).unique original
  change velocity (clock 0 (prepared p)) =
    quantumFeature (fun i => Source.vector (p + Dynamics.timeDisplacement 0) i * Dynamics.generator i) at generated
  rw [clock_zero] at generated
  simpa only [Dynamics.timeDisplacement,
    zero_smul, add_zero, Stage10.Runtime.tick_vector] using generated

end
end SaturationMonoid.PhysicsCore.YangMills.NativeSource
