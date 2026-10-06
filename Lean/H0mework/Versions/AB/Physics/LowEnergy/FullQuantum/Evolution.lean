import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Source
import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingResponse
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! The full source symbol evolves the primal and its independent canonical dual.
Every source insertion is composed on the complete carrier before its old reader. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineHolonomicField
open YangMills.FullPairing StageNineCurrentCoframeMatterTemporalPrincipal
open scoped InnerProductSpace
noncomputable section
local instance : NormedAlgebra ℚ (Hilbert →L[ℂ] Hilbert) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (Hilbert →L[ℂ] Hilbert) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

def evolution (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  NormedSpace.exp (t • operator (drift C p k))

theorem evolution_zero (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : evolution C p k 0 = 1 := by
  have zero : (0 : ℝ) • operator (drift C p k) = 0 := by ext v i; simp
  rw [evolution, zero, NormedSpace.exp_zero]

theorem evolution_add (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t s : ℝ) :
    evolution C p k (t+s) = evolution C p k t * evolution C p k s := by
  unfold evolution
  have scalarAdd : (t+s) • operator (drift C p k) =
      t • operator (drift C p k) + s • operator (drift C p k) := by
    ext v i
    simp
    ring
  rw [scalarAdd]
  apply NormedSpace.exp_add_of_commute
  show (t • operator (drift C p k)) * (s • operator (drift C p k)) =
    (s • operator (drift C p k)) * (t • operator (drift C p k))
  ext v i
  simp
  ring

theorem evolution_inverse (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    evolution C p k (-t) * evolution C p k t = 1 := by
  rw [← evolution_add, neg_add_cancel, evolution_zero]

theorem evolution_inverse_reverse (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    evolution C p k t * evolution C p k (-t) = 1 := by
  rw [← evolution_add, add_neg_cancel, evolution_zero]

theorem evolution_derivative (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (evolution C p k)
      (evolution C p k t * operator (drift C p k)) t :=
  hasDerivAt_exp_smul_const (operator (drift C p k)) t

theorem evolution_commutes (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    evolution C p k t * operator (drift C p k) =
      operator (drift C p k) * evolution C p k t := by
  have commute : Commute (t • operator (drift C p k)) (operator (drift C p k)) := by
    show (t • operator (drift C p k)) * operator (drift C p k) =
      operator (drift C p k) * (t • operator (drift C p k))
    ext v i
    simp
  exact commute.exp_left.eq

def primal (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) : Mother := fromOperator (evolution C p k t)

theorem primal_coordinates (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (v : DiracExteriorMatterCarrier) :
    naturalCoordinates (primal C p k t v) = evolution C p k t (naturalCoordinates v) :=
  coordinates_fromOperator _ _

theorem primal_zero (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (v : DiracExteriorMatterCarrier) : primal C p k 0 v = v := by
  apply naturalCoordinates.injective
  rw [primal_coordinates, evolution_zero]
  rfl

theorem primal_inverse (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (v : DiracExteriorMatterCarrier) :
    primal C p k (-t) (primal C p k t v) = v := by
  apply naturalCoordinates.injective
  rw [primal_coordinates, primal_coordinates]
  change (evolution C p k (-t) * evolution C p k t) (naturalCoordinates v) = _
  rw [evolution_inverse]
  rfl

theorem primal_derivative (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (v : DiracExteriorMatterCarrier) :
    HasDerivAt (fun time => naturalCoordinates (primal C p k time v))
      (naturalCoordinates (drift C p k (primal C p k t v))) t := by
  let evaluate := (ContinuousLinearMap.apply ℂ Hilbert (naturalCoordinates v)).restrictScalars ℝ
  have generated := evaluate.hasFDerivAt.comp_hasDerivAt t (evolution_derivative C p k t)
  rw [evolution_commutes] at generated
  convert! generated using 1
  · funext time
    rw [primal_coordinates]
    rfl

theorem primal_drift_commute (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (v : DiracExteriorMatterCarrier) :
    primal C p k t (drift C p k v) = drift C p k (primal C p k t v) := by
  apply naturalCoordinates.injective
  rw [primal_coordinates, ← operator_coordinates, ← operator_coordinates, primal_coordinates]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (naturalCoordinates v))
    (evolution_commutes C p k t)

def canonicalDual (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (chi : Module.Dual ℂ DiracExteriorMatterCarrier) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  chi.comp ((currentCoframeMatterTemporalPrincipal (C.coframe p)).comp
    ((primal C p k (-t)).comp
      (currentCoframeMatterTemporalPrincipalInverse (C.coframe p))))

theorem original_concomitant (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (v : DiracExteriorMatterCarrier)
    (chi : Module.Dual ℂ DiracExteriorMatterCarrier)
    (noncharacteristic : coframeTemporalPrincipalScalar (C.coframe p) ≠ 0) :
    canonicalDual C p k t chi
      (currentCoframeMatterTemporalPrincipal (C.coframe p) (primal C p k t v)) =
      chi (currentCoframeMatterTemporalPrincipal (C.coframe p) v) := by
  simp only [canonicalDual, LinearMap.comp_apply]
  rw [currentCoframeMatterTemporalPrincipalInverse_left _ noncharacteristic, primal_inverse]

theorem canonicalDual_derivative (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (chi : Module.Dual ℂ DiracExteriorMatterCarrier)
    (v : DiracExteriorMatterCarrier)
    (noncharacteristic : coframeTemporalPrincipalScalar (C.coframe p) ≠ 0) :
    HasDerivAt (fun time => canonicalDual C p k time chi v)
      (-canonicalDual C p k t chi
        (currentCoframeMatterTemporalPrincipal (C.coframe p)
          (drift C p k (currentCoframeMatterTemporalPrincipalInverse (C.coframe p) v)))) t := by
  let seed := currentCoframeMatterTemporalPrincipalInverse (C.coframe p) v
  let read : Hilbert →L[ℂ] ℂ :=
    (chi.comp ((currentCoframeMatterTemporalPrincipal (C.coframe p)).comp
      naturalCoordinates.symm.toLinearMap)).toContinuousLinearMap
  have read_value (w : DiracExteriorMatterCarrier) :
      read (naturalCoordinates w) = chi (currentCoframeMatterTemporalPrincipal (C.coframe p) w) := by
    simp only [read, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have read_negative (w : Hilbert) : read ((-1 : ℝ) • w) = -read w := by
    rw [neg_one_smul, map_neg]
  have inverseCurve := (primal_derivative C p k (-t) seed).scomp t (hasDerivAt_neg t)
  have generated := (read.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t inverseCurve
  change HasDerivAt (fun time => read (naturalCoordinates (primal C p k (-time) seed)))
    (read ((-1 : ℝ) • naturalCoordinates (drift C p k (primal C p k (-t) seed)))) t at generated
  simp only [read_negative, read_value] at generated
  convert! generated using 1
  simp only [canonicalDual, LinearMap.comp_apply,
    currentCoframeMatterTemporalPrincipalInverse_left _ noncharacteristic]
  rw [primal_drift_commute]

theorem canonicalDual_original_equation (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (chi : Module.Dual ℂ DiracExteriorMatterCarrier)
    (v : DiracExteriorMatterCarrier)
    (noncharacteristic : coframeTemporalPrincipalScalar (C.coframe p) ≠ 0) :
    HasDerivAt (fun time => canonicalDual C p k time chi v)
      (canonicalDual C p k t chi (dualDrift C p k v)) t := by
  rw [dualDrift_original C p k noncharacteristic, map_neg]
  exact canonicalDual_derivative C p k t chi v noncharacteristic

def insertion (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : Mother) : Mother :=
  (currentCoframeMatterTemporalPrincipal (C.coframe p)).comp
    ((primal C p k (-t)).comp
      ((currentCoframeMatterTemporalPrincipalInverse (C.coframe p)).comp
        (A.comp (primal C p k t))))

theorem original_inserted_pair (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : Mother)
    (chi : Module.Dual ℂ DiracExteriorMatterCarrier) (v : DiracExteriorMatterCarrier) :
    canonicalDual C p k t chi (A (primal C p k t v)) =
      chi (insertion C p k t A v) := rfl

theorem original_Stage10_insertion (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : Mother) :
    canonicalDual C p k t (Stage9C.Material.SpinPair.actual.conjugateMatter p)
      (A (primal C p k t (Stage9C.Material.SpinPair.actual.matter p))) =
      4 * (Stage9C.Material.SpinPair.spinScale : ℂ) *
        Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer p)
          (Stage9DEF.Compatibility.responseMatrix (insertion C p k t A)) := by
  rw [original_inserted_pair]
  have generated := Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.quantumClosure.sourceResponse
    p (insertion C p k t A)
  rw [Stage9DEF.Runtime.firstQuantumTick_answer, Stage9DEF.Runtime.fieldAt_eq_vector] at generated
  rw [Stage10.Runtime.tick_vector]
  exact generated

section Positive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem symmetric_no_jordan (T : E →ₗ[ℂ] E) (symmetric : T.IsSymmetric)
    (v : E) (square_zero : T (T v) = 0) : T v = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [symmetric, square_zero, inner_zero_right]

theorem faithful_positive_representation_obstruction
    (embed : DiracExteriorMatterCarrier →ₗ[ℂ] E) (faithful : Function.Injective embed)
    (T : E →ₗ[ℂ] E) (symmetric : T.IsSymmetric)
    (intertwines : ∀ v, T (embed v) = embed (yukawaHamiltonian SU7ExteriorBreakingYukawa.exteriorBreakingScalar v)) :
    False := by
  apply yukawa_time_nonzero
  apply LinearMap.ext
  intro v
  apply faithful
  have square : T (T (embed v)) = 0 := by
    rw [intertwines, intertwines]
    have vanished := LinearMap.congr_fun
      (yukawa_time_square SU7ExteriorBreakingYukawa.exteriorBreakingScalar) v
    change yukawaHamiltonian SU7ExteriorBreakingYukawa.exteriorBreakingScalar
      (yukawaHamiltonian SU7ExteriorBreakingYukawa.exteriorBreakingScalar v) = 0 at vanished
    rw [vanished, map_zero]
  have zero := symmetric_no_jordan T symmetric (embed v) square
  rw [intertwines] at zero
  simpa using zero

end Positive
end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum
