import H0mework.Physics.LowEnergy.FullQuantum.FockEvolution
import Mathlib.Analysis.Calculus.MeanValue

/-! The full source Fock flow preserves its actual prepared one-particle sector. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedWeight
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineHolonomicField
open QuantizationCheck.Fermion
noncomputable section
attribute [local instance] Fermion.fullIndexOrder
local instance : Fintype (Finset Quantum.Index) := Fintype.ofFinite _
local instance : CompleteSpace (Fock Quantum.Index) :=
  inferInstanceAs (CompleteSpace (Finset Quantum.Index → ℂ))
local instance : NormedAlgebra ℚ (Fock Quantum.Index →L[ℂ] Fock Quantum.Index) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (Fock Quantum.Index →L[ℂ] Fock Quantum.Index) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

theorem fockGenerator_commute (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    Commute (fockGenerator C p k) (fockEvolution C p k t) := by
  have commute : Commute (fockGenerator C p k) (t • fockGenerator C p k) := by
    show fockGenerator C p k*(t • fockGenerator C p k)=(t • fockGenerator C p k)*fockGenerator C p k
    ext v i
    simp
  exact commute.exp_right

theorem oneParticle_inverse_derivative (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (v : DiracExteriorMatterCarrier) (t : ℝ) :
    HasDerivAt (fun time => fockEvolution C p k (-time)
      (oneParticle (Quantum.coordinates (primal C p k time v)))) 0 t := by
  have inverse := (fockEvolution_derivative C p k (-t)).scomp t (hasDerivAt_neg t)
  have restricted := (ContinuousLinearMap.restrictScalarsL ℂ
      (Fock Quantum.Index) (Fock Quantum.Index) ℝ ℝ).hasFDerivAt.comp_hasDerivAt t inverse
  have wave := original_oneParticle_evolution C p k t v
  have original : HasDerivAt (fun time => oneParticle (Quantum.coordinates (primal C p k time v)))
      (fockGenerator C p k (oneParticle (Quantum.coordinates (primal C p k t v)))) t := by
    simpa only [fockGenerator,smul_apply,LinearMap.coe_toContinuousLinearMap',quantumGenerator,
      Fermion.quantize_apply] using wave
  have generated := restricted.clm_apply original
  convert! generated using 1
  change 0=(-1 : ℝ) • fockGenerator C p k
      (fockEvolution C p k (-t) (oneParticle (Quantum.coordinates (primal C p k t v))))+
    fockEvolution C p k (-t) (fockGenerator C p k (oneParticle (Quantum.coordinates (primal C p k t v))))
  have commute := congrArg (fun A : Fock Quantum.Index →L[ℂ] Fock Quantum.Index =>
    A (oneParticle (Quantum.coordinates (primal C p k t v)))) (fockGenerator_commute C p k (-t)).eq
  change fockGenerator C p k (fockEvolution C p k (-t) _)=fockEvolution C p k (-t) (fockGenerator C p k _) at commute
  rw [commute]
  module

theorem fockEvolution_oneParticle (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (v : DiracExteriorMatterCarrier) (t : ℝ) :
    fockEvolution C p k t (oneParticle (Quantum.coordinates v))=
      oneParticle (Quantum.coordinates (primal C p k t v)) := by
  have constant := is_const_of_deriv_eq_zero
    (fun time => (oneParticle_inverse_derivative C p k v time).differentiableAt)
    (fun time => (oneParticle_inverse_derivative C p k v time).deriv) t 0
  have initial : fockEvolution C p k 0 (oneParticle (Quantum.coordinates (primal C p k 0 v)))=
      oneParticle (Quantum.coordinates v) := by
    rw [fockEvolution_zero,primal_zero]
    rfl
  simp only [neg_zero,initial] at constant
  have transported := congrArg (fockEvolution C p k t) constant
  have inverse : fockEvolution C p k t*fockEvolution C p k (-t)=1 := by
    rw [← fockEvolution_add,add_neg_cancel,fockEvolution_zero]
  have applied := congrArg (fun A : Fock Quantum.Index →L[ℂ] Fock Quantum.Index =>
    A (oneParticle (Quantum.coordinates (primal C p k t v)))) inverse
  change fockEvolution C p k t (fockEvolution C p k (-t) _)=_ at applied
  rw [applied] at transported
  exact transported.symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedWeight
