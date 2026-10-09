import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginEnergyWard
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedSoftObservable

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativeSoftWardBoundary
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace
local instance : NormedAlgebra ℝ FiberOperators:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ FiberOperators:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : CompleteSpace FiberOperators:=ContinuousLinearMap.instCompleteSpace

/-- The actual negative-frequency adjoint keeps the entire original Yukawa defect. -/
def sourceWardDualDefect : FiberOperators :=
  sourceEnergyYukawaDefect*sourceNativeOriginGeneratorFiber.adjoint-
    sourceNativeOriginGeneratorFiber.adjoint*sourceEnergyYukawaDefect

def sourceWardGenerator (dual : Bool) : FiberOperators :=
  if dual then -sourceNativeOriginGeneratorFiber.adjoint else sourceNativeOriginGeneratorFiber

def sourceWardInsertion (dual : Bool) : FiberOperators :=
  if dual then (sourceNativeOriginCanonicalFiber 0).adjoint-sourceWardDualDefect
  else sourceNativeOriginCanonicalFiber 0

theorem sourceWardInsertion_commutator (dual : Bool) (p : (Fin 3 → ℝ)) :
    sourceWardInsertion dual=sourceHamiltonianFiber p*sourceWardGenerator dual-
      sourceWardGenerator dual*sourceHamiltonianFiber p := by
  have actual:=sourceNativeOriginEnergyFiber p
  rw [sourceNativeOriginEnergy_NoetherFiber] at actual
  have direct : sourceNativeOriginCanonicalFiber 0=
      sourceHamiltonianFiber p*sourceNativeOriginGeneratorFiber-
        sourceNativeOriginGeneratorFiber*sourceHamiltonianFiber p := by
    apply neg_injective
    simpa only [neg_sub] using actual
  cases dual
  · exact direct
  · have adjoint:=congrArg ContinuousLinearMap.adjoint direct
    simp only [map_sub,←ContinuousLinearMap.star_eq_adjoint,star_mul] at adjoint
    simp only [ContinuousLinearMap.star_eq_adjoint] at adjoint
    simp only [sourceWardInsertion,sourceWardGenerator,ite_true,
      sourceWardDualDefect,adjoint,←sourceHamiltonianFiber_dual_defect p]
    apply ContinuousLinearMap.ext
    intro v
    simp only [mul_apply_eq_comp,sub_apply,neg_apply,map_sub,map_neg]
    abel

/-- The source drift is exactly minus i times the full Hamiltonian. -/
theorem sourceWardDrift (p : (Fin 3 → ℝ)) :
    operator (drift actual 0 p)=(-Complex.I) • sourceHamiltonianFiber p := by
  rw [←hamiltonian_drift,operator_smul]
  rfl

def sourceWardFiber (dual : Bool) (p : (Fin 3 → ℝ)) (time : ℝ) : FiberOperators :=
  evolution actual 0 p (-time)*sourceWardGenerator dual*evolution actual 0 p time

def sourceWardCurrentFiber (dual : Bool) (p : (Fin 3 → ℝ)) (time : ℝ) : FiberOperators :=
  evolution actual 0 p (-time)*sourceWardInsertion dual*evolution actual 0 p time

/-- Both derivatives use the original drift sign and the original nonunitary full flow. -/
theorem sourceWardFiber_derivative (dual : Bool) (p : (Fin 3 → ℝ)) (time : ℝ) :
    HasDerivAt (sourceWardFiber dual p)
      (Complex.I • sourceWardCurrentFiber dual p time) time := by
  have backward := (evolution_derivative actual 0 p (-time)).scomp time (hasDerivAt_neg time)
  have generated := (backward.mul_const (sourceWardGenerator dual)).mul
    (evolution_derivative actual 0 p time)
  have commute:=evolution_commutes actual 0 p time
  rw [sourceWardDrift] at commute
  have commuteH : evolution actual 0 p time*sourceHamiltonianFiber p=
      sourceHamiltonianFiber p*evolution actual 0 p time := by
    have undo:=congrArg (fun A : FiberOperators=>Complex.I • A) commute
    simpa only [mul_smul_comm,smul_mul_assoc,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul] using undo
  convert! generated using 1
  simp only [Function.comp_apply,sourceWardCurrentFiber,sourceWardInsertion_commutator dual p,sourceWardDrift,
    mul_smul_comm,neg_smul,mul_sub,sub_mul,smul_sub,mul_assoc]
  rw [commuteH]
  apply ContinuousLinearMap.ext
  intro v
  simp only [mul_apply_eq_comp,smul_apply,sub_apply,add_apply,neg_apply,one_smul]
  module

theorem sourceWardCurrentFiber_continuous (dual : Bool) (p : (Fin 3 → ℝ)) :
    Continuous (sourceWardCurrentFiber dual p) := by
  have flow : Continuous (evolution actual 0 p):=
    continuous_iff_continuousAt.mpr fun t=>(evolution_derivative actual 0 p t).continuousAt
  exact ((flow.comp continuous_neg).mul continuous_const).mul flow

theorem sourceWardCurrentFiber_bound (dual : Bool) (p : (Fin 3 → ℝ)) (time : ℝ) :
    ‖sourceWardCurrentFiber dual p time‖≤(1+|time| *sourceRate 0)^2*‖sourceWardInsertion dual‖ := by
  have forward:=complete_evolution_bound actual 0 p (original_freeHamiltonian_selfAdjoint 0 p) time
  have backward:=complete_evolution_bound actual 0 p (original_freeHamiltonian_selfAdjoint 0 p) (-time)
  simp only [abs_neg] at backward
  have generated:=norm_mul_le_of_le (norm_mul_le_of_le backward (le_refl ‖sourceWardInsertion dual‖)) forward
  exact generated.trans_eq (by unfold sourceRate; ring)

/-- This is the finite-dimensional Duhamel identity before lifting to the whole original L2 carrier. -/
theorem sourceWardFiber_boundary (dual : Bool) (p : (Fin 3 → ℝ)) (time : ℝ) :
    Complex.I • (∫s in (0:ℝ)..time,sourceWardCurrentFiber dual p s)=
      sourceWardFiber dual p time-sourceWardGenerator dual := by
  have generated:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _=>sourceWardFiber_derivative dual p s)
    (((sourceWardCurrentFiber_continuous dual p).const_smul Complex.I).intervalIntegrable (0:ℝ) time)
  simpa only [intervalIntegral.integral_smul,sourceWardFiber,neg_zero,evolution_zero,one_mul,mul_one] using generated

end LowEnergy.PreparationPhysicalNativeSoftWardBoundary
