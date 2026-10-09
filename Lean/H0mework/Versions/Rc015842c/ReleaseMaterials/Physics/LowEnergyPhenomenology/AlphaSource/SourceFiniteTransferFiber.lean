import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteOriginVertices

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteTransferWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalNativeSoftWardBoundary PreparationPhysicalEnergyPoleChargeReturn
open PreparationPhysicalFiniteOriginCovariance PreparationPhysicalNormalizedFullField
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular CanonicalGradedSpatialSource
open MeasureTheory Filter
open scoped Topology InnerProductSpace
local instance : NormedAlgebra ℝ FiberOperators:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ FiberOperators:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : CompleteSpace FiberOperators:=ContinuousLinearMap.instCompleteSpace
attribute [local irreducible] sourceHamiltonianFiber sourceWardGenerator sourceWardInsertion

def sourceTransferHamiltonian (shift : PhysicalMomentum) : FiberOperators :=
  sourceCliffordFiber (spinPrincipal shift)

/-- The complete original Hamiltonian pays this momentum difference; no background lower term is deleted from either endpoint. -/
theorem sourceTransferHamiltonian_difference (left right : PhysicalMomentum) :
    sourceTransferHamiltonian (left-right)=sourceHamiltonianFiber left-sourceHamiltonianFiber right :=
  (sourceHamiltonianFiber_difference left right).symm

/-- The finite transfer adds its actual spatial-current insertion to the original X/negative-adjoint Ward current. -/
def sourceTransferInsertion (dual : Bool) (shift : PhysicalMomentum) : FiberOperators :=
  sourceWardInsertion dual+sourceTransferHamiltonian shift*sourceWardGenerator dual

theorem sourceTransferInsertion_between (dual : Bool) (left right : PhysicalMomentum) :
    sourceTransferInsertion dual (left-right)=
      sourceHamiltonianFiber left*sourceWardGenerator dual-sourceWardGenerator dual*sourceHamiltonianFiber right := by
  rw [sourceTransferInsertion,sourceTransferHamiltonian_difference,sourceWardInsertion_commutator dual right]
  rw [sub_mul]
  abel

theorem sourceTransferInsertion_offsets (dual : Bool) (left right p : PhysicalMomentum) :
    sourceTransferInsertion dual (left-right)=
      sourceHamiltonianFiber (p+left)*sourceWardGenerator dual-sourceWardGenerator dual*sourceHamiltonianFiber (p+right) := by
  have shift : (p+left)-(p+right)=left-right := by abel
  simpa only [shift] using sourceTransferInsertion_between dual (p+left) (p+right)

/-- Both independent spectral inputs and temporal principal inverses keep their original order, including the full nonselfadjoint defect. -/
theorem sourceTransferDiracWard (dual : Bool) (left right : PhysicalMomentum)
    (energyL dampingL energyR dampingR : ℝ) (positiveL : 0<dampingL) (positiveR : 0<dampingR) :
    (Retarded.diracValue 0 left energyL dampingL).adjoint*
      sourceTransferInsertion dual (left-right)*Retarded.diracValue 0 right energyR dampingR=
      (star (Retarded.spectralParameter energyL dampingL)-Retarded.spectralParameter energyR dampingR) •
        ((Retarded.diracValue 0 left energyL dampingL).adjoint*sourceWardGenerator dual*Retarded.diracValue 0 right energyR dampingR)+
      Complex.I • (sourceEnergyTemporalInverse.adjoint*sourceWardGenerator dual*Retarded.diracValue 0 right energyR dampingR)+
      Complex.I • ((Retarded.diracValue 0 left energyL dampingL).adjoint*sourceWardGenerator dual*sourceEnergyTemporalInverse)+
      (Retarded.diracValue 0 left energyL dampingL).adjoint*sourceEnergyYukawaDefect*
        sourceWardGenerator dual*Retarded.diracValue 0 right energyR dampingR := by
  rw [sourceTransferInsertion_between]
  have split :
      (Retarded.diracValue 0 left energyL dampingL).adjoint*
        (sourceHamiltonianFiber left*sourceWardGenerator dual-sourceWardGenerator dual*sourceHamiltonianFiber right)*
          Retarded.diracValue 0 right energyR dampingR=
      ((Retarded.diracValue 0 left energyL dampingL).adjoint*(sourceHamiltonianFiber left).adjoint)*
        sourceWardGenerator dual*Retarded.diracValue 0 right energyR dampingR-
      (Retarded.diracValue 0 left energyL dampingL).adjoint*sourceWardGenerator dual*
        (sourceHamiltonianFiber right*Retarded.diracValue 0 right energyR dampingR)+
      (Retarded.diracValue 0 left energyL dampingL).adjoint*
        (sourceHamiltonianFiber left-(sourceHamiltonianFiber left).adjoint)*
          sourceWardGenerator dual*Retarded.diracValue 0 right energyR dampingR := by
    simp only [mul_sub,sub_mul,mul_assoc]
    abel
  rw [split,sourceEnergyDiracGreen_dual left energyL dampingL positiveL,
    sourceEnergyDiracGreen_hamiltonian right energyR dampingR positiveR,sourceHamiltonianFiber_dual_defect]
  simp only [add_mul,mul_sub,smul_mul_assoc,mul_smul_comm,sub_smul]
  abel

def sourceTransferFiber (dual : Bool) (left right p : PhysicalMomentum) (time : ℝ) : FiberOperators :=
  evolution actual 0 (p+left) (-time)*sourceWardGenerator dual*evolution actual 0 (p+right) time

def sourceTransferCurrentFiber (dual : Bool) (left right p : PhysicalMomentum) (time : ℝ) : FiberOperators :=
  evolution actual 0 (p+left) (-time)*sourceTransferInsertion dual (left-right)*evolution actual 0 (p+right) time

/-- The full source drift differentiates the two distinct momenta; the spatial transfer term is retained. -/
theorem sourceTransferFiber_derivative (dual : Bool) (left right p : PhysicalMomentum) (time : ℝ) :
    HasDerivAt (sourceTransferFiber dual left right p)
      (Complex.I • sourceTransferCurrentFiber dual left right p time) time := by
  have backward:=(evolution_derivative actual 0 (p+left) (-time)).scomp time (hasDerivAt_neg time)
  have generated:=(backward.mul_const (sourceWardGenerator dual)).mul
    (evolution_derivative actual 0 (p+right) time)
  have commute:=evolution_commutes actual 0 (p+right) time
  rw [sourceWardDrift] at commute
  have commuteH : evolution actual 0 (p+right) time*sourceHamiltonianFiber (p+right)=
      sourceHamiltonianFiber (p+right)*evolution actual 0 (p+right) time := by
    have undo:=congrArg (fun A : FiberOperators=>Complex.I • A) commute
    simpa only [mul_smul_comm,smul_mul_assoc,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul] using undo
  convert! generated using 1
  simp only [Function.comp_apply,sourceTransferCurrentFiber,sourceTransferInsertion_offsets dual left right p,
    sourceWardDrift,mul_smul_comm,neg_smul,mul_sub,sub_mul,smul_sub,mul_assoc]
  rw [commuteH]
  apply ContinuousLinearMap.ext
  intro v
  simp only [mul_apply_eq_comp,smul_apply,sub_apply,add_apply,neg_apply,one_smul]
  module

theorem sourceTransferCurrentFiber_continuous (dual : Bool) (left right p : PhysicalMomentum) :
    Continuous (sourceTransferCurrentFiber dual left right p) := by
  have flow (q : PhysicalMomentum) : Continuous (evolution actual 0 q):=
    continuous_iff_continuousAt.mpr fun t=>(evolution_derivative actual 0 q t).continuousAt
  exact (((flow (p+left)).comp continuous_neg).mul continuous_const).mul (flow (p+right))

theorem sourceTransferCurrentFiber_bound (dual : Bool) (left right p : PhysicalMomentum) (time : ℝ) :
    ‖sourceTransferCurrentFiber dual left right p time‖≤
      (1+|time| *sourceRate 0)^2*‖sourceTransferInsertion dual (left-right)‖ := by
  have forward:=complete_evolution_bound actual 0 (p+right) (original_freeHamiltonian_selfAdjoint 0 _) time
  have backward:=complete_evolution_bound actual 0 (p+left) (original_freeHamiltonian_selfAdjoint 0 _) (-time)
  simp only [abs_neg] at backward
  have generated:=norm_mul_le_of_le (norm_mul_le_of_le backward (le_refl ‖sourceTransferInsertion dual (left-right)‖)) forward
  exact generated.trans_eq (by unfold sourceRate;ring)

end LowEnergy.PreparationPhysicalFiniteTransferWard
