import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceCoframeCovariantCurrent
import H0mework.Physics.LowEnergyFermion.NormalOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceCoframeSpinNormalOrder
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoframeForm SourceCoframeCovariantSquare GaussQuantumMultiplier
open scoped ContDiff Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber

/-- Original four-operator normal product transported by the fixed occupation coordinates. -/
def normalFiber (A B : Matrix Mode Mode ℂ) : FiberEnd :=
  (fiberCoordinates.symm.toLinearMap.comp
    ((SaturationMonoid.PhysicsCore.LowEnergy.Fermion.normalProduct A B).comp fiberCoordinates.toLinearMap)).toContinuousLinearMap

/-- Exact source CAR normal ordering; second quantization is not treated as a multiplicative map. -/
theorem original_fiber_normal_order (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B=quantized (A*B)+normalFiber A B := by
  apply ContinuousLinearMap.ext
  intro psi
  apply fiberCoordinates.injective
  change SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize A
      (SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize B (fiberCoordinates psi))=
    SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize (A*B) (fiberCoordinates psi)+
      SaturationMonoid.PhysicsCore.LowEnergy.Fermion.normalProduct A B (fiberCoordinates psi)
  exact LinearMap.congr_fun (SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize_normal_order A B) (fiberCoordinates psi)

def oneBody : FiberEnd := (∑ a : Fin 7,(residualWeight a : ℂ) •
  quantized (GaussCoframeSpin.full a*GaussCoframeSpin.full a))+(-9/8 : ℂ) • fiberNumber

def quartic : FiberEnd := ∑ a : Fin 7,(residualWeight a : ℂ) •
  normalFiber (GaussCoframeSpin.full a) (GaussCoframeSpin.full a)

def quarticKernel (i j k l : Mode) : ℂ := ∑ a : Fin 7,(residualWeight a : ℂ)*
  (GaussCoframeSpin.full a i j*GaussCoframeSpin.full a k l)

/-- The complete four-index source coefficient retains the original creation/annihilation order. -/
theorem original_quartic_kernel (psi : FockFiber) :
    fiberCoordinates (quartic psi)=∑ i : Mode,∑ j : Mode,∑ k : Mode,∑ l : Mode,
      quarticKernel i j k l • ((SaturationMonoid.PhysicsCore.LowEnergy.Fermion.creation i*
        SaturationMonoid.PhysicsCore.LowEnergy.Fermion.creation k*
        SaturationMonoid.PhysicsCore.LowEnergy.Fermion.annihilation l*
        SaturationMonoid.PhysicsCore.LowEnergy.Fermion.annihilation j) (fiberCoordinates psi)) := by
  have hc (A B : Matrix Mode Mode ℂ) (p : FockFiber) : fiberCoordinates (normalFiber A B p)=
      SaturationMonoid.PhysicsCore.LowEnergy.Fermion.normalProduct A B (fiberCoordinates p) := rfl
  simp only [quartic,sum_apply,smul_apply,map_sum,map_smul,hc]
  simp only [SaturationMonoid.PhysicsCore.LowEnergy.Fermion.normalProduct,LinearMap.sum_apply,
    LinearMap.smul_apply,Finset.smul_sum,smul_smul,quarticKernel,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- The actual spin remainder, including its number shift, contains its full original quartic CAR term. -/
theorem original_spin_normal_fiber :
    (∑ a : Fin 7,(residualWeight a : ℂ) • (quantized (GaussCoframeSpin.full a)*quantized (GaussCoframeSpin.full a)))+
      (-9/8 : ℂ) • fiberNumber=oneBody+quartic := by
  simp_rw [original_fiber_normal_order]
  simp only [smul_add,Finset.sum_add_distrib,oneBody,quartic]
  abel

private theorem number_value (f : QuantumTest) (z : SourceCoordinateSlice) :
    number f z=fiberNumber (f z) := by
  apply PiLp.ext
  intro w
  exact (number_apply f z w).trans (fiberNumber_apply (f z) w).symm
private def evaluate (z : SourceCoordinateSlice) : QuantumTest →ₗ[ℂ] FockFiber where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The normal-ordered fibre is evaluated in the original coframe action on the original compact core. -/
theorem original_spin_normal_action (f : QuantumTest) (z : SourceCoordinateSlice) :
    (spinRemainder+numberShift) f z=(inverseVolume z : ℂ) • ((oneBody+quartic) (f z)) := by
  have h := congrArg (fun A : FiberEnd => (inverseVolume z : ℂ) • A (f z)) original_spin_normal_fiber
  rw [←h]
  change evaluate z (spinRemainder f+numberShift f)=_
  rw [map_add]
  have hs : evaluate z (spinRemainder f)=(inverseVolume z : ℂ) •
      (∑ a : Fin 7,(residualWeight a : ℂ) • (quantized (GaussCoframeSpin.full a)*quantized (GaussCoframeSpin.full a))) (f z) := by
    simp only [spinRemainder,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sum,map_smul]
    change (∑ a : Fin 7,(residualWeight a : ℂ) • quantized (GaussCoframeSpin.full a)
      ((inverseVolume z : ℂ) • quantized (GaussCoframeSpin.full a) (f z)))=_
    simp only [map_smul,sum_apply,smul_apply,mul_apply_eq_comp,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring
  rw [hs]
  have hn : evaluate z (numberShift f)=(inverseVolume z : ℂ) • ((-9/8 : ℂ) • fiberNumber (f z)) := by
    change (1/2 : ℂ) • (number (multiply numberCoefficient numberCoefficient_smooth f) z+
      multiply numberCoefficient numberCoefficient_smooth (number f) z)=_
    rw [number_value,multiply_apply,multiply_apply,number_value,map_smul]
    simp only [numberCoefficient,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_div,
      Complex.ofReal_ofNat,smul_add,smul_smul]
    module
  rw [hn]
  simp only [add_apply,smul_apply,smul_add]

/-- The same original differential coframe action consumes the actual one-body and four-operator source terms. -/
theorem original_coframe_normal_action (f : QuantumTest) (z : SourceCoordinateSlice) :
    coframeAction f z=SourceCoframeCovariantAction.covariantKinetic f z+
      (inverseVolume z : ℂ) • ((oneBody+quartic) (f z))+
        multiply volumePotential volumePotential_smooth f z := by
  rw [original_coframe_covariant]
  simp only [LinearMap.add_apply]
  change SourceCoframeCovariantAction.covariantKinetic f z+spinRemainder f z+numberShift f z+
    multiply volumePotential volumePotential_smooth f z=_
  have h := original_spin_normal_action f z
  change spinRemainder f z+numberShift f z=_ at h
  rw [←h]
  abel

end LowEnergy.SourceCoframeSpinNormalOrder
