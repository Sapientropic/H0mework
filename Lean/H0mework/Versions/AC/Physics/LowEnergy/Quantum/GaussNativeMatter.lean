import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceQuantumFockGauge

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussNativeMatter
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore DiracExteriorMatterAction StageNineHolonomicField
open StageNineCoframeGravityGaugeRegularity StageNineFullDiracAdjointLocalOperator
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineP286GaugeConnectionVariation
open scoped ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

private def nativeRead : NativeLie →ₗ[ℝ] P286CoordinateCarrier where
  toFun a := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def nativePrimal : NativeLie →ₗ[ℝ] Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ where
  toFun a := LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (nativeRead a))))
  map_add' a b := by
    rw [nativeRead.map_add, p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add, diracExteriorMotherLieAction_add]
    exact LowEnergy.Quantum.operatorMatrix.map_add _ _
  map_smul' r a := by
    rw [nativeRead.map_smul, p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul]
    rw [RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact LowEnergy.Quantum.operatorMatrix.toLinearEquiv.map_smul (r : ℂ)
        (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (nativeRead a))))

def nativeFull : NativeLie →ₗ[ℝ] Matrix Mode Mode ℂ where
  toFun a := Matrix.fromBlocks (nativePrimal a) 0 0 ((nativePrimal a).map (starRingEnd ℂ))
  map_add' a b := by
    ext i j
    cases i <;> cases j <;> simp [map_add, Matrix.fromBlocks, Matrix.map_apply]
  map_smul' r a := by
    ext i j
    cases i <;> cases j <;>
      simp [map_smul, Matrix.fromBlocks, Matrix.map_apply]

theorem nativePrimal_stabilizer (a : stabilizer) : nativePrimal (a : NativeLie) = primalGaugeMatrix a := rfl

theorem nativeFull_stabilizer (a : stabilizer) : nativeFull (a : NativeLie) = fullGaugeMatrix a := rfl

theorem nativePrimal_skew (a : NativeLie) : (nativePrimal a).conjTranspose = -nativePrimal a := by
  classical
  have hpair (u v : DiracExteriorMatterCarrier) :
      LowEnergy.Quantum.coordinatePair (diracExteriorMotherLieAction
        (p286LieBlockEmbed (p286CoordinateEquiv.symm a)) u) v +
      LowEnergy.Quantum.coordinatePair u (diracExteriorMotherLieAction
        (p286LieBlockEmbed (p286CoordinateEquiv.symm a)) v) = 0 := by
    rw [LowEnergy.Quantum.coordinatePair_full, LowEnergy.Quantum.coordinatePair_full, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun spin _ => fullInternalPair_motherLie_skew _ (u spin) (v spin))
  ext i j
  have h := hpair (LowEnergy.Quantum.coordinates.symm (Pi.single i 1))
    (LowEnergy.Quantum.coordinates.symm (Pi.single j 1))
  simp only [LowEnergy.Quantum.coordinatePair, ← LowEnergy.Quantum.matrix_action,
    LinearEquiv.apply_symm_apply] at h
  change star (nativePrimal a j i) = -(nativePrimal a i j)
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite, ite_mul] at h
  exact eq_neg_of_add_eq_zero_left h

theorem nativeFull_skew (a : NativeLie) : (nativeFull a).conjTranspose = -nativeFull a := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j => exact congrFun (congrFun (nativePrimal_skew a) i) j
    | inr j => simp [nativeFull]
  | inr i => cases j with
    | inl j => simp [nativeFull]
    | inr j =>
      have h := congrArg star (congrFun (congrFun (nativePrimal_skew a) i) j)
      simpa [nativeFull, Matrix.conjTranspose_apply] using h

theorem quantizedFiber_add (A B : Matrix Mode Mode ℂ) :
    quantizedFiber (A+B) = quantizedFiber A + quantizedFiber B := by
  have h : LowEnergy.Fermion.quantize (A+B) =
      LowEnergy.Fermion.quantize A + LowEnergy.Fermion.quantize B := by
    simp only [LowEnergy.Fermion.quantize, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  ext psi
  simp [quantizedFiber, h]

def nativeFock : NativeLie →ₗ[ℝ] FockFiber →L[ℂ] FockFiber where
  toFun a := (quantizedFiber (nativeFull a)).toContinuousLinearMap
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro psi
    rw [map_add, quantizedFiber_add]
    rfl
  map_smul' r a := by
    apply ContinuousLinearMap.ext
    intro psi
    rw [map_smul]
    change quantizedFiber ((r : ℂ) • nativeFull a) psi = (r : ℂ) • quantizedFiber (nativeFull a) psi
    rw [quantizedFiber_smul]
    rfl

theorem nativeFock_stabilizer (a : stabilizer) : nativeFock (a : NativeLie) = fiberGenerator a := rfl

theorem nativeFock_skew (a : NativeLie) (psi phi : FockFiber) :
    inner ℂ (nativeFock a psi) phi + inner ℂ psi (nativeFock a phi) = 0 :=
  quantizedFiber_skew (nativeFull a) (nativeFull_skew a) psi phi

#print axioms nativeFull_stabilizer
#print axioms nativeFock
#print axioms nativeFock_skew
end LowEnergy.GaussNativeMatter
