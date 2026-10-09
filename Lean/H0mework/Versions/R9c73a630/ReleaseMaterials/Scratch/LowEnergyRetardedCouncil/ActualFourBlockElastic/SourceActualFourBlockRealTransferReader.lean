import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockBraPoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion ActualFourBlockSource MixedSpectatorCandidate
open ActualCandidateBra ActualFourBlockElastic MixedSpectatorPairedSourceFrame
open scoped BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

def amplitude (x : ℂ) (dual : Bool) : ℂ :=
  (∑a : Fin 97,∑b : Fin 97,
    ((-1/2 : ℂ)*MixedSpectatorContactExchange.contactCoefficient (worldTransfer x 0) a b)*
      ActualCandidateBra.pairPoint dual a b) +
  (∑a : Fin 97,∑b : Fin 97,
    ((-1/2 : ℂ)*MixedSpectatorCanonical79Exchange.canonicalCoefficient x 0 a b)*
      ActualCandidateBra.pairPoint dual a b) +
  (∑a : Fin 97,∑b : Fin 97,
    ((-1/2 : ℂ)*MixedSpectatorDual24Exchange.dualCoefficient x 0 a b)*
      ActualCandidateBra.pairPoint dual a b)

def axialKinematics (x : ℂ)
    (hC : MixedSpectatorCanonical79Exchange.RegularMomentum x 0)
    (hD : MixedSpectatorDual24Exchange.RegularMomentum x 0)
    (hS : MixedSpectatorScalar61Exchange.denominator (worldTransfer x 0) ≠ 0) : Kinematics where
  x := x
  k := 0
  pLeft := 0
  pRight := 0
  canonicalRegular := hC
  dualRegular := hD
  scalarRegular := hS

attribute [local irreducible] pairing ActualCandidateBra.pairPoint block coherentTree
  MixedSpectatorContactVertices.sourceVertex MixedSpectatorScalar61Exchange.sourceVertex
  MixedSpectatorContactExchange.contactCoefficient
  MixedSpectatorCanonical79Exchange.canonicalCoefficient
  MixedSpectatorDual24Exchange.dualCoefficient MixedSpectatorScalar61Exchange.greenCoefficient

private theorem pair_sum_right {ι : Type*} [Fintype ι] (v : Fock Mode) (u : ι → Fock Mode) :
    pairing v (∑i : ι,u i) = ∑i : ι,pairing v (u i) := by
  simp only [pairing, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The original scalar department remains in the actual four-block operator.
Its fixed-bra read is zero by the full70 source-entry CAR law at every transfer. -/
theorem actual_axial_coherent_bra (x : ℂ)
    (hC : MixedSpectatorCanonical79Exchange.RegularMomentum x 0)
    (hD : MixedSpectatorDual24Exchange.RegularMomentum x 0)
    (hS : MixedSpectatorScalar61Exchange.denominator (worldTransfer x 0) ≠ 0)
    (dual : Bool) :
    pairing (fiberCoordinates (bra dual))
      (coherentTree (axialKinematics x hC hD hS) (fiberCoordinates (candidate dual))) =
        amplitude x dual := by
  rw [coherentTree,LinearMap.sum_apply,pair_sum_right,Fin.sum_univ_four]
  unfold ActualFourBlockSource.block
  dsimp only [axialKinematics]
  have h3 : (3 : Fin 4) = (2 : Fin 3).succ := rfl
  rw [h3]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Fin.succ_zero_eq_one]
  unfold MixedSpectatorContactExchange.actualContactTree
    MixedSpectatorCanonical79Exchange.actualCanonicalTree
    MixedSpectatorDual24Exchange.actualDualTree MixedSpectatorScalar61Exchange.actualScalar61Tree
  rw [actual_bra_source_sum,actual_bra_source_sum,actual_bra_source_sum]
  have hs := actual_bra_normal_sum dual
    (fun a b : Fin 70 => (-1/2 : ℂ)*
      MixedSpectatorScalar61Exchange.greenCoefficient (worldTransfer x 0) a b)
    MixedSpectatorScalar61Exchange.sourceVertex MixedSpectatorScalar61Exchange.sourceVertex
  simp only [ActualCandidateBra.actual_scalar_source_pair_zero,mul_zero,
    Finset.sum_const_zero] at hs
  rw [hs,add_zero]
  rfl

theorem actual_imaginary_amplitude (dual : Bool) :
    amplitude Complex.I dual = pairing (fiberCoordinates (bra dual))
      (coherentTree imaginaryKinematics (fiberCoordinates (candidate dual))) :=
  (actual_axial_coherent_bra Complex.I actual_imaginary_canonical_regular
    actual_imaginary_dual_regular actual_imaginary_scalar_regular dual).symm

end LowEnergy.ActualFourBlockRealTransfer
