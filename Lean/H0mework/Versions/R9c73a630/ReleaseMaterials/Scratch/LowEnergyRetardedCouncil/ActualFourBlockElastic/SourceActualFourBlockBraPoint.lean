import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairs
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockImaginaryPoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 12000000
noncomputable section
namespace LowEnergy.ActualFourBlockElastic
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion ActualFourBlockSource MixedSpectatorCandidate
open ActualCandidateBra MixedSpectatorPairedSourceFrame
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

theorem actual_bra_normal_source_pair (dual : Bool) (a b : Fin 97) :
    pairing (fiberCoordinates (bra dual))
      (LowEnergy.Fermion.normalProduct
        (MixedSpectatorContactVertices.sourceVertex 0 a)
        (MixedSpectatorContactVertices.sourceVertex 0 b) (fiberCoordinates (candidate dual))) =
        ActualCandidateBra.pairPoint dual a b := by
  have h := ActualCandidateBra.actual_source_pair dual a b
  rw [fiber_pairing] at h
  exact h

attribute [local irreducible] pairing ActualCandidateBra.pairPoint
  MixedSpectatorContactVertices.sourceVertex MixedSpectatorScalar61Exchange.sourceVertex
  MixedSpectatorContactExchange.contactCoefficient
  MixedSpectatorCanonical79Exchange.canonicalCoefficient
  MixedSpectatorDual24Exchange.dualCoefficient MixedSpectatorScalar61Exchange.greenCoefficient

private theorem pair_sum_right {ι : Type*} [Fintype ι] (v : Fock Mode) (u : ι → Fock Mode) :
    pairing v (∑i : ι,u i) = ∑i : ι,pairing v (u i) := by
  simp only [pairing, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem pair_smul_right (c : ℂ) (v u : Fock Mode) :
    pairing v (c • u) = c * pairing v u := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem actual_bra_normal_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (dual : Bool) (coefficient : ι → κ → ℂ)
    (A : ι → Matrix Mode Mode ℂ) (B : κ → Matrix Mode Mode ℂ) :
    pairing (fiberCoordinates (bra dual))
      ((∑a : ι,∑b : κ,coefficient a b • LowEnergy.Fermion.normalProduct (A a) (B b))
        (fiberCoordinates (candidate dual))) =
      ∑a : ι,∑b : κ,coefficient a b *
        inner ℂ (bra dual) (SourceCoframeSpinNormalOrder.normalFiber (A a) (B b) (candidate dual)) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pair_sum_right, pair_smul_right]
  simp only [fiber_pairing]
  rfl

theorem actual_bra_source_sum (dual : Bool) (coefficient : Fin 97 → Fin 97 → ℂ) :
    pairing (fiberCoordinates (bra dual))
      ((∑a : Fin 97,∑b : Fin 97,coefficient a b • LowEnergy.Fermion.normalProduct
        (MixedSpectatorContactVertices.sourceVertex 0 a)
        (MixedSpectatorContactVertices.sourceVertex 0 b))
        (fiberCoordinates (candidate dual))) =
      ∑a : Fin 97,∑b : Fin 97,coefficient a b * ActualCandidateBra.pairPoint dual a b := by
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,pair_sum_right,pair_smul_right,
    actual_bra_normal_source_pair]

def braBlockPoint (dual : Bool) (b : Fin 4) : ℂ :=
  ![∑a : Fin 97,∑b : Fin 97,
      ((-1/2 : ℂ)*MixedSpectatorContactExchange.contactCoefficient (worldTransfer Complex.I 0) a b)*
        ActualCandidateBra.pairPoint dual a b,
    ∑a : Fin 97,∑b : Fin 97,
      ((-1/2 : ℂ)*MixedSpectatorCanonical79Exchange.canonicalCoefficient Complex.I 0 a b)*
        ActualCandidateBra.pairPoint dual a b,
    ∑a : Fin 97,∑b : Fin 97,
      ((-1/2 : ℂ)*MixedSpectatorDual24Exchange.dualCoefficient Complex.I 0 a b)*
        ActualCandidateBra.pairPoint dual a b,
    0] b

theorem actual_bra_block_point (dual : Bool) (b : Fin 4) :
    pairing (fiberCoordinates (bra dual))
      (block imaginaryKinematics b (fiberCoordinates (candidate dual))) = braBlockPoint dual b := by
  fin_cases b
  · exact actual_bra_source_sum dual (fun a b => (-1/2 : ℂ)*
      MixedSpectatorContactExchange.contactCoefficient (worldTransfer Complex.I 0) a b)
  · exact actual_bra_source_sum dual (fun a b => (-1/2 : ℂ)*
      MixedSpectatorCanonical79Exchange.canonicalCoefficient Complex.I 0 a b)
  · exact actual_bra_source_sum dual (fun a b => (-1/2 : ℂ)*
      MixedSpectatorDual24Exchange.dualCoefficient Complex.I 0 a b)
  · change pairing (fiberCoordinates (bra dual))
        ((∑a : Fin 70,∑b : Fin 70,
          ((-1/2 : ℂ)*MixedSpectatorScalar61Exchange.greenCoefficient
            (worldTransfer Complex.I 0) a b) • LowEnergy.Fermion.normalProduct
              (MixedSpectatorScalar61Exchange.sourceVertex a)
              (MixedSpectatorScalar61Exchange.sourceVertex b))
          (fiberCoordinates (candidate dual))) = 0
    have h := actual_bra_normal_sum dual
        (fun a b : Fin 70 => (-1/2 : ℂ)*
          MixedSpectatorScalar61Exchange.greenCoefficient (worldTransfer Complex.I 0) a b)
        MixedSpectatorScalar61Exchange.sourceVertex MixedSpectatorScalar61Exchange.sourceVertex
    simpa only [ActualCandidateBra.actual_scalar_source_pair_zero,mul_zero,
      Finset.sum_const_zero] using h

theorem actual_coherent_bra_point (dual : Bool) :
    pairing (fiberCoordinates (bra dual))
      (coherentTree imaginaryKinematics (fiberCoordinates (candidate dual))) =
        ∑b : Fin 4,braBlockPoint dual b := by
  simp only [coherentTree,LinearMap.sum_apply,pair_sum_right,actual_bra_block_point]

end LowEnergy.ActualFourBlockElastic
