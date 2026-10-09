import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferLocalAnalytic
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferScalarRows
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferContact
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferFiberCarrier
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion ActualFourBlockSource ActualFourBlockDetector
open MixedSpectatorPairedSourceFrame
open scoped BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

theorem actual_axial_fiber_analytic (z : ℂ)
    (hC : MixedSpectatorCanonical79Exchange.RegularMomentum z 0)
    (hD : MixedSpectatorDual24Exchange.RegularMomentum z 0)
    (hS : MixedSpectatorScalar61Exchange.denominator (worldTransfer z 0) ≠ 0) :
    AnalyticAt ℂ axialFiber z := by
  change AnalyticAt ℂ (fun x => fiberLift (axialTree x)) z
  simp only [axialTree,map_add,map_sum,map_smul]
  apply AnalyticAt.add
  · apply AnalyticAt.add
    · apply AnalyticAt.add
      · apply Finset.analyticAt_fun_sum
        intro a _
        apply Finset.analyticAt_fun_sum
        intro b _
        exact (analyticAt_const.mul (actual_contact_coefficient_analytic z a b)).smul analyticAt_const
      · apply Finset.analyticAt_fun_sum
        intro a _
        apply Finset.analyticAt_fun_sum
        intro b _
        exact (analyticAt_const.mul (actual_canonical_coefficient_analytic z hC a b)).smul analyticAt_const
    · apply Finset.analyticAt_fun_sum
      intro a _
      apply Finset.analyticAt_fun_sum
      intro b _
      exact (analyticAt_const.mul (actual_dual_coefficient_analytic z hD a b)).smul analyticAt_const
  · apply Finset.analyticAt_fun_sum
    intro a _
    apply Finset.analyticAt_fun_sum
    intro b _
    exact (analyticAt_const.mul (actual_scalar_coefficient_analytic z hS a b)).smul analyticAt_const

end LowEnergy.ActualFourBlockRealTransfer
