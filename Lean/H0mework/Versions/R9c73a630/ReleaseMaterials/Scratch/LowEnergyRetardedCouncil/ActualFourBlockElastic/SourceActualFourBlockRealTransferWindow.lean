import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferAmplitude
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferRegular
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDenominators
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferReader
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockElasticNonzero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion ActualFourBlockSource MixedSpectatorCandidate ActualCandidateBra
open ActualFourBlockElastic Set
open scoped BigOperators
attribute [local irreducible] pairing coherentTree amplitude

private theorem imaginary_amplitude_nonzero (dual : Bool) : amplitude Complex.I dual ≠ 0 := by
  rw [actual_imaginary_amplitude,actual_imaginary_coherent_bra_value]
  apply mul_ne_zero (by norm_num)
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (show (0 : ℝ) < 30 by norm_num))

theorem actual_real_transfer_source_window :
    ∃δ : ℝ,0 < δ ∧ ∀x : ℝ,0 < |x| → |x| < δ →
      ∃p : Kinematics,p.x = x ∧ p.k = 0 ∧ p.pLeft = 0 ∧ p.pRight = 0 ∧
        ∀dual : Bool,coherentTree p (fiberCoordinates (candidate dual)) ≠ 0 := by
  let f : ℂ → ℂ := fun x => amplitude x false * amplitude x true
  have hm : MeromorphicOn f univ := by
    intro z hz
    exact (actual_amplitude_meromorphic false z hz).mul (actual_amplitude_meromorphic true z hz)
  have ha : AnalyticAt ℂ f Complex.I := (actual_amplitude_analytic_I false).mul (actual_amplitude_analytic_I true)
  have hn : f Complex.I ≠ 0 :=
    mul_ne_zero (imaginary_amplitude_nonzero false) (imaginary_amplitude_nonzero true)
  obtain ⟨δ,hδ,h⟩ := punctured_real_regular_of_imaginary_witness f sourceDenominator hm ha hn
    (fun i z _ => (actual_denominator_analytic z i).meromorphicAt)
    (actual_denominator_analytic Complex.I) actual_denominator_imaginary_nonzero
  refine ⟨δ,hδ,?_⟩
  intro x hx hxd
  obtain ⟨hamp,hden⟩ := h x hx hxd
  obtain ⟨hC,hD,hS⟩ := actual_denominators_regular x hden
  let p := axialKinematics x hC hD hS
  refine ⟨p,rfl,rfl,rfl,rfl,?_⟩
  intro dual hz
  have hn : amplitude x dual ≠ 0 := by
    cases dual
    · exact (mul_ne_zero_iff.mp hamp).1
    · exact (mul_ne_zero_iff.mp hamp).2
  have hb := actual_axial_coherent_bra x hC hD hS dual
  change pairing (fiberCoordinates (bra dual))
    (coherentTree p (fiberCoordinates (candidate dual))) = amplitude x dual at hb
  rw [hz] at hb
  have hzero : pairing (fiberCoordinates (bra dual)) (0 : Fock Mode) = 0 := by
    simp only [pairing,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  rw [hzero] at hb
  exact hn hb.symm

end LowEnergy.ActualFourBlockRealTransfer
