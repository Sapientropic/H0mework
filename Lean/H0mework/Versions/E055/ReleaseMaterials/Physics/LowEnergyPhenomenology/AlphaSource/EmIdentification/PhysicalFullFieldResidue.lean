import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldScattering
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldContinuity

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalFullFieldScattering
open PreparationVacuumFullSlowFieldResponse PreparationVacuumMixedFieldReturn PreparationVacuumFieldCovector
open Filter
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField SU7MotherLieAlgebra StageNineLorentzConnectionVariation
open StageNineCoframeScalarMatterRegularity StageNineP286GaugeConnectionVariation
open SU7MotherGaugeTheory
open FullQuantum.StateGreen FullQuantum.Triangular YangMills.FullPairing
open FullQuantum.CoframeResponse FullQuantum.FullSpace
open Electromagnetic.CanonicalCoframe
open scoped Matrix BigOperators Topology InnerProductSpace

/-- The four normalized causal legs converge to their source residues.
    Common real scaling of the original scattering pair then gives its
    sixth-power limit, including the independent mixed contact. This names the
    full-field causal scattering residue, not a physical Thomson theorem:
    the physical identification of the external packet is a separate gate. -/
theorem actual_scattering_pair_residue
    (momentum : Fin 3 → ℝ)
    (Apos Aneg Bpos Bneg : CausalFieldLeg)
    (shift : Fin 3 → ℝ)
    (time age : ℝ) :
    Tendsto
      (fun d : ℝ =>
        (d : ℂ)^6 •
          actualScatteringPair
            momentum Apos Aneg Bpos Bneg shift time age d)
      (𝓝[>] 0)
      (𝓝 (actualScatteringResidue
        momentum Apos Aneg Bpos Bneg shift time age)) := by
  have hAp : Tendsto (fun d : ℝ => (d : ℂ)^3 • causalField Apos d) (𝓝[>] 0)
      (𝓝 (residueField Apos)) :=
    sourceJointCausalField_residue Apos.q Apos.wave Apos.frequency
      Apos.left Apos.right Apos.nonrealL Apos.nonrealR
  have hAn : Tendsto (fun d : ℝ => (d : ℂ)^3 • causalField Aneg d) (𝓝[>] 0)
      (𝓝 (residueField Aneg)) :=
    sourceJointCausalField_residue Aneg.q Aneg.wave Aneg.frequency
      Aneg.left Aneg.right Aneg.nonrealL Aneg.nonrealR
  have hBp : Tendsto (fun d : ℝ => (d : ℂ)^3 • causalField Bpos d) (𝓝[>] 0)
      (𝓝 (residueField Bpos)) :=
    sourceJointCausalField_residue Bpos.q Bpos.wave Bpos.frequency
      Bpos.left Bpos.right Bpos.nonrealL Bpos.nonrealR
  have hBn : Tendsto (fun d : ℝ => (d : ℂ)^3 • causalField Bneg d) (𝓝[>] 0)
      (𝓝 (residueField Bneg)) :=
    sourceJointCausalField_residue Bneg.q Bneg.wave Bneg.frequency
      Bneg.left Bneg.right Bneg.nonrealL Bneg.nonrealR
  have hprod : Tendsto
      (fun d : ℝ =>
        (((d : ℂ)^3 • causalField Apos d, (d : ℂ)^3 • causalField Aneg d),
          ((d : ℂ)^3 • causalField Bpos d, (d : ℂ)^3 • causalField Bneg d)))
      (𝓝[>] 0)
      (𝓝 ((residueField Apos, residueField Aneg),
        (residueField Bpos, residueField Bneg))) :=
    (hAp.prodMk_nhds hAn).prodMk_nhds (hBp.prodMk_nhds hBn)
  have hcomp : Tendsto
      ((fun p : FourFields =>
          originalScatteringPair momentum
            (originalTransferPair p.1.1 p.1.2)
            (originalTransferPair p.2.1 p.2.2) shift time age) ∘
        (fun d : ℝ =>
          (((d : ℂ)^3 • causalField Apos d, (d : ℂ)^3 • causalField Aneg d),
            ((d : ℂ)^3 • causalField Bpos d,
              (d : ℂ)^3 • causalField Bneg d))))
      (𝓝[>] 0)
      (𝓝 (actualScatteringResidue
        momentum Apos Aneg Bpos Bneg shift time age)) :=
    ((original_scattering_joint_continuous momentum shift time age).tendsto
      ((residueField Apos, residueField Aneg),
        (residueField Bpos, residueField Bneg))).comp hprod
  have heq :
      (fun d : ℝ =>
        (d : ℂ)^6 •
          actualScatteringPair
            momentum Apos Aneg Bpos Bneg shift time age d) =ᶠ[𝓝[>] 0]
      ((fun p : FourFields =>
          originalScatteringPair momentum
            (originalTransferPair p.1.1 p.1.2)
            (originalTransferPair p.2.1 p.2.2) shift time age) ∘
        (fun d : ℝ =>
          (((d : ℂ)^3 • causalField Apos d, (d : ℂ)^3 • causalField Aneg d),
            ((d : ℂ)^3 • causalField Bpos d,
              (d : ℂ)^3 • causalField Bneg d)))) :=
    Filter.Eventually.mono self_mem_nhdsWithin fun d hd => by
      have hdR : d ≠ 0 := ne_of_gt hd
      simp only [Function.comp_apply, actualScatteringPair, causalTransfer]
      have scalarCoe : (↑(((d : ℝ)^3)⁻¹) : ℂ) * (d : ℂ)^3 = 1 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul,
          inv_mul_cancel₀ (pow_ne_zero 3 hdR), Complex.ofReal_one]
      have cube : ∀ leg : CausalFieldLeg,
          causalField leg d =
            (↑(((d : ℝ)^3)⁻¹) : ℂ) • ((d : ℂ)^3 • causalField leg d) := by
        intro leg
        rw [smul_smul, scalarCoe, one_smul]
      conv_lhs => rw [cube Apos, cube Aneg, cube Bpos, cube Bneg]
      conv_lhs => rw [original_scattering_real_scale]
      conv_lhs => rw [smul_smul]
      have scalar1R : (d : ℝ)^6 * (((d : ℝ)^3)⁻¹)^2 = 1 := by
        rw [inv_pow, ← pow_mul]
        show (d : ℝ)^6 * ((d : ℝ)^6)⁻¹ = 1
        exact mul_inv_cancel₀ (pow_ne_zero 6 hdR)
      have scalar1 : (d : ℂ)^6 * (↑(((d : ℝ)^3)⁻¹) : ℂ)^2 = 1 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
          scalar1R, Complex.ofReal_one]
      rw [scalar1, one_smul]
  exact Filter.Tendsto.congr' heq.symm hcomp

end LowEnergy.GaussComposite.PhysicalFullFieldScattering
