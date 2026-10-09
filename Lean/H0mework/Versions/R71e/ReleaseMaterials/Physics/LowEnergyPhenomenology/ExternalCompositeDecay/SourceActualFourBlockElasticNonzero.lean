import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockBraPoint
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualBraContactDualContraction
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualBraDualExchange
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraSourceContraction
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraScalarContraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockElastic
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion ActualFourBlockSource MixedSpectatorCandidate
open ActualCandidateBra ActualBraContactDualContraction ActualCanonical79Imaginary
open scoped BigOperators Matrix
attribute [local irreducible] pairing ActualCandidateBra.pairPoint
  MixedSpectatorCanonical79Exchange.canonicalCoefficient

theorem actual_imaginary_canonical_bra_value (dual : Bool) :
    (∑a : Fin 97,∑b : Fin 97,
      ((-1/2 : ℂ)*MixedSpectatorCanonical79Exchange.canonicalCoefficient Complex.I 0 a b)*
        ActualCandidateBra.pairPoint dual a b) =
      (50304430064141165448074104830433/97699116566232156027102301987500 : ℂ)*
        (Real.sqrt 30 : ℂ) := by
  calc
    _ = ∑i : Fin 79,∑j : Fin 79,
        ((-1/2 : ℂ)*MixedSpectatorCanonical79Data.axialInverse Complex.I 0 i j)*
          currentPoint dual i j := actual_canonical_source_bra dual
    _ = ((11883666571412341/35669395945134500 : ℂ) -
          3409605742/277762698775 - 14903039908/277762698775 +
            1088882209340648877779/4396698917687141306250)*(Real.sqrt 30 : ℂ) :=
      actual_canonical_bra_contraction dual
    _ = _ := by ring

theorem actual_imaginary_coherent_bra_value (dual : Bool) :
    pairing (fiberCoordinates (bra dual))
      (coherentTree imaginaryKinematics (fiberCoordinates (candidate dual))) =
        (1502925864947895702084635234454041/3859115104366170163070540928506250 : ℂ)*
          (Real.sqrt 30 : ℂ) := by
  have h (b : Fin 4) : braBlockPoint dual b =
      (![((-1/25 : ℂ)*(Real.sqrt 30 : ℂ)),
        ((50304430064141165448074104830433/97699116566232156027102301987500 : ℂ)*
          (Real.sqrt 30 : ℂ)),
        ((-27/316 : ℂ)*(Real.sqrt 30 : ℂ)),0] : Fin 4 → ℂ) b := by
    fin_cases b
    · exact actual_contact_bra_contraction dual
    · exact actual_imaginary_canonical_bra_value dual
    · exact actual_dual_bra_value dual
    · rfl
  rw [actual_coherent_bra_point]
  simp_rw [h]
  norm_num [Fin.sum_univ_succ]
  ring

theorem actual_imaginary_coherent_candidate_nonzero (dual : Bool) :
    coherentTree imaginaryKinematics (fiberCoordinates (candidate dual)) ≠ 0 := by
  intro hz
  have hv := actual_imaginary_coherent_bra_value dual
  have hp : pairing (fiberCoordinates (bra dual)) (0 : Fock Mode) = 0 := by
    simp only [pairing,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  rw [hz,hp] at hv
  have hs : (Real.sqrt 30 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (show (0 : ℝ) < 30 by norm_num))
  exact (mul_ne_zero (by norm_num) hs) hv.symm

end LowEnergy.ActualFourBlockElastic
