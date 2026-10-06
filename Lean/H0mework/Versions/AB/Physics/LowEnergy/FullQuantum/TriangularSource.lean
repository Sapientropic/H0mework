import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Evolution
import Mathlib.Algebra.Ring.Commute

/-! The original spin/gauge coefficients preserve all three exterior grades.
The only off-diagonal arrow is the source's degree-two to degree-six Yukawa. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
open DiracExteriorMatterAction DiracCliffordRepresentation
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDiracDualYukawaSpinJurisdiction StageNineDynamicBreakingVacuum
open StageNineCurrentCoframeMatterTemporalPrincipal SU7MotherLieAlgebra
open SU7ExteriorBreakingYukawa YangMills.FullPairing
noncomputable section

def grade (d : Fin 3) : Mother :=
  ![MixedSymbol.degreeSix, MixedSymbol.degreeTwo, MixedSymbol.degreeFour] d

theorem grade_spin (d : Fin 3) (M : DiracMatrix) :
    Commute (grade d) (diracMatrixMatterAction M) := by
  fin_cases d
  · exact MixedSymbol.degreeSix_spin M
  · exact MixedSymbol.degreeTwo_spin M
  · exact MixedSymbol.degreeFour_spin M

theorem grade_gauge (d : Fin 3) (M : SU7MotherLieMatrix) :
    Commute (grade d) (diracExteriorMotherLieAction M) := by
  fin_cases d
  · exact MixedSymbol.degreeSix_gauge M
  · exact MixedSymbol.degreeTwo_gauge M
  · exact MixedSymbol.degreeFour_gauge M

theorem grade_connection (d : Fin 3) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) (mu : LorentzianIndex) : Commute (grade d) (connection C p mu) :=
  (grade_spin d _).add_right (grade_gauge d _)

theorem grade_principal (d : Fin 3) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) :
    Commute (grade d) (currentCoframeMatterTemporalPrincipal (C.coframe p)) :=
  (grade_spin d _).smul_right Complex.I

theorem grade_principal_inverse (d : Fin 3) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) :
    Commute (grade d) (currentCoframeMatterTemporalPrincipalInverse (C.coframe p)) :=
  (grade_principal d C p).smul_right _

def freeKnown (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : Mother :=
  Complex.I • ∑ j : Fin 3,
    (diracMatrixMatterAction (inverseCoframeDiracGamma
      { coframe := C.coframe p, derivative := 0 } j.succ)).comp
      ((Complex.I * (k j : ℂ)) • (1 : Mother) + connection C p j.succ)

def freeDrift (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : Mother :=
  -currentCoframeMatterTemporalPrincipalInverse (C.coframe p) * freeKnown C p k -
    connection C p 0

def interaction (C : StageNineHolonomicConfiguration) (p : BasePoint) : Mother :=
  -currentCoframeMatterTemporalPrincipalInverse (C.coframe p) *
    diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (C.scalar p))

def freeHamiltonian (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : Mother := Complex.I • freeDrift C p k

def interactionHamiltonian (C : StageNineHolonomicConfiguration) (p : BasePoint) : Mother :=
  Complex.I • interaction C p

theorem free_hamiltonian_drift (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : (-Complex.I) • freeHamiltonian C p k = freeDrift C p k := by
  simp [freeHamiltonian, smul_smul]

theorem interaction_hamiltonian_drift (C : StageNineHolonomicConfiguration) (p : BasePoint) :
    (-Complex.I) • interactionHamiltonian C p = interaction C p := by
  simp [interactionHamiltonian, smul_smul]

theorem source_split (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : drift C p k = freeDrift C p k + interaction C p := by
  change -currentCoframeMatterTemporalPrincipalInverse (C.coframe p) *
    (freeKnown C p k + diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (C.scalar p))) - connection C p 0 = _
  unfold freeDrift interaction
  noncomm_ring

theorem hamiltonian_split (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) :
    hamiltonian C p k = freeHamiltonian C p k + interactionHamiltonian C p := by
  rw [hamiltonian, source_split, smul_add]
  rfl

theorem grade_freeKnown (d : Fin 3) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) (k : Fin 3 → ℝ) : Commute (grade d) (freeKnown C p k) := by
  apply Commute.smul_right
  apply Commute.sum_right
  intro j _
  exact (grade_spin d _).mul_right
    (((Commute.one_right (grade d)).smul_right _).add_right (grade_connection d C p j.succ))

theorem grade_freeDrift (d : Fin 3) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) (k : Fin 3 → ℝ) : Commute (grade d) (freeDrift C p k) := by
  change grade d * freeDrift C p k = freeDrift C p k * grade d
  apply LinearMap.ext
  intro v
  have temporal (w : DiracExteriorMatterCarrier) :
      grade d (currentCoframeMatterTemporalPrincipalInverse (C.coframe p) w) =
        currentCoframeMatterTemporalPrincipalInverse (C.coframe p) (grade d w) :=
    LinearMap.congr_fun (grade_principal_inverse d C p).eq w
  have spatial := LinearMap.congr_fun (grade_freeKnown d C p k).eq v
  have connection := LinearMap.congr_fun (grade_connection d C p 0).eq v
  simp only [Module.End.mul_apply] at spatial connection
  change grade d (-currentCoframeMatterTemporalPrincipalInverse (C.coframe p)
    (freeKnown C p k v) - FullQuantum.connection C p 0 v) =
      -currentCoframeMatterTemporalPrincipalInverse (C.coframe p) (freeKnown C p k (grade d v)) -
        FullQuantum.connection C p 0 (grade d v)
  rw [map_sub, map_neg, temporal, spatial, connection]

theorem grade_freeHamiltonian (d : Fin 3) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) (k : Fin 3 → ℝ) : Commute (grade d) (freeHamiltonian C p k) :=
  (grade_freeDrift d C p k).smul_right Complex.I

theorem six_interaction (C : StageNineHolonomicConfiguration) (p : BasePoint) :
    MixedSymbol.degreeSix * interaction C p = interaction C p := by
  apply LinearMap.ext
  intro v
  have temporal (w : DiracExteriorMatterCarrier) :
      MixedSymbol.degreeSix (currentCoframeMatterTemporalPrincipalInverse (C.coframe p) w) =
        currentCoframeMatterTemporalPrincipalInverse (C.coframe p) (MixedSymbol.degreeSix w) :=
    LinearMap.congr_fun (grade_principal_inverse 0 C p).eq w
  have output := LinearMap.congr_fun
    (MixedSymbol.yukawa_output (scalarCoordinateEquiv.symm (C.scalar p))) v
  simp only [LinearMap.comp_apply] at output
  change MixedSymbol.degreeSix (-currentCoframeMatterTemporalPrincipalInverse (C.coframe p)
    (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (C.scalar p)) v)) =
      -currentCoframeMatterTemporalPrincipalInverse (C.coframe p)
        (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (C.scalar p)) v)
  rw [map_neg, temporal, output]

theorem interaction_six (C : StageNineHolonomicConfiguration) (p : BasePoint) :
    interaction C p * MixedSymbol.degreeSix = 0 := by
  unfold interaction
  rw [mul_assoc]
  have input : diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (C.scalar p)) *
      MixedSymbol.degreeSix = 0 := MixedSymbol.yukawa_degreeSix _
  rw [input, mul_zero]

theorem six_interactionHamiltonian (C : StageNineHolonomicConfiguration) (p : BasePoint) :
    MixedSymbol.degreeSix * interactionHamiltonian C p = interactionHamiltonian C p := by
  rw [interactionHamiltonian, mul_smul_comm, six_interaction]

theorem interactionHamiltonian_six (C : StageNineHolonomicConfiguration) (p : BasePoint) :
    interactionHamiltonian C p * MixedSymbol.degreeSix = 0 := by
  rw [interactionHamiltonian, smul_mul_assoc, interaction_six, smul_zero]

theorem source_insertions (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (R : Mother) (preserves : Commute MixedSymbol.degreeSix R) :
    interactionHamiltonian C p * R * interactionHamiltonian C p = 0 := by
  calc
    _ = interactionHamiltonian C p * R *
        (MixedSymbol.degreeSix * interactionHamiltonian C p) := by rw [six_interactionHamiltonian]
    _ = (interactionHamiltonian C p * MixedSymbol.degreeSix) * R * interactionHamiltonian C p := by
      calc
        _ = interactionHamiltonian C p * (R * MixedSymbol.degreeSix) * interactionHamiltonian C p := by noncomm_ring
        _ = interactionHamiltonian C p * (MixedSymbol.degreeSix * R) * interactionHamiltonian C p := by rw [preserves.eq]
        _ = _ := by noncomm_ring
    _ = 0 := by rw [interactionHamiltonian_six, zero_mul, zero_mul]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
