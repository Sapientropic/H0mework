import H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading
import H0mework.Physics.LowEnergy.FullQuantum.TriangularDirac

/-! Source resolvents and original action insertions supply every grading law. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops
open DiracExteriorMatterAction DiracCliffordRepresentation SU7MotherLieAlgebra
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineCurrentCoframeMatterTemporalPrincipal SU7ExteriorBreakingYukawa
open StageNineDiracDualYukawaSpinJurisdiction StageNineDynamicBreakingVacuum
noncomputable section

theorem source_hamiltonian (C : StageNineHolonomicConfiguration) (p : BasePoint) (k : Fin 3 → ℝ) :
    Expansion (hamiltonian C p k) (Triangular.freeHamiltonian C p k) := by
  have difference : hamiltonian C p k-Triangular.freeHamiltonian C p k=Triangular.interactionHamiltonian C p := by
    rw [Triangular.hamiltonian_split]
    convert! add_sub_cancel_left (Triangular.freeHamiltonian C p k) (Triangular.interactionHamiltonian C p) using 1
  refine ⟨Triangular.grade_freeHamiltonian 0 C p k,?_⟩
  rw [difference]
  exact ⟨Triangular.six_interactionHamiltonian C p,Triangular.interactionHamiltonian_six C p⟩

theorem source_variation (first second : StageNineHolonomicConfiguration)
    (p q : BasePoint) (k l : Fin 3 → ℝ) :
    Expansion (hamiltonian first p k-hamiltonian second q l)
      (Triangular.freeHamiltonian first p k-Triangular.freeHamiltonian second q l) :=
  (source_hamiltonian first p k).sub (source_hamiltonian second q l)

theorem source_resolvent (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) (regular : IsUnit (Triangular.freeKernel C p k z)) :
    Expansion (Triangular.fullResolvent C p k z) (Triangular.freeResolvent C p k z) := by
  have free := Triangular.grade_freeResolvent 0 C p k z regular
  have correction : Arrow
      (Triangular.freeResolvent C p k z*Triangular.interactionHamiltonian C p*Triangular.freeResolvent C p k z) :=
    Arrow.diagonal_right (Arrow.diagonal_left free
      ⟨Triangular.six_interactionHamiltonian C p,Triangular.interactionHamiltonian_six C p⟩) free
  refine ⟨free,?_⟩
  have difference : Triangular.fullResolvent C p k z-Triangular.freeResolvent C p k z=
      Triangular.freeResolvent C p k z*Triangular.interactionHamiltonian C p*Triangular.freeResolvent C p k z := by
    unfold Triangular.fullResolvent
    convert! add_sub_cancel_left (Triangular.freeResolvent C p k z)
      (Triangular.freeResolvent C p k z*Triangular.interactionHamiltonian C p*Triangular.freeResolvent C p k z) using 1
  rw [difference]
  exact correction

theorem original_gauge_vertex (coframe : LorentzianCoframe) (mu : LorentzianIndex)
    (data : P286LieBlockData) :
    Expansion (Exchange.currentOperator coframe mu data) (Exchange.currentOperator coframe mu data) := by
  have spin : Commute six (diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := coframe, derivative := 0 } mu)) := MixedSymbol.degreeSix_spin _
  have gauge : Commute six (diracExteriorMotherLieAction (p286LieBlockEmbed data)) := MixedSymbol.degreeSix_gauge _
  exact Expansion.refl _ ((spin.mul_right gauge).smul_right Complex.I)

theorem original_scalar_vertex (scalar : ScalarCoordinateCarrier) :
    Arrow (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm scalar)) :=
  ⟨MixedSymbol.yukawa_output _,MixedSymbol.yukawa_degreeSix _⟩

theorem original_principal_inverse (C : StageNineHolonomicConfiguration) (p : BasePoint) :
    Expansion (currentCoframeMatterTemporalPrincipalInverse (C.coframe p))
      (currentCoframeMatterTemporalPrincipalInverse (C.coframe p)) :=
  Expansion.refl _ (Triangular.grade_principal_inverse 0 C p)

def freeDiracResolvent (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) : Mother :=
  Complex.I • (Triangular.freeResolvent C p k z*currentCoframeMatterTemporalPrincipalInverse (C.coframe p))

theorem source_diracResolvent (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) (regular : IsUnit (Triangular.freeKernel C p k z)) :
    Expansion (Triangular.diracResolvent C p k z) (freeDiracResolvent C p k z) :=
  ((source_resolvent C p k z regular).mul (original_principal_inverse C p)).smul Complex.I

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops
