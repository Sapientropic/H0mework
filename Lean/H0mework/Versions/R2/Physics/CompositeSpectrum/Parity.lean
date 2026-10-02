import H0mework.Versions.R2.Physics.CompositeSpectrum.Naturality

/-! Spatial inversion is derived from the actual Clifford matrices and the
pullback of the primitive one-form. Both spatial legs of magnetic curvature
change sign, so this magnetic cubic is parity even. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF
open StageNineSpinMatterBundle
open SU7ExteriorBreakingYukawa
open scoped Kronecker

noncomputable section

def paritySign (direction : LorentzianIndex) : ℝ := if direction = 0 then 1 else -1

def parityPoint (point : BasePoint) : BasePoint :=
  WithLp.toLp 2 (fun direction => paritySign direction * point direction)

theorem parityPoint_involutive (point : BasePoint) : parityPoint (parityPoint point) = point := by
  ext direction
  by_cases zero : direction = 0 <;> simp [parityPoint, paritySign, zero]

theorem parityPoint_time (point : BasePoint) : parityPoint point 0 = point 0 := by
  simp [parityPoint, paritySign]

def parityMatrix : DiracMatrix := Complex.I • diracGammaZero

theorem parityMatrix_square : parityMatrix * parityMatrix = 1 := by
  rw [parityMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two, Complex.I_sq, diracGammaZero_sq]
  simp

theorem parityMatrix_clifford (direction : LorentzianIndex) :
    parityMatrix * diracGamma direction * parityMatrix =
      (paritySign direction : ℂ) • diracGamma direction := by
  ext row column
  fin_cases direction <;> fin_cases row <;> fin_cases column <;>
    norm_num [parityMatrix, paritySign, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod] <;> ring_nf <;> simp

def occupiedParity : State.Observable := parityMatrix ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem phaseHamiltonian_chirality : phaseHamiltonian =
    (frequency : ℂ) • (diracGammaFive ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  ext ⟨spin, color⟩ ⟨other, input⟩
  fin_cases spin <;> fin_cases other <;>
    simp [phaseHamiltonian, Dynamics.rate, diracGammaFive, Matrix.diagonal_apply, Matrix.one_apply,
      Prod.mk.injEq, Matrix.kroneckerMap_apply]

theorem occupiedParity_square : occupiedParity * occupiedParity = 1 := by
  rw [occupiedParity, ← Matrix.mul_kronecker_mul, parityMatrix_square,
    Matrix.one_mul, Matrix.one_kronecker_one]

theorem phaseHamiltonian_parity : occupiedParity * phaseHamiltonian * occupiedParity = -phaseHamiltonian := by
  have chirality : parityMatrix * diracGammaFive * parityMatrix = -diracGammaFive := by
    have anti : diracGammaZero * diracGammaFive = -(diracGammaFive * diracGammaZero) := by
      have relation := diracGammaFive_anticommutes 0
      change diracGammaFive * diracGammaZero + diracGammaZero * diracGammaFive = 0 at relation
      exact eq_neg_of_add_eq_zero_right relation
    simp only [parityMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← pow_two, Complex.I_sq, anti, Matrix.neg_mul, Matrix.mul_assoc, diracGammaZero_sq]
    simp
  rw [phaseHamiltonian_chirality, occupiedParity, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, chirality]
  ext row column
  simp [Matrix.kroneckerMap_apply]

theorem groundProjector_parity :
    occupiedParity * groundProjector * occupiedParity = 1 - groundProjector := by
  rw [groundProjector, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, occupiedParity_square, Matrix.mul_smul, Matrix.smul_mul, phaseHamiltonian_parity]
  module

theorem parityMatter_square (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction parityMatrix (diracMatrixMatterAction parityMatrix matter) = matter := by
  have product := LinearMap.congr_fun (diracMatrixMatterAction_mul parityMatrix parityMatrix) matter
  simp only [LinearMap.comp_apply] at product
  rw [← product, parityMatrix_square]
  funext spin
  simp [diracMatrixMatterAction, Matrix.one_apply]

def parityFrame : Source.Frame.Action where
  toLinearMap := diracMatrixMatterAction parityMatrix
  invFun := diracMatrixMatterAction parityMatrix
  left_inv := parityMatter_square
  right_inv := parityMatter_square

def parityGaugePullback : StageNineHolonomicConfiguration :=
  { Runtime.configuration with
    gaugeConnection := fun point direction =>
      paritySign direction • Runtime.configuration.gaugeConnection (parityPoint point) direction }

theorem parityGaugePullback_connection :
    parityGaugePullback.gaugeConnection = fun _ => gaugePotential (-gaugeScale) := by
  funext point direction
  simp only [parityGaugePullback, Runtime.configuration_eq, actual_gaugeConnection]
  fin_cases direction <;> simp [paritySign, gaugePotential, smul_smul]

theorem parityGaugePullback_curvature (point : BasePoint) :
    holonomicGaugeCurvature parityGaugePullback point =
      holonomicGaugeCurvature Runtime.configuration point := by
  rw [constantGauge_curvature parityGaugePullback (-gaugeScale) parityGaugePullback_connection point,
    Runtime.configuration_eq, actual_gaugeCurvature]
  simp [magneticCurvature]

def parityCompositeAction (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  alternatingProduct (fun axis => Complex.I • diracExteriorMotherLieAction
    (SU7MotherLieAlgebra.p286LieBlockEmbed
      (holonomicGaugeCurvature parityGaugePullback point (magneticPair axis))))

theorem parityCompositeAction_eq (point : BasePoint) : parityCompositeAction point = compositeAction point := by
  unfold parityCompositeAction compositeAction incomingCurvatureAction
  rw [parityGaugePullback_curvature]

theorem incomingCurvatureAction_parity (point : BasePoint) (axis : Fin 3)
    (matter : DiracExteriorMatterCarrier) :
    incomingCurvatureAction point axis (parityFrame matter) =
      parityFrame (incomingCurvatureAction point axis matter) := by
  change Complex.I • internalMatterLinearAction _ (diracMatrixMatterAction parityMatrix matter) =
    diracMatrixMatterAction parityMatrix (Complex.I • internalMatterLinearAction _ matter)
  rw [map_smul]
  congr 1
  exact (LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal parityMatrix
    (exteriorSpinorMotherLieAction (SU7MotherLieAlgebra.p286LieBlockEmbed
      (holonomicGaugeCurvature Runtime.configuration point (magneticPair axis))))) matter).symm

theorem compositeAction_parity (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    parityCompositeAction point (parityFrame matter) = parityFrame (compositeAction point matter) := by
  rw [parityCompositeAction_eq]
  exact alternatingProduct_intertwines _ _ parityFrame (incomingCurvatureAction_parity point) matter

theorem compositeAction_parity_dual (point : BasePoint) (matter : DiracExteriorMatterCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (dual.comp parityFrame.symm.toLinearMap)
      (parityCompositeAction point (parityFrame matter)) = dual (compositeAction point matter) := by
  rw [compositeAction_parity]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem actual_compositeAction_parity_even (point : BasePoint) :
    ((Runtime.configuration.conjugateMatter point).comp parityFrame.symm.toLinearMap)
      (parityCompositeAction point (parityFrame (Runtime.configuration.matter point))) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Runtime.tick.answer point) (cubic point) := by
  rw [compositeAction_parity_dual, compositeAction_quantum_response]

theorem source_matter_parityPoint (point : BasePoint) :
    Runtime.configuration.matter (parityPoint point) = Runtime.configuration.matter point := by
  simp [Runtime.configuration_eq, actual_matter, upperPhase, lowerPhase, phase, parityPoint_time]

theorem source_dual_parityPoint (point : BasePoint) :
    Runtime.configuration.conjugateMatter (parityPoint point) = Runtime.configuration.conjugateMatter point := by
  simp [Runtime.configuration_eq, actual_conjugateMatter,
    upperDualPhase, lowerDualPhase, upperPhase, lowerPhase, phase, parityPoint_time]

theorem actual_compositeAction_parity_pullback (point : BasePoint) :
    ((Runtime.configuration.conjugateMatter (parityPoint point)).comp parityFrame.symm.toLinearMap)
      (parityCompositeAction point
        (parityFrame (Runtime.configuration.matter (parityPoint point)))) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Runtime.tick.answer point) (cubic point) := by
  rw [source_matter_parityPoint, source_dual_parityPoint, actual_compositeAction_parity_even]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
