import H0mework.Physics.LowEnergyFermion.Hermitian
import H0mework.Versions.AB.Physics.LowEnergyQuantum.Preparation
import H0mework.Versions.AB.Physics.LowEnergyExchange.Current

/-! The full native 252-mode source enters the two-particle CAR consumer. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineFullDiracAdjointMaterial
open ProofFreeRicherAnholonomicSource SU7MotherLieAlgebra StageNineDynamicBreakingVacuum
open StageNineDiracDualYukawaSpinJurisdiction
open scoped BigOperators Matrix
noncomputable section

abbrev fullIndexOrder : LinearOrder Quantum.Index :=
  LinearOrder.lift' (Fintype.equivFin Quantum.Index) (Fintype.equivFin Quantum.Index).injective

attribute [local instance] fullIndexOrder

def sourcePair (u v : DiracExteriorMatterCarrier) : Fock Quantum.Index :=
  twoParticle (Quantum.coordinates u) (Quantum.coordinates v)

def sourceNormal (A B : Module.End ℂ DiracExteriorMatterCarrier) : Module.End ℂ (Fock Quantum.Index) :=
  normalProduct (Quantum.operatorMatrix A) (Quantum.operatorMatrix B)

theorem full_source_normal_order (A B : Module.End ℂ DiracExteriorMatterCarrier) (ψ : Fock Quantum.Index) :
    secondQuantize (Quantum.operatorMatrix A) (secondQuantize (Quantum.operatorMatrix B) ψ) =
      secondQuantize (Quantum.operatorMatrix (A.comp B)) ψ + sourceNormal A B ψ := by
  rw [Quantum.matrix_composition]
  exact original_secondQuantize_normal_order _ _ ψ

theorem source_normal_matrixElement (A B : Module.End ℂ DiracExteriorMatterCarrier)
    (x y u v : DiracExteriorMatterCarrier) :
    pairing (sourcePair x y) (sourceNormal A B (sourcePair u v)) =
      (Quantum.coordinatePair x (A u)*Quantum.coordinatePair y (B v) -
        Quantum.coordinatePair x (B v)*Quantum.coordinatePair y (A u)) -
      (Quantum.coordinatePair x (A v)*Quantum.coordinatePair y (B u) -
        Quantum.coordinatePair x (B u)*Quantum.coordinatePair y (A v)) := by
  unfold sourcePair sourceNormal
  rw [normalProduct_matrixElement]
  simp only [Quantum.matrix_action, modePair, Quantum.coordinatePair]

theorem canonical_source_matrixElement (A B : Module.End ℂ DiracExteriorMatterCarrier)
    (x y u v : DiracExteriorMatterCarrier) :
    pairing (sourcePair (Quantum.spinExchange x) (Quantum.spinExchange y))
      (sourceNormal A B (sourcePair u v)) =
      (fullCanonicalDiracAdjoint x (A u)*fullCanonicalDiracAdjoint y (B v) -
        fullCanonicalDiracAdjoint x (B v)*fullCanonicalDiracAdjoint y (A u)) -
      (fullCanonicalDiracAdjoint x (A v)*fullCanonicalDiracAdjoint y (B u) -
        fullCanonicalDiracAdjoint x (B u)*fullCanonicalDiracAdjoint y (A v)) := by
  rw [source_normal_matrixElement]
  simp only [Quantum.canonicalDual_full_response]

def realVertex (density : ℝ) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    Matrix Quantum.Index Quantum.Index ℂ :=
  (density : ℂ) • hermitianPart (Quantum.operatorMatrix (Quantum.spinExchange.comp action))

theorem realVertex_adjoint (density : ℝ) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    (realVertex density action).conjTranspose = realVertex density action := by
  simp [realVertex, Matrix.conjTranspose_smul, hermitianPart_adjoint]

theorem realVertex_response (density : ℝ) (action : Module.End ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier) :
    modePair (Quantum.coordinates matter) (realVertex density action *ᵥ Quantum.coordinates matter) =
      ((density*(fullCanonicalDiracAdjoint matter (action matter)).re : ℝ) : ℂ) := by
  rw [realVertex, Matrix.smul_mulVec, modePair_smul_right, hermitianPart_self,
    Quantum.matrix_action]
  have identity : modePair (Quantum.coordinates matter)
      (Quantum.coordinates (Quantum.spinExchange (action matter))) =
      fullCanonicalDiracAdjoint matter (action matter) := by
    rw [Quantum.canonicalDual_full_response, Quantum.spinExchange_selfAdjoint]
    rfl
  change (density : ℂ)*(modePair (Quantum.coordinates matter)
    (Quantum.coordinates (Quantum.spinExchange (action matter)))).re = _
  rw [identity]
  push_cast
  rfl

def currentVertex (coframe : LorentzianCoframe) (density : ℝ) (mu : LorentzianIndex)
    (data : P286LieBlockData) : Matrix Quantum.Index Quantum.Index ℂ :=
  ((|coframe.det| : ℝ) : ℂ) • realVertex density (Exchange.currentOperator coframe mu data)

def scalarVertex (coframe : LorentzianCoframe) (density : ℝ) (direction : ScalarCoordinateCarrier) :
    Matrix Quantum.Index Quantum.Index ℂ :=
  ((|coframe.det| : ℝ) : ℂ) • realVertex density
    (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm direction))

theorem original_real_current (coframe : LorentzianCoframe) (density : ℝ)
    (mu : LorentzianIndex) (data : P286LieBlockData) (matter : DiracExteriorMatterCarrier) :
    pairing (oneParticle (Quantum.coordinates matter))
      (secondQuantize (currentVertex coframe density mu data) (oneParticle (Quantum.coordinates matter))) =
      (Exchange.current coframe matter ((density : ℂ) • fullCanonicalDiracAdjoint matter) mu data : ℂ) := by
  rw [pairing_secondQuantize_oneParticle (currentVertex coframe density mu data)
    (Quantum.coordinates matter) (Quantum.coordinates matter)]
  change modePair (Quantum.coordinates matter)
    (currentVertex coframe density mu data *ᵥ Quantum.coordinates matter) = _
  rw [currentVertex, Matrix.smul_mulVec, modePair_smul_right, realVertex_response]
  simp [Exchange.current, LinearMap.smul_apply, Complex.mul_re]

theorem original_real_scalar_source (coframe : LorentzianCoframe) (density : ℝ)
    (direction : ScalarCoordinateCarrier) (matter : DiracExteriorMatterCarrier) :
    pairing (oneParticle (Quantum.coordinates matter))
      (secondQuantize (scalarVertex coframe density direction) (oneParticle (Quantum.coordinates matter))) =
      (Exchange.yukawaSource coframe matter ((density : ℂ) • fullCanonicalDiracAdjoint matter) direction : ℂ) := by
  rw [pairing_secondQuantize_oneParticle (scalarVertex coframe density direction)
    (Quantum.coordinates matter) (Quantum.coordinates matter)]
  change modePair (Quantum.coordinates matter)
    (scalarVertex coframe density direction *ᵥ Quantum.coordinates matter) = _
  rw [scalarVertex, Matrix.smul_mulVec, modePair_smul_right, realVertex_response]
  simp [Exchange.yukawaSource, LinearMap.smul_apply, Complex.mul_re]

theorem original_current_scalar_fourFermion (coframe : LorentzianCoframe)
    (density firstDensity : ℝ) (mu : LorentzianIndex) (data : P286LieBlockData)
    (direction : ScalarCoordinateCarrier) (i k j l : Quantum.Index) :
    let A := currentVertex coframe density mu data
    let B := scalarVertex coframe firstDensity direction
    pairing (twoParticle (Pi.single i 1) (Pi.single k 1))
      (normalProduct A B (twoParticle (Pi.single j 1) (Pi.single l 1))) =
      (A i j*B k l-B i l*A k j)-(A i l*B k j-B i j*A k l) :=
  occupied_normal_matrixElement _ _ i k j l

theorem sourcePair_prepared (firstAmplitude secondAmplitude firstAngle secondAngle : ℝ) :
    sourcePair (Quantum.preparedSpinor firstAmplitude firstAngle)
      (Quantum.preparedSpinor secondAmplitude secondAngle) =
      ((4*firstAmplitude*secondAmplitude : ℝ) : ℂ) •
        sourcePair (Quantum.preparedSpinor (1/2) firstAngle) (Quantum.preparedSpinor (1/2) secondAngle) := by
  rw [Quantum.prepared_normalization firstAmplitude firstAngle,
    Quantum.prepared_normalization secondAmplitude secondAngle]
  unfold sourcePair
  rw [map_smul, map_smul, twoParticle_smul]
  congr 1
  push_cast
  ring

theorem prepared_normal_response (A B : Matrix Quantum.Index Quantum.Index ℂ)
    (firstAmplitude secondAmplitude firstAngle secondAngle : ℝ) :
    let prepared := sourcePair (Quantum.preparedSpinor firstAmplitude firstAngle)
      (Quantum.preparedSpinor secondAmplitude secondAngle)
    let unit := sourcePair (Quantum.preparedSpinor (1/2) firstAngle) (Quantum.preparedSpinor (1/2) secondAngle)
    pairing prepared (normalProduct A B prepared) =
      ((16*firstAmplitude^2*secondAmplitude^2 : ℝ) : ℂ) * pairing unit (normalProduct A B unit) := by
  dsimp
  rw [sourcePair_prepared, map_smul, pairing_smul_left, pairing_smul_right]
  have conjugate : star ((4*firstAmplitude*secondAmplitude : ℝ) : ℂ) =
      ((4*firstAmplitude*secondAmplitude : ℝ) : ℂ) := by simp
  rw [conjugate]
  push_cast
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
