import H0mework.Physics.SpinPair.Actual

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open Stage9C.Reduction
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

theorem phaseCoefficients_smooth :
    ContDiff ℝ ∞ (fun point => spinPairCoefficients (upperPhase point) (lowerPhase point)) := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;>
    simp only [spinPairCoefficients]
  all_goals first
    | exact phase_smooth _
    | exact (phase_smooth _).neg
    | exact contDiff_const

theorem seed_matter_smooth :
    ContDiff ℝ ∞ (fun point => matterCoordinateEquiv (seed.matter point)) := by
  let linear := (sourceColorMatterCoordinateLinear.restrictScalars ℝ).toContinuousLinearMap
  exact linear.contDiff.comp phaseCoefficients_smooth

theorem seed_conjugateMatter_smooth (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ (fun point => seed.conjugateMatter point
      (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))) := by
  have upper : ContDiff ℝ ∞ upperDualPhase := contDiff_const.mul (phase_smooth frequency)
  have lower : ContDiff ℝ ∞ lowerDualPhase := contDiff_const.mul (phase_smooth (-frequency))
  change ContDiff ℝ ∞ (fun point => ∑ spin, ∑ state,
    spinPairCoefficients (upperDualPhase point) (lowerDualPhase point) spin state *
      sourceColorDoubletDual state
        (matterCoordinateEquiv.symm (EuclideanSpace.single index 1) spin))
  simp only [Fin.sum_univ_four, Fin.sum_univ_two, spinPairCoefficients,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zero_mul, zero_add, add_zero]
  fun_prop

theorem seed_smooth : seed.Smooth := by
  obtain ⟨_, oldConnection, oldGravityAuxiliary, oldMultiplier, _, oldGaugeAuxiliary, _, _, _⟩ :=
    firstAssemblyCartanActual_smooth
  have gauge (direction : LorentzianIndex) : ContDiff ℝ ∞
      (fun _ : BasePoint => p286CoordinateEquiv (gaugePotential gaugeScale direction)) :=
    contDiff_const
  refine ⟨fun _ _ => contDiff_const, oldConnection, oldGravityAuxiliary, oldMultiplier,
    gauge, oldGaugeAuxiliary, contDiff_const, seed_matter_smooth,
    seed_conjugateMatter_smooth⟩

theorem actual_smooth : actual.Smooth :=
  algebraicCartanReduction_smooth positiveSmoothUnifiedSource seed seed_smooth seed_nondegenerate

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
