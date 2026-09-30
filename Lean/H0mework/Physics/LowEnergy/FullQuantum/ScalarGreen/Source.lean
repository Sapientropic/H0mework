import H0mework.Physics.LowEnergy.FullQuantum.ScalarGreen.Inverse
import H0mework.Physics.LowEnergy.FullQuantum.PerturbedGreen.Local

/-! The all-amplitude inverse belongs to the same arbitrary spatial scalar field in the original action. -/
set_option autoImplicit false
open MeasureTheory
open scoped SchwartzMap InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ScalarGreen
open FullSpace SpatialGreen YangMills.FullPairing ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair StageNineDynamicBreakingVacuum
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineDiracDualYukawaSpinJurisdiction StageNineDiracDualFormNativeConjugateMatterVariation
open DiracExteriorMatterAction SU7MotherLieAlgebra SU7MotherGaugeTheory
noncomputable section
attribute [local irreducible] green SpatialWeak.adjointDifferential

def scalarField (profile : ScalarProfile) : BasePoint → ScalarCoordinateCarrier :=
  fun point => profile (PerturbedGreen.spatialPart point)

theorem scalar_insertion_native (profile : ScalarProfile) (x : Position) :
    PerturbedGreen.insertion actual (fun _ => 0) (scalarField profile) (PerturbedGreen.spatialPoint x)=
      diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (profile x)) := by
  apply LinearMap.ext
  intro v
  simp [PerturbedGreen.insertion,YangMills.Response.Forcing.spatialInsertion,
    p286GaugeConnectionMotherVariation,scalarField,PerturbedGreen.spatialPart_point,
    diracExteriorMotherLieAction_zero_matrix]

theorem native_kernel_ae (profile : ScalarProfile) (epsilon : ℝ) (momentum : Fin 3 → ℝ)
    (z : ℂ) (field : FullMatterL2) :
    (fun x => operator (Triangular.diracKernel
      (PerturbedGreen.varied actual (fun _ => 0) (scalarField profile) epsilon)
      (PerturbedGreen.spatialPoint x) momentum z) (field x))=ᵐ[volume]
      fun x => operator (Triangular.diracKernel actual 0 momentum z) (field x)+(epsilon : ℂ) • potential profile field x := by
  filter_upwards [potential_ae profile field] with x insertion
  rw [PerturbedGreen.varied_diracKernel,scalar_insertion_native,Triangular.operator_add,
    Triangular.operator_smul,PerturbedGreen.actual_kernel_constant,insertion]
  rfl

theorem scalar_response_weak (energy damping : ℝ) (positive : 0<damping) (profile : ScalarProfile)
    (epsilon : ℝ) (source : FullMatterL2) (test : 𝓢(Position,Hilbert)) :
    inner ℂ ((SpatialWeak.adjointDifferential 0 energy damping test).toLp 2 volume)
      (response 0 energy damping positive profile (epsilon : ℂ) source)+
      (epsilon : ℂ)*inner ℂ (test.toLp 2 volume)
        (potential profile (response 0 energy damping positive profile (epsilon : ℂ) source))=
      inner ℂ (test.toLp 2 volume) source := by
  have solved := response_solves 0 energy damping positive profile (epsilon : ℂ) source
  have weak := SpatialWeak.equation_weak 0 energy damping _ _ solved test
  rw [inner_sub_right,inner_smul_right] at weak
  exact eq_sub_iff_add_eq.mp weak

theorem scalar_response_original_weak (energy damping : ℝ) (positive : 0<damping) (profile : ScalarProfile)
    (epsilon : ℝ) (source : FullMatterL2) (test : 𝓢(Position,Hilbert)) :
    let field := response 0 energy damping positive profile (epsilon : ℂ) source
    (∫ x, inner ℂ ((SpatialWeak.constant 0 energy damping).adjoint (test x)+Complex.I •
      ∑ j, (SpatialWeak.spatial 0 j).adjoint (fderiv ℝ test x (SpatialWeak.direction j))) (field x))+
      (epsilon : ℂ)*(∫ x, inner ℂ (test x)
        (operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (profile x))) (field x)))=
      ∫ x, inner ℂ (test x) (source x) := by
  dsimp only
  have weak := scalar_response_weak energy damping positive profile epsilon source test
  rw [L2.inner_def,L2.inner_def,L2.inner_def] at weak
  convert weak using 1
  · congr 1
    · apply integral_congr_ae
      filter_upwards [(SpatialWeak.adjointDifferential 0 energy damping test).coeFn_toLp 2 volume] with x read
      rw [read,SpatialWeak.adjointDifferential,SpatialWeak.firstOrder_apply]
    · congr 1
      apply integral_congr_ae
      filter_upwards [test.coeFn_toLp 2 volume,
        potential_ae profile (response 0 energy damping positive profile (epsilon : ℂ) source)] with x read insertion
      rw [read,insertion]
  · apply integral_congr_ae
    filter_upwards [test.coeFn_toLp 2 volume] with x read
    rw [read]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ScalarGreen
