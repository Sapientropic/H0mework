import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Domain
import H0mework.Physics.LowEnergy.FullQuantum.ScalarGreen.Source

/-! All bounded native gauge components and all 35 scalar coordinates return to the same primitive action. -/
set_option autoImplicit false
open MeasureTheory
open scoped SchwartzMap InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open DiracExteriorMatterAction Triangular StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction ScalarGreen
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineHolonomicField SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineDiracDualFormNativeConjugateMatterVariation
noncomputable section

private theorem yukawa_zero : diracDualRightChiralYukawaAction 0=0 := by
  simpa only [zero_smul] using diracDualRightChiralYukawaAction_smul (0 : ℂ) 0

def gaugeField (profile : GaugeProfile) : BasePoint → P286GaugeOneForm :=
  fun point => profile (PerturbedGreen.spatialPart point)

def configuration (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) : StageNineHolonomicConfiguration :=
  { varyP286GaugeConnectionCoordinate actual (gaugeField gauge) parameter with scalar := scalarField scalar }

theorem rawGauge_mother (gauge : P286GaugeOneForm) :
    Complex.I • (currentCoframeMatterTemporalPrincipal (actual.coframe 0)*gaugeMotherLinear gauge)=
      PerturbedGreen.insertion actual (fun _ => gauge) (fun _ => 0) 0 := by
  apply LinearMap.ext
  intro v
  simp only [gaugeMotherLinear,LinearMap.coe_mk,AddHom.coe_mk,YangMills.Response.Forcing.insertion,
    PerturbedGreen.insertion,Module.End.mul_apply,LinearMap.smul_apply,LinearMap.sub_apply,
    LinearMap.neg_apply,LinearMap.comp_apply,LinearMap.add_apply,map_smul,map_sub,map_neg,
    currentCoframeMatterTemporalPrincipalInverse_right _ (actual_noncharacteristic 0),
    map_zero,yukawa_zero,add_zero,smul_smul,Complex.I_mul_I]
  module

theorem gauge_insertion_native (profile : GaugeProfile) (x : Position) :
    PerturbedGreen.insertion actual (gaugeField profile) (fun _ => 0) (PerturbedGreen.spatialPoint x)=
      PerturbedGreen.insertion actual (fun _ => profile x) (fun _ => 0) 0 := by
  simp only [PerturbedGreen.insertion,YangMills.Response.Forcing.spatialInsertion,actual_coframe,
    p286GaugeConnectionMotherVariation,gaugeField,PerturbedGreen.spatialPart_point]

theorem rawGauge_ae (profile : GaugeProfile) (field : FullMatterL2) :
    rawGauge 0 profile field=ᵐ[volume] fun x => operator
      (PerturbedGreen.insertion actual (gaugeField profile) (fun _ => 0) (PerturbedGreen.spatialPoint x)) (field x) := by
  filter_upwards [principal_ae 0 (gaugePotential profile field),gaugePotential_ae profile field,
    Lp.coeFn_smul Complex.I (principal 0 (gaugePotential profile field))] with x temporal insertion scaled
  change (Complex.I • principal 0 (gaugePotential profile field)) x=_
  rw [scaled]
  simp only [Pi.smul_apply]
  rw [temporal,insertion,gauge_insertion_native]
  have identity := congrArg (fun A : FiberOperators => A (field x))
    (congrArg operator (rawGauge_mother (profile x)))
  simpa only [operator_smul,operator_mul,smul_apply,mul_apply_eq_comp] using! identity

theorem configuration_connection (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile)
    (point : BasePoint) (mu : LorentzianIndex) :
    connection (configuration gauge parameter scalar) point mu=connection actual point mu+
      (parameter : ℂ) • diracExteriorMotherLieAction (p286GaugeConnectionMotherVariation (gaugeField gauge) point mu) :=
  PerturbedGreen.varied_connection actual (gaugeField gauge) (fun _ => 0) parameter point mu

theorem configuration_kernel (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile)
    (point : BasePoint) (momentum : Fin 3 → ℝ) (z : ℂ) :
    diracKernel (configuration gauge parameter scalar) point momentum z=
      diracKernel actual point momentum z+(parameter : ℂ) •
        PerturbedGreen.insertion actual (gaugeField gauge) (fun _ => 0) point+
        diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (scalarField scalar point))-
        diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point)) := by
  apply LinearMap.ext
  intro v
  have coframe : (configuration gauge parameter scalar).coframe=actual.coframe := rfl
  have value : (configuration gauge parameter scalar).scalar point=scalarField scalar point := rfl
  simp only [diracKernel,lowerSymbol,knownSymbol,coframe,value,configuration_connection,
    PerturbedGreen.insertion,YangMills.Response.Forcing.spatialInsertion,
    map_zero,yukawa_zero,add_zero,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.sum_apply,
    map_add,map_smul,Finset.sum_add_distrib,Finset.smul_sum,smul_add,smul_smul]
  rw [mul_comm Complex.I (parameter : ℂ)]
  abel

theorem native_kernel_ae (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile)
    (momentum : Fin 3 → ℝ) (z : ℂ) (field : FullMatterL2) :
    (fun x => operator (diracKernel (configuration gauge parameter scalar)
      (PerturbedGreen.spatialPoint x) momentum z) (field x))=ᵐ[volume]
      fun x => operator (diracKernel actual 0 momentum z) (field x)+
        (parameter : ℂ) • rawGauge 0 gauge field x+potential scalar field x-backgroundY 0 field x := by
  filter_upwards [rawGauge_ae gauge field,potential_ae scalar field,backgroundY_ae 0 field]
    with x gaugeRead scalarRead backgroundRead
  have scalarValue : scalarField scalar (PerturbedGreen.spatialPoint x)=scalar x := by
    rw [scalarField,PerturbedGreen.spatialPart_point]
  rw [configuration_kernel,PerturbedGreen.actual_kernel_constant]
  have difference (A B : Mother) : operator (A-B)=operator A-operator B := by ext v; simp [operator]
  rw [difference,operator_add,operator_add,operator_smul,scalarValue]
  simp only [add_apply,sub_apply,smul_apply]
  rw [gaugeRead,scalarRead,backgroundRead,actual_scalar]

theorem fullG_original_weak (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (source : FullMatterL2)
    (test : 𝓢(Position,Hilbert)) :
    let field := fullG 0 energy damping positive gauge parameter scalar source
    (∫ x, inner ℂ ((SpatialWeak.constant 0 energy damping).adjoint (test x)+Complex.I •
      ∑ j, (SpatialWeak.spatial 0 j).adjoint (fderiv ℝ test x (SpatialWeak.direction j))) (field x))+
      (parameter : ℂ)*(∫ x, inner ℂ (test x) (operator
        (PerturbedGreen.insertion actual (gaugeField gauge) (fun _ => 0) (PerturbedGreen.spatialPoint x)) (field x)))+
      (∫ x, inner ℂ (test x) (operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (scalar x))) (field x)-
        operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar 0))) (field x)))=
      ∫ x, inner ℂ (test x) (source x) := by
  dsimp only
  have weak := fullG_weak 0 energy damping positive gauge parameter scalar source test
  dsimp only at weak
  rw [L2.inner_def,L2.inner_def,L2.inner_def,L2.inner_def] at weak
  convert weak using 1
  · congr 1
    · congr 1
      · apply integral_congr_ae
        filter_upwards [(SpatialWeak.adjointDifferential 0 energy damping test).coeFn_toLp 2 volume] with x read
        rw [read,SpatialWeak.adjointDifferential,SpatialWeak.firstOrder_apply]
      · congr 1
        apply integral_congr_ae
        filter_upwards [test.coeFn_toLp 2 volume,
          rawGauge_ae gauge (fullG 0 energy damping positive gauge parameter scalar source)] with x read applied
        rw [read,applied]
    · apply integral_congr_ae
      filter_upwards [test.coeFn_toLp 2 volume,
        potential_ae scalar (fullG 0 energy damping positive gauge parameter scalar source),
        backgroundY_ae 0 (fullG 0 energy damping positive gauge parameter scalar source),
        Lp.coeFn_sub (potential scalar (fullG 0 energy damping positive gauge parameter scalar source))
          (backgroundY 0 (fullG 0 energy damping positive gauge parameter scalar source))]
        with x read varied background subtracted
      simp only [Pi.sub_apply] at subtracted
      rw [read,subtracted,varied,background]
  · apply integral_congr_ae
    filter_upwards [test.coeFn_toLp 2 volume] with x read
    rw [read]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
