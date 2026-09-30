import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Continuation
import H0mework.Physics.LowEnergy.FullQuantum.PerturbedGreen.Local
import H0mework.Physics.YangMillsSourceQuantum.InsertionSkew
import Mathlib.MeasureTheory.Function.Holder

/-! Every bounded real P286 field generates its own full self-adjoint Hamiltonian insertion. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open DiracExteriorMatterAction SU7MotherLieAlgebra SU7MotherGaugeTheory Triangular
noncomputable section
local instance gaugeModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance gaugeCoordinateFintype : Fintype P286CoordinateIndex := Fintype.ofFinite _

def gaugeMotherLinear : P286GaugeOneForm →ₗ[ℝ] Mother where
  toFun gauge := Complex.I • YangMills.Response.Forcing.insertion actual (fun _ => gauge) 0
  map_add' first second := by
    apply LinearMap.ext
    intro v
    simp only [YangMills.Response.Forcing.insertion,YangMills.Response.Forcing.spatialInsertion,
      p286GaugeConnectionMotherVariation,Pi.add_apply,map_add,p286LieBlockEmbed_add,
      diracExteriorMotherLieAction_add,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,
      LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.sum_apply,map_add,map_sum,
      Finset.sum_add_distrib,smul_add,smul_sub,smul_neg,Finset.smul_sum]
    abel
  map_smul' r gauge := by
    apply LinearMap.ext
    intro v
    simp only [YangMills.Response.Forcing.insertion,YangMills.Response.Forcing.spatialInsertion,
      p286GaugeConnectionMotherVariation,Pi.smul_apply,map_smul,p286LieBlockEmbed_real_smul,
      diracExteriorMotherLieAction_real_smul,LinearMap.sub_apply,LinearMap.neg_apply,
      LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.sum_apply,map_smul,
      Finset.smul_sum,smul_sub,smul_neg,smul_smul,RingHom.id_apply]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
    simp only [mul_comm Complex.I (r : ℂ),← smul_smul,← Finset.smul_sum,map_smul]
    module

def gaugeLinear : P286GaugeOneForm →ₗ[ℝ] FiberOperators where
  toFun gauge := operator (gaugeMotherLinear gauge)
  map_add' first second := by rw [map_add,operator_add]
  map_smul' r gauge := by
    rw [gaugeMotherLinear.map_smul r gauge]
    change operator ((r : ℂ) • gaugeMotherLinear gauge)=(r : ℂ) • operator (gaugeMotherLinear gauge)
    exact operator_smul _ _

def gaugeMap : P286GaugeOneForm →L[ℝ] FiberOperators :=
  ⟨gaugeLinear,gaugeLinear.continuous_of_finiteDimensional⟩

theorem gaugeMap_selfAdjoint (gauge : P286GaugeOneForm) : IsSelfAdjoint (gaugeMap gauge) := by
  have same := Stage10.Recovery.stageOneThroughTenClosure.final.recoversStageNine.trans
    Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.actualGenerated
  have source := YangMills.Response.Skew.insertion_skew (fun _ => gauge) 0
  rw [same] at source
  change star (operator (Complex.I • YangMills.Response.Forcing.insertion actual (fun _ => gauge) 0))=_
  rw [operator_smul,star_smul,source]
  simp [gaugeMap,gaugeLinear,gaugeMotherLinear,operator_smul]

abbrev GaugeProfile := Lp (α := Position) P286GaugeOneForm ⊤ volume

def gaugeMatrixField (profile : GaugeProfile) : Lp (α := Position) FiberOperators ⊤ volume :=
  gaugeMap.compLpL ⊤ volume profile

def gaugePotential (profile : GaugeProfile) : PerturbedGreen.SpatialOperators :=
  (ContinuousLinearMap.id ℂ FiberOperators).holderL volume ⊤ 2 2 (gaugeMatrixField profile)

theorem gaugePotential_ae (profile : GaugeProfile) (field : FullMatterL2) :
    gaugePotential profile field=ᵐ[volume] fun x => gaugeMap (profile x) (field x) := by
  filter_upwards [(ContinuousLinearMap.id ℂ FiberOperators).coeFn_holder (p := ⊤) (q := 2) (r := 2)
    (gaugeMatrixField profile) field,gaugeMap.coeFn_compLpL profile] with x multiplied native
  erw [multiplied]
  change gaugeMatrixField profile x (field x)=_
  erw [native]

theorem gaugePotential_selfAdjoint (profile : GaugeProfile) : IsSelfAdjoint (gaugePotential profile) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro first second
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gaugePotential_ae profile first,gaugePotential_ae profile second] with x left right
  erw [left,right]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (gaugeMap_selfAdjoint (profile x))) (first x) (second x)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
