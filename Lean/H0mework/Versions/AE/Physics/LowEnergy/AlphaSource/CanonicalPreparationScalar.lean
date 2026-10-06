import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparedGraph

/-! The physical scalar norm of the original Canonical preparation.  The
completion is along the original Number1 core; no configuration state is chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalScalarPreparation
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussDensityCore GaussComposite.SourceGraph
open MeasureTheory Set Filter
open scoped Topology ContDiff Distributions

abbrev ScalarSpace := GaussHistoryHilbert.SectorHilbert 1

def scalarCore : ScalarTest →ₗ[ℂ] ScalarSpace where
  toFun := scalarLp 1
  map_add' f g := by
    apply Lp.ext
    filter_upwards [scalarLp_ae 1 (f+g),scalarLp_ae 1 f,scalarLp_ae 1 g,
      Lp.coeFn_add (scalarLp 1 f) (scalarLp 1 g)] with z h hf hg ha
    rw [h,ha,Pi.add_apply,hf,hg]
    rfl
  map_smul' c f := scalarLp_smul 1 c f

theorem scalarCore_dense : DenseRange scalarCore := by
  have dense := OpenChartTestDomain.dense_compact_contDiff_inside
    GaussHistoryHilbert.physicalChart (GaussHistoryHilbert.numberMeasure 1)
      (F := ℂ) (p := 2) (by norm_num)
  apply dense.mono
  rintro f ⟨g,hfg,hgk,hgc,hgs⟩
  let test : ScalarTest := ⟨g,hgc,hgk,hgs⟩
  exact ⟨test,Lp.ext ((scalarLp_ae 1 test).trans hfg.symm)⟩

theorem seed_core_norm (f : ScalarTest) : ‖seedCore f‖=‖scalarCore f‖ := by
  change ‖embed (seedSection f)‖=‖scalarLp 1 f‖
  rw [seedSection_norm,seed_unit,one_mul]

def seedBase : ScalarSpace →L[ℂ] H := seedCore.extendOfNorm scalarCore

theorem seedBase_core (f : ScalarTest) : seedBase (scalarCore f)=embed (seedSection f) :=
  LinearMap.extendOfNorm_eq scalarCore_dense
    ⟨1,fun f => by rw [seed_core_norm,one_mul]⟩ f

theorem seedBase_norm (f : ScalarSpace) : ‖seedBase f‖=‖f‖ := by
  refine scalarCore_dense.induction_on f (isClosed_eq (by fun_prop) continuous_norm) ?_
  intro g
  rw [seedBase_core]
  exact seed_core_norm g

def seedIsometry : ScalarSpace →ₗᵢ[ℂ] H where
  toLinearMap := seedBase.toLinearMap
  norm_map' := seedBase_norm

def forget : Profile →L[ℂ] ScalarSpace := scalarCore.extendOfNorm core

theorem forget_core (f : ScalarTest) : forget (core f)=scalarCore f :=
  LinearMap.extendOfNorm_eq core_dense
    ⟨1,fun f => by simpa only [scalarCore,one_mul] using! scalar_base_bound f⟩ f

theorem prepared_factors (f : Profile) : prepared f=seedBase (forget f) := by
  refine core_dense.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [prepared_core,forget_core,seedBase_core]

theorem prepared_norm (f : Profile) : ‖prepared f‖=‖forget f‖ := by
  rw [prepared_factors,seedBase_norm]

theorem prepared_inner (f g : Profile) :
    inner ℂ (prepared f) (prepared g)=inner ℂ (forget f) (forget g) := by
  rw [prepared_factors,prepared_factors]
  exact seedIsometry.inner_map_map (forget f) (forget g)

theorem physically_unit_iff (f : Profile) : ‖prepared f‖=1 ↔ ‖forget f‖=1 := by
  rw [prepared_norm]

end LowEnergy.CanonicalScalarPreparation
