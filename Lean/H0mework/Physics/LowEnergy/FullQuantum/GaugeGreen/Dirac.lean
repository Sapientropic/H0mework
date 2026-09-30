import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Coupled

/-! Return through the original C0 and Yukawa to the actual spatial Dirac equation. -/
set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped SchwartzMap InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open DiracExteriorMatterAction Triangular StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction ScalarGreen
noncomputable section

private theorem constant_toLp (L : FiberOperators) (f : 𝓢(Position,Hilbert)) :
    L.compLpL 2 volume (f.toLp 2)=(f.postcompCLM L).toLp 2 := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (f.toLp 2),f.coeFn_toLp 2 volume,
    (f.postcompCLM L).coeFn_toLp 2 volume] with x hl hf hg
  erw [hl,hf]

private theorem constant_fourier_schwartz (L : FiberOperators) (f : 𝓢(Position,Hilbert)) :
    𝓕 (f.postcompCLM L)=(𝓕 f).postcompCLM L := by
  apply SchwartzMap.ext
  intro xi
  rw [SchwartzMap.fourier_coe,SchwartzMap.postcompCLM_apply,
    SchwartzMap.fourier_coe,Real.fourier_eq,Real.fourier_eq]
  have generated := L.integral_comp_comm
    ((Real.fourierIntegral_convergent_iff (μ := volume) xi).mpr f.integrable)
  simpa only [SchwartzMap.postcompCLM_apply,Circle.smul_def,map_smul] using generated

theorem constant_fourier (L : FiberOperators) (field : FullMatterL2) :
    FullSpace.fourier (L.compLpL 2 volume field)=L.compLpL 2 volume (FullSpace.fourier field) := by
  apply DenseRange.induction_on (p := fun g : FullMatterL2 =>
      FullSpace.fourier (L.compLpL 2 volume g)=L.compLpL 2 volume (FullSpace.fourier g))
    (SchwartzMap.denseRange_toLpCLM (E := Position) (F := Hilbert) (p := 2) ENNReal.ofNat_ne_top) field
  · exact isClosed_eq (FullSpace.fourier.continuous.comp (L.compLpL 2 volume).continuous)
      ((L.compLpL 2 volume).continuous.comp FullSpace.fourier.continuous)
  · intro test
    change 𝓕 (L.compLpL 2 volume (test.toLp 2))=L.compLpL 2 volume (𝓕 (test.toLp 2))
    rw [constant_toLp,SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq,
      constant_toLp,constant_fourier_schwartz]

def backgroundY (point : BasePoint) : PerturbedGreen.SpatialOperators :=
  (operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point)))).compLpL 2 volume

def rawGauge (point : BasePoint) (gauge : GaugeProfile) : PerturbedGreen.SpatialOperators :=
  Complex.I • (principal point).comp (gaugePotential gauge)

theorem diracKernel_free_factor (point : BasePoint) (momentum : Fin 3 → ℝ) (z : ℂ) :
    diracKernel actual point momentum z=(-Complex.I) •
      (currentCoframeMatterTemporalPrincipal (actual.coframe point)*freeKernel actual point momentum z)+
        diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point)) := by
  apply LinearMap.ext
  intro v
  change (-Complex.I*z) • currentCoframeMatterTemporalPrincipal (actual.coframe point) v+
    (freeKnown actual point momentum v+
      diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point)) v+
      currentCoframeMatterTemporalPrincipal (actual.coframe point) (connection actual point 0 v))=
    (-Complex.I) • currentCoframeMatterTemporalPrincipal (actual.coframe point)
      (z • v-Complex.I • (-currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)
        (freeKnown actual point momentum v)-connection actual point 0 v))+
      diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point)) v
  simp only [map_sub,map_smul,map_neg,
    currentCoframeMatterTemporalPrincipalInverse_right _ (actual_noncharacteristic point),
    smul_sub,smul_neg,smul_smul]
  simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul]
  abel

theorem symbol_free_factor (point : BasePoint) (energy damping : ℝ) (frequency : Position) :
    SpatialGreen.symbol point energy damping frequency=(-Complex.I) •
      (operator (currentCoframeMatterTemporalPrincipal (actual.coframe point))*
        freeKernelOperator point (physicalMomentum frequency) energy damping)+
      operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point))) := by
  rw [SpatialGreen.symbol,diracKernel_free_factor,operator_add,operator_smul,operator_mul]
  rfl

theorem principal_fourier (point : BasePoint) (field : FullMatterL2) :
    FullSpace.fourier (principal point field)=principal point (FullSpace.fourier field) :=
  constant_fourier _ field

theorem backgroundY_fourier (point : BasePoint) (field : FullMatterL2) :
    FullSpace.fourier (backgroundY point field)=backgroundY point (FullSpace.fourier field) :=
  constant_fourier _ field

theorem principal_ae (point : BasePoint) (field : FullMatterL2) :
    principal point field=ᵐ[volume] fun x =>
      operator (currentCoframeMatterTemporalPrincipal (actual.coframe point)) (field x) :=
  (operator (currentCoframeMatterTemporalPrincipal (actual.coframe point))).coeFn_compLpL field

theorem backgroundY_ae (point : BasePoint) (field : FullMatterL2) :
    backgroundY point field=ᵐ[volume] fun x =>
      operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point))) (field x) :=
  (operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point)))).coeFn_compLpL field

attribute [local irreducible] principal backgroundY SpatialGreen.sourceField SpatialGreen.symbol

theorem diracSource_fourier_ae (point : BasePoint) (field source : FullMatterL2) :
    FullSpace.fourier ((-Complex.I) • principal point source+backgroundY point field)=ᵐ[volume]
      fun frequency => (-Complex.I) • operator (currentCoframeMatterTemporalPrincipal (actual.coframe point))
        (FullSpace.fourier source frequency)+
        operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point)))
          (FullSpace.fourier field frequency) := by
  rw [map_add,map_smul,principal_fourier,backgroundY_fourier]
  filter_upwards [principal_ae point (FullSpace.fourier source),backgroundY_ae point (FullSpace.fourier field),
    Lp.coeFn_add ((-Complex.I) • principal point (FullSpace.fourier source)) (backgroundY point (FullSpace.fourier field)),
    Lp.coeFn_smul (-Complex.I) (principal point (FullSpace.fourier source))]
    with frequency temporal yukawa addition scaled
  simp only [Pi.add_apply,Pi.smul_apply] at addition scaled
  rw [addition,scaled,temporal,yukawa]

theorem free_equation_original (point : BasePoint) (energy damping : ℝ) (field source : FullMatterL2)
    (solves : sourceField point energy damping field=ᵐ[volume] FullSpace.fourier source) :
    SpatialGreen.Equation point energy damping field ((-Complex.I) • principal point source+backgroundY point field) := by
  filter_upwards [solves,diracSource_fourier_ae point field source] with frequency solved output
  unfold SpatialGreen.sourceField
  rw [symbol_free_factor,output]
  simp only [add_apply,smul_apply,mul_apply_eq_comp]
  unfold sourceField at solved
  rw [solved]

theorem principalOperator_inverse_left (point : BasePoint) (v : Hilbert) :
    operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))
      (operator (currentCoframeMatterTemporalPrincipal (actual.coframe point)) v)=v := by
  obtain ⟨w,rfl⟩ := naturalCoordinates.surjective v
  rw [operator_coordinates,operator_coordinates,
    currentCoframeMatterTemporalPrincipalInverse_left _ (actual_noncharacteristic point)]

theorem original_equation_free (point : BasePoint) (energy damping : ℝ) (field source : FullMatterL2)
    (solves : SpatialGreen.Equation point energy damping field
      ((-Complex.I) • principal point source+backgroundY point field)) :
    sourceField point energy damping field=ᵐ[volume] FullSpace.fourier source := by
  filter_upwards [solves,diracSource_fourier_ae point field source] with frequency solved output
  unfold SpatialGreen.sourceField at solved
  rw [symbol_free_factor,output] at solved
  simp only [add_apply,smul_apply,mul_apply_eq_comp] at solved
  have scaled := add_right_cancel solved
  have read := congrArg (fun v : Hilbert => Complex.I •
    operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)) v) scaled
  unfold sourceField
  simpa only [map_smul,principalOperator_inverse_left,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul] using read

private theorem coupled_source (point : BasePoint) (gauge : GaugeProfile) (parameter : ℝ)
    (scalar : ScalarProfile) (field source : FullMatterL2) :
    (-Complex.I) • principal point
      (Complex.I • inversePrincipal point (source-potential scalar field)+(parameter : ℂ) • gaugePotential gauge field)+
      backgroundY point field=
        source-(parameter : ℂ) • rawGauge point gauge field-(potential scalar field-backgroundY point field) := by
  change (-Complex.I) • principal point
    (Complex.I • inversePrincipal point (source-potential scalar field)+(parameter : ℂ) • gaugePotential gauge field)+
    backgroundY point field=
      source-(parameter : ℂ) • (Complex.I • principal point (gaugePotential gauge field))-
        (potential scalar field-backgroundY point field)
  rw [map_add,map_smul,map_smul,inversePrincipal_right]
  simp only [smul_add,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul]
  module

theorem coupled_original (point : BasePoint) (energy damping : ℝ) (gauge : GaugeProfile) (parameter : ℝ)
    (scalar : ScalarProfile) (field source : FullMatterL2)
    (solves : CoupledEquation point energy damping gauge parameter scalar field source) :
    SpatialGreen.Equation point energy damping field
      (source-(parameter : ℂ) • rawGauge point gauge field-(potential scalar field-backgroundY point field)) := by
  have original := free_equation_original point energy damping field
    (Complex.I • inversePrincipal point (source-potential scalar field)+(parameter : ℂ) • gaugePotential gauge field) solves
  rw [coupled_source] at original
  exact original

theorem original_coupled (point : BasePoint) (energy damping : ℝ) (gauge : GaugeProfile) (parameter : ℝ)
    (scalar : ScalarProfile) (field source : FullMatterL2)
    (solves : SpatialGreen.Equation point energy damping field
      (source-(parameter : ℂ) • rawGauge point gauge field-(potential scalar field-backgroundY point field))) :
    CoupledEquation point energy damping gauge parameter scalar field source := by
  apply original_equation_free point energy damping field
    (Complex.I • inversePrincipal point (source-potential scalar field)+(parameter : ℂ) • gaugePotential gauge field)
  rw [coupled_source]
  exact solves

theorem fullG_original (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (source : FullMatterL2) :
    SpatialGreen.Equation point energy damping (fullG point energy damping positive gauge parameter scalar source)
      (source-(parameter : ℂ) • rawGauge point gauge (fullG point energy damping positive gauge parameter scalar source)-
        (potential scalar (fullG point energy damping positive gauge parameter scalar source)-
          backgroundY point (fullG point energy damping positive gauge parameter scalar source))) :=
  coupled_original point energy damping gauge parameter scalar _ source
    (fullG_solves point energy damping positive gauge parameter scalar source)


theorem fullG_original_unique (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (field source : FullMatterL2)
    (solves : SpatialGreen.Equation point energy damping field
      (source-(parameter : ℂ) • rawGauge point gauge field-(potential scalar field-backgroundY point field))) :
    field=fullG point energy damping positive gauge parameter scalar source :=
  fullG_unique point energy damping positive gauge parameter scalar field source
    (original_coupled point energy damping gauge parameter scalar field source solves)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
