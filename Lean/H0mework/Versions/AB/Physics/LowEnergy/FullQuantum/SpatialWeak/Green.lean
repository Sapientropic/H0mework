import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.SpatialWeak.Schwartz

/-! The genuine full-space causal integral solves the original spatial equation against every Schwartz test. -/
set_option autoImplicit false
open Set MeasureTheory FourierTransform
open scoped SchwartzMap InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialWeak
open FullSpace SpatialGreen YangMills.FullPairing ProofFreeRicherAnholonomicSource
noncomputable section
attribute [local irreducible] constant spatial differential symbol sourceField green

def adjointDifferential (point : BasePoint) (energy damping : ℝ) :
    𝓢(Position,Hilbert) → 𝓢(Position,Hilbert) :=
  firstOrder (constant point energy damping).adjoint (fun j => (spatial point j).adjoint)

attribute [local irreducible] adjointDifferential

theorem polynomial_adjoint (C : FiberOperators) (G : Fin 3 → FiberOperators) (frequency : Position) :
    polynomial C.adjoint (fun j => (G j).adjoint) frequency=(polynomial C G frequency).adjoint := by
  have coefficient (r : ℝ) (A : FiberOperators) : ((r : ℂ) • A).adjoint=(r : ℂ) • A.adjoint := by
    have generated := map_smulₛₗ (ContinuousLinearMap.adjoint :
      (Hilbert →L[ℂ] Hilbert) ≃ₗᵢ⋆[ℂ] (Hilbert →L[ℂ] Hilbert)) (r : ℂ) A
    simpa only [Complex.conj_ofReal] using! generated
  simp only [polynomial,map_sub,map_sum]
  simp only [coefficient]

theorem adjointDifferential_fourier (point : BasePoint) (energy damping : ℝ)
    (test : 𝓢(Position,Hilbert)) (frequency : Position) :
    (𝓕 (adjointDifferential point energy damping test)) frequency=
      (symbol point energy damping frequency).adjoint ((𝓕 test) frequency) := by
  rw [adjointDifferential,firstOrder_fourier,polynomial_adjoint,symbol_affine]
  rfl

theorem equation_weak (point : BasePoint) (energy damping : ℝ) (field source : FullMatterL2)
    (equation : Equation point energy damping field source) (test : 𝓢(Position,Hilbert)) :
    inner ℂ ((adjointDifferential point energy damping test).toLp 2 volume) field=
      inner ℂ (test.toLp 2 volume) source := by
  have left : inner ℂ (FullSpace.fourier ((adjointDifferential point energy damping test).toLp 2 volume))
      (FullSpace.fourier field)=inner ℂ ((adjointDifferential point energy damping test).toLp 2 volume) field := by
    convert! FullSpace.fourier.inner_map_map
      ((adjointDifferential point energy damping test).toLp 2 volume) field using 1
  have right : inner ℂ (FullSpace.fourier (test.toLp 2 volume)) (FullSpace.fourier source)=
      inner ℂ (test.toLp 2 volume) source := by
    convert! FullSpace.fourier.inner_map_map (test.toLp 2 volume) source using 1
  rw [← left,← right]
  have input : FullSpace.fourier (test.toLp 2 volume)=(𝓕 test).toLp 2 volume := SchwartzMap.toLp_fourier_eq test
  have output : FullSpace.fourier ((adjointDifferential point energy damping test).toLp 2 volume)=
      (𝓕 (adjointDifferential point energy damping test)).toLp 2 volume := SchwartzMap.toLp_fourier_eq _
  erw [input,output,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [equation,(𝓕 test).coeFn_toLp 2 volume,
    (𝓕 (adjointDifferential point energy damping test)).coeFn_toLp 2 volume] with frequency solved initial result
  rw [initial,result,adjointDifferential_fourier,ContinuousLinearMap.adjoint_inner_left]
  unfold SpatialGreen.sourceField at solved
  rw [solved]

theorem green_weak (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) (test : 𝓢(Position,Hilbert)) :
    inner ℂ ((adjointDifferential point energy damping test).toLp 2 volume)
      (green point energy damping positive source)=inner ℂ (test.toLp 2 volume) source :=
  equation_weak point energy damping _ source (green_solves point energy damping positive source) test

theorem time_integral_weak (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) (test : 𝓢(Position,Hilbert)) :
    inner ℂ ((adjointDifferential point energy damping test).toLp 2 volume)
      (∫ t : ℝ in Ioi 0, MatterSpace.Response.temporalWeight energy damping t •
        spatialFlow point t (inversePrincipal point source))=inner ℂ (test.toLp 2 volume) source := by
  rw [← green_time_integral point energy damping positive]
  exact green_weak point energy damping positive source test

theorem green_recovers_schwartz (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (field : 𝓢(Position,Hilbert)) :
    green point energy damping positive ((differential point energy damping field).toLp 2 volume)=field.toLp 2 volume := by
  have solved : Equation point energy damping (field.toLp 2 volume) ((differential point energy damping field).toLp 2 volume) := by
    convert! schwartz_source_ae point energy damping field using 1
  exact (equation_unique point energy damping positive (field.toLp 2 volume)
    ((differential point energy damping field).toLp 2 volume) solved).symm

theorem domain_dense (point : BasePoint) (energy damping : ℝ) :
    Dense {field : FullMatterL2 | MemLp (sourceField point energy damping field) 2 volume} := by
  apply Dense.mono (s₁ := Set.range (fun test : 𝓢(Position,Hilbert) => (test.toLp 2 volume : FullMatterL2)))
    (s₂ := {field : FullMatterL2 | MemLp (sourceField point energy damping field) 2 volume})
  · rintro field ⟨test,rfl⟩
    exact schwartz_in_domain point energy damping test
  · exact SchwartzMap.denseRange_toLpCLM (E := Position) (F := Hilbert) (p := 2) ENNReal.ofNat_ne_top

theorem equation_graph_closed (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    IsClosed {pair : FullMatterL2 × FullMatterL2 | Equation point energy damping pair.1 pair.2} := by
  have same : {pair : FullMatterL2 × FullMatterL2 | Equation point energy damping pair.1 pair.2}=
      {pair : FullMatterL2 × FullMatterL2 | pair.1=green point energy damping positive pair.2} := by
    ext pair
    exact equation_iff point energy damping positive pair.1 pair.2
  rw [same]
  exact isClosed_eq continuous_fst ((green point energy damping positive).continuous.comp continuous_snd)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialWeak
