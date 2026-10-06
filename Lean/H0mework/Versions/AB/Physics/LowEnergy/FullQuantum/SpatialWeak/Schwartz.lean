import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.SpatialWeak.Symbol

/-! Smooth rapidly decreasing full-matter fields recover the original first-order spatial operator. -/
set_option autoImplicit false
open MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialWeak
open FullSpace SpatialGreen YangMills.FullPairing ProofFreeRicherAnholonomicSource
noncomputable section

private theorem constant_fourier (L : FiberOperators) (f : 𝓢(Position,Hilbert)) :
    𝓕 (f.postcompCLM L)=(𝓕 f).postcompCLM L := by
  apply SchwartzMap.ext
  intro xi
  rw [SchwartzMap.fourier_coe,SchwartzMap.postcompCLM_apply,
    SchwartzMap.fourier_coe,Real.fourier_eq,Real.fourier_eq]
  have generated := L.integral_comp_comm
    ((Real.fourierIntegral_convergent_iff (μ := volume) xi).mpr f.integrable)
  simpa only [SchwartzMap.postcompCLM_apply,Circle.smul_def,map_smul] using generated

def direction (j : Fin 3) : Position := EuclideanSpace.basisFun (Fin 3) ℝ j

def firstOrder (C : FiberOperators) (G : Fin 3 → FiberOperators)
    (f : 𝓢(Position,Hilbert)) : 𝓢(Position,Hilbert) :=
  f.postcompCLM C+Complex.I • ∑ j, (∂_{direction j} f).postcompCLM (G j)

theorem firstOrder_apply (C : FiberOperators) (G : Fin 3 → FiberOperators)
    (f : 𝓢(Position,Hilbert)) (x : Position) :
    firstOrder C G f x=C (f x)+Complex.I • ∑ j, G j (fderiv ℝ f x (direction j)) := by
  simp [firstOrder,SchwartzMap.lineDerivOp_apply_eq_fderiv]

def polynomial (C : FiberOperators) (G : Fin 3 → FiberOperators) (frequency : Position) : FiberOperators :=
  C-∑ j, ((physicalMomentum frequency j : ℝ) : ℂ) • G j

attribute [local irreducible] direction firstOrder polynomial symbol constant spatial

private theorem derivative_scalar (L : FiberOperators) (r : ℝ) (v : Hilbert) :
    Complex.I • L ((2*Real.pi*Complex.I : ℂ) • (r • v))=
      -(((2*Real.pi*r : ℝ) : ℂ) • L v) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r v,map_smul,map_smul,← neg_smul]
  simp only [smul_smul]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem firstOrder_fourier (C : FiberOperators) (G : Fin 3 → FiberOperators)
    (f : 𝓢(Position,Hilbert)) (frequency : Position) :
    (𝓕 (firstOrder C G f)) frequency=polynomial C G frequency ((𝓕 f) frequency) := by
  have term (j : Fin 3) :
      Complex.I • ((𝓕 ((∂_{direction j} f).postcompCLM (G j))) frequency)=
      -(((physicalMomentum frequency j : ℝ) : ℂ) • G j ((𝓕 f) frequency)) := by
    rw [constant_fourier,SchwartzMap.postcompCLM_apply]
    have growth : (fun y : Position => inner ℝ y (direction j)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (direction j)).hasTemperateGrowth
    have derivative := congrArg (fun g : 𝓢(Position,Hilbert) => g frequency)
      (SchwartzMap.fourier_lineDerivOp_eq f (direction j))
    simp only [smul_apply] at derivative
    rw [SchwartzMap.smulLeftCLM_apply_apply growth] at derivative
    have coordinate : inner ℝ frequency (direction j)=frequency j := by
      unfold direction
      exact EuclideanSpace.inner_basisFun_real (Fin 3) frequency j
    rw [coordinate] at derivative
    rw [derivative]
    convert! derivative_scalar (G j) (frequency j) ((𝓕 f) frequency) using 1
  rw [firstOrder,FourierTransform.fourier_add,FourierTransform.fourier_smul,
    FourierTransform.fourier_sum,constant_fourier]
  change C ((𝓕 f) frequency)+Complex.I •
    (∑ j, (𝓕 ((∂_{direction j} f).postcompCLM (G j))) frequency)=_
  simp only [Finset.smul_sum]
  simp only [polynomial,sub_apply,sum_apply,smul_apply]
  simp only [term,Finset.sum_neg_distrib]
  rfl

def differential (point : BasePoint) (energy damping : ℝ) :
    𝓢(Position,Hilbert) → 𝓢(Position,Hilbert) := firstOrder (constant point energy damping) (spatial point)

attribute [local irreducible] differential

theorem differential_fourier (point : BasePoint) (energy damping : ℝ)
    (f : 𝓢(Position,Hilbert)) (frequency : Position) :
    (𝓕 (differential point energy damping f)) frequency=
      symbol point energy damping frequency ((𝓕 f) frequency) := by
  rw [differential,firstOrder_fourier,symbol_affine,polynomial]

theorem schwartz_source_ae (point : BasePoint) (energy damping : ℝ) (f : 𝓢(Position,Hilbert)) :
    sourceField point energy damping (f.toLp 2)=ᵐ[volume]
      FullSpace.fourier ((differential point energy damping f).toLp 2) := by
  have input : FullSpace.fourier (f.toLp 2)=(𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq f
  have output : FullSpace.fourier ((differential point energy damping f).toLp 2)=
      (𝓕 (differential point energy damping f)).toLp 2 := SchwartzMap.toLp_fourier_eq _
  rw [output]
  filter_upwards [(𝓕 f).coeFn_toLp 2 volume,
    (𝓕 (differential point energy damping f)).coeFn_toLp 2 volume] with frequency hinput houtput
  change symbol point energy damping frequency (FullSpace.fourier (f.toLp 2) frequency)=_
  erw [input,hinput,houtput,differential_fourier]

theorem schwartz_in_domain (point : BasePoint) (energy damping : ℝ) (f : 𝓢(Position,Hilbert)) :
    MemLp (sourceField point energy damping (f.toLp 2)) 2 volume :=
  (Lp.memLp (FullSpace.fourier ((differential point energy damping f).toLp 2))).ae_eq
    (schwartz_source_ae point energy damping f).symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialWeak
