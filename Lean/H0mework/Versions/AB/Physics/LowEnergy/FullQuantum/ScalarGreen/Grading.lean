import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.ScalarGreen.Local

/-! The original grading survives the nonlocal spatial Green and arbitrary local scalar profiles. -/
set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ScalarGreen
open FullSpace SpatialGreen YangMills.FullPairing DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Triangular
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

private theorem constant_fourier (L : FiberOperators) (field : FullMatterL2) :
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

theorem six_fourier (field : FullMatterL2) :
    FullSpace.fourier (six field)=six (FullSpace.fourier field) :=
  constant_fourier (operator MixedSymbol.degreeSix) field

private theorem mother_six_square : MixedSymbol.degreeSix*MixedSymbol.degreeSix=MixedSymbol.degreeSix := by
  apply LinearMap.ext
  intro v
  rfl

private theorem expansion_preserves {A A0 : Mother} (expansion : ClosedLoops.Expansion A A0) :
    MixedSymbol.degreeSix*A*MixedSymbol.degreeSix=A*MixedSymbol.degreeSix := by
  have right : A*MixedSymbol.degreeSix=A0*MixedSymbol.degreeSix := by
    have killed := expansion.2.2
    have distribution : (A-A0)*MixedSymbol.degreeSix=A*MixedSymbol.degreeSix-A0*MixedSymbol.degreeSix := by
      convert! sub_mul A A0 MixedSymbol.degreeSix using 1
    rw [distribution] at killed
    exact sub_eq_zero.mp killed
  calc
    _ = MixedSymbol.degreeSix*(A*MixedSymbol.degreeSix) := mul_assoc _ _ _
    _ = MixedSymbol.degreeSix*(A0*MixedSymbol.degreeSix) := by rw [right]
    _ = (MixedSymbol.degreeSix*A0)*MixedSymbol.degreeSix := (mul_assoc _ _ _).symm
    _ = (A0*MixedSymbol.degreeSix)*MixedSymbol.degreeSix := by rw [expansion.1.eq]
    _ = A0*(MixedSymbol.degreeSix*MixedSymbol.degreeSix) := mul_assoc _ _ _
    _ = A0*MixedSymbol.degreeSix := by rw [mother_six_square]
    _ = _ := right.symm

theorem diracValue_preserves_six (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    operator MixedSymbol.degreeSix*Retarded.diracValue point momentum energy damping*operator MixedSymbol.degreeSix=
      Retarded.diracValue point momentum energy damping*operator MixedSymbol.degreeSix := by
  rw [Retarded.diracValue_original point momentum energy damping positive]
  rw [← operator_mul,← operator_mul,← operator_mul]
  congr 1
  exact expansion_preserves (ClosedLoops.source_diracResolvent actual point momentum
    (Retarded.spectralParameter energy damping) (Retarded.sourceFree_regular point momentum energy damping positive))

theorem green_six (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) (field : FullMatterL2) :
    six (green point energy damping positive (six field))=green point energy damping positive (six field) := by
  apply FullSpace.fourier.injective
  rw [six_fourier]
  apply Lp.ext
  filter_upwards [six_ae (FullSpace.fourier (green point energy damping positive (six field))),
    green_fourier_ae point energy damping positive (six field),six_ae (FullSpace.fourier field)]
    with frequency outer response inner
  rw [outer,response,six_fourier,inner]
  exact congrArg (fun A : FiberOperators => A (FullSpace.fourier field frequency))
    (diracValue_preserves_six point (physicalMomentum frequency) energy damping positive)

theorem two_scalar_insertions_zero (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (first second : ScalarProfile) (field : FullMatterL2) :
    potential first (green point energy damping positive (potential second field))=0 := by
  have projected := green_six point energy damping positive (potential second field)
  rw [six_potential] at projected
  have killed := potential_six first (green point energy damping positive (potential second field))
  rw [projected] at killed
  exact killed

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ScalarGreen
