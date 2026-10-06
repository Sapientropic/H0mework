import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussCARHistory
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussYukawaCoefficient
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceBoundaryGram
import H0mework.Physics.LowEnergy.Electromagnetic.Identification.Composite

/-! Original scalar--Canonical composite legs on the actual Gauss100 core.
The existing half-density CAR acts after source scalar multiplication. Both
legs enter the unchanged completed H0 resolvent; no configuration state is chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.GaussComposite
open SaturationMonoid.PhysicsCore
open LowEnergy.Electromagnetic.Identification
open SU7ExteriorMatterRestriction StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreDifferential GaussCoreHilbert GaussNativePotential GaussHistoryHilbert
open SourceBoundaryGram FullYSourceResolventGraphSplice
open GaussUnitaryHistory (HistorySpace inclusion)
open scoped ContDiff InnerProductSpace

def mode (spin : Fin 2) (color : Fin 3) : Mode :=
  Sum.inl ⟨(spin.castLE (by decide) : Fin 4), Sum.inr (Sum.inl (Composite.matterBasis color))⟩

def scalarCoefficient (channel : Fin 2) (color : Fin 3) : Scalar →ₗ[ℂ] ℂ :=
  (if color=1 then (-1 : ℂ) else 1) •
    ((su7ExteriorBasis 4).coord (Composite.scalarBasis channel color)).comp
      scalarCoordinateEquiv.symm.toLinearMap

def coefficient (channel : Fin 2) (color : Fin 3) (z : SourceCoordinateSlice) : ℂ :=
  scalarCoefficient channel color (scalarField z)

def originalRead (channel spin : Fin 2) (phi : Scalar) (psi : DiracExteriorMatterCarrier) : ℂ :=
  ∑ color : Fin 3, scalarCoefficient channel color phi *
    (su7ExteriorBasis 2).repr (psi (spin.castLE (by decide))).2.1 (Composite.matterBasis color)

theorem original_mode_read (spin : Fin 2) (color : Fin 3) (psi : DiracExteriorMatterCarrier) :
    LowEnergy.Quantum.coordinates psi
      ⟨(spin.castLE (by decide) : Fin 4),Sum.inr (Sum.inl (Composite.matterBasis color))⟩ =
    (su7ExteriorBasis 2).repr (psi (spin.castLE (by decide))).2.1 (Composite.matterBasis color) := by
  rfl

theorem source_coefficient_bridge (channel spin : Fin 2) (phi : Scalar)
    (psi : DiracExteriorMatterCarrier) :
    originalRead channel spin phi psi = ∑ color : Fin 3,
      scalarCoefficient channel color phi * LowEnergy.Quantum.coordinates psi
        ⟨(spin.castLE (by decide) : Fin 4),Sum.inr (Sum.inl (Composite.matterBasis color))⟩ := by
  simp only [originalRead,original_mode_read]

theorem mode_equal (s t : Fin 2) (c d : Fin 3) :
    mode s c = mode t d ↔ s=t ∧ c=d := by
  constructor
  · intro h
    have hs := congrArg (fun m : Mode => Sum.elim (fun q => q.1) (fun q => q.1) m) h
    have he : s=t := Fin.ext (by simpa only [mode,Sum.elim_inl,Fin.val_castLE] using congrArg Fin.val hs)
    subst t
    have hc : Composite.matterBasis c = Composite.matterBasis d := by simpa [mode] using h
    have e := congrArg Subtype.val hc
    change ({Sum.inl c,Sum.inr (Sum.inr (Sum.inl 0))} : Finset SU7MotherLieAlgebra.SU7MotherIndex) =
      {Sum.inl d,Sum.inr (Sum.inr (Sum.inl 0))} at e
    have member : Sum.inl c ∈ ({Sum.inl d,Sum.inr (Sum.inr (Sum.inl 0))} :
        Finset SU7MotherLieAlgebra.SU7MotherIndex) := by rw [←e]; simp
    refine ⟨rfl,?_⟩
    simpa only [Finset.mem_insert,Finset.mem_singleton,Sum.inl.injEq,Sum.inl_ne_inr,or_false] using member
  · rintro ⟨rfl,rfl⟩
    rfl

def fiberAnnihilation (channel spin : Fin 2) (phi : Scalar) : FockFiber →L[ℂ] FockFiber :=
  ∑ color : Fin 3, scalarCoefficient channel color phi • GaussCARHistory.annihilateFiber (mode spin color)

def fiberCreation (channel spin : Fin 2) (phi : Scalar) : FockFiber →L[ℂ] FockFiber :=
  ∑ color : Fin 3, star (scalarCoefficient channel color phi) • GaussCARHistory.createFiber (mode spin color)

def scalarGram (a b : Fin 2) (phi psi : Scalar) : ℂ :=
  ∑ color : Fin 3, scalarCoefficient a color phi * star (scalarCoefficient b color psi)

private theorem sum_anticommutator {R : Type*} [Ring R] [Algebra ℂ R]
    (a b : Fin 3 → ℂ) (A B : Fin 3 → R) :
    (∑ c, a c • A c)*(∑ d, b d • B d)+(∑ d, b d • B d)*(∑ c, a c • A c) =
      ∑ c, ∑ d, (a c*b d) • (A c*B d+B d*A c) := by
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul,
    smul_add,Finset.sum_add_distrib,Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [mul_comm (b d) (a c)]

theorem fiber_contact (a b s t : Fin 2) (phi psi : Scalar) :
    fiberAnnihilation a s phi*fiberCreation b t psi+
      fiberCreation b t psi*fiberAnnihilation a s phi =
      if s=t then scalarGram a b phi psi • (1 : FockFiber →L[ℂ] FockFiber) else 0 := by
  unfold fiberAnnihilation fiberCreation
  rw [sum_anticommutator (fun c => scalarCoefficient a c phi)
    (fun d => star (scalarCoefficient b d psi))
    (fun c => GaussCARHistory.annihilateFiber (mode s c))
    (fun d => GaussCARHistory.createFiber (mode t d))]
  simp_rw [GaussCARHistory.fiber_car,mode_equal]
  by_cases h : s=t
  · simp only [h,true_and,ite_true]
    simp only [smul_ite,smul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true,scalarGram]
    simp only [Fin.sum_univ_three]
    apply ContinuousLinearMap.ext
    intro f
    apply PiLp.ext
    intro word
    let q : Fin 3 → ℂ := fun c => scalarCoefficient a c phi * star (scalarCoefficient b c psi)
    change q 0 * f word + q 1 * f word + q 2 * f word = (q 0+q 1+q 2)*f word
    ring
  · simp [h]

theorem coefficient_smooth (channel : Fin 2) (color : Fin 3) :
    ContDiff ℝ ∞ (coefficient channel color) :=
  (scalarCoefficient channel color).toContinuousLinearMap.contDiff.restrict_scalars ℝ
    |>.comp scalarField_smooth

def scalarMultiplier (c : SourceCoordinateSlice → ℂ)
    (smooth : ContDiff ℝ ∞ c) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => c z • (1 : FockFiber →L[ℂ] FockFiber))
    (fun _ => (smooth.smul contDiff_const).contDiffAt)

theorem scalarMultiplier_apply (c : SourceCoordinateSlice → ℂ)
    (smooth : ContDiff ℝ ∞ c) (f : QuantumTest) (z : SourceCoordinateSlice) :
    scalarMultiplier c smooth f z = c z • f z := by
  rfl

def annihilationSource (channel : Fin 2) (spin : Fin 2) : QuantumTest →ₗ[ℂ] H :=
  ∑ color : Fin 3,
    (GaussCARHistory.annihilate (mode spin color)).toLinearMap.comp
      (embed.comp (scalarMultiplier (coefficient channel color) (coefficient_smooth channel color)))

def creationSource (channel : Fin 2) (spin : Fin 2) : QuantumTest →ₗ[ℂ] H :=
  ∑ color : Fin 3,
    (GaussCARHistory.create (mode spin color)).toLinearMap.comp
      (embed.comp (scalarMultiplier (fun z => star (coefficient channel color z))
        (((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.contDiff).comp
          (coefficient_smooth channel color))))

theorem annihilation_source_apply (channel : Fin 2) (spin : Fin 2) (f : QuantumTest) :
    annihilationSource channel spin f = ∑ color : Fin 3,
      GaussCARHistory.annihilate (mode spin color)
        (embed (scalarMultiplier (coefficient channel color) (coefficient_smooth channel color) f)) := by
  simp only [annihilationSource,LinearMap.sum_apply,LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]

theorem annihilation_bound (channel : Fin 2) (spin : Fin 2) (f : QuantumTest) :
    ‖annihilationSource channel spin f‖ ≤ ∑ color : Fin 3,
      ‖embed (scalarMultiplier (coefficient channel color) (coefficient_smooth channel color) f)‖ := by
  rw [annihilation_source_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => GaussCARHistory.annihilate_bound _ _))

def leg (addition : Bool) (channel spin : Fin 2) : QuantumTest →ₗ[ℂ] H :=
  if addition then creationSource channel spin else annihilationSource channel spin

def propagate (addition : Bool) (channel spin : Fin 2) (z : ℂ) (hz : z.im≠0)
    (f : QuantumTest) : HistorySpace :=
  sameResolvent z hz (inclusion (leg addition channel spin f))

def twoPoint (leftAddition rightAddition : Bool) (leftChannel leftSpin rightChannel rightSpin : Fin 2)
    (z : ℂ) (hz : z.im≠0) (f g : QuantumTest) : ℂ :=
  inner ℂ (inclusion (leg leftAddition leftChannel leftSpin f))
    (propagate rightAddition rightChannel rightSpin z hz g)

theorem twoPoint_bound
    (leftAddition rightAddition : Bool) (leftChannel leftSpin rightChannel rightSpin : Fin 2)
    (z : ℂ) (hz : z.im≠0) (f g : QuantumTest) :
    ‖twoPoint leftAddition rightAddition leftChannel leftSpin rightChannel rightSpin z hz f g‖ ≤
      ‖leg leftAddition leftChannel leftSpin f‖ *
        ((1/|z.im|)*‖leg rightAddition rightChannel rightSpin g‖) := by
  apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
  rw [inclusion.norm_map]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [propagate,inclusion.norm_map] using
    same_resolvent_bound z hz (inclusion (leg rightAddition rightChannel rightSpin g))

theorem propagate_boundary (addition : Bool) (channel spin : Fin 2)
    (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    propagate addition channel spin z hz f =
      sourceBody z (inclusion (leg addition channel spin f)) +
      boundaryReturn z hz (inclusion (leg addition channel spin f)) := by
  simp only [propagate,boundaryReturn,sub_apply]
  abel

theorem coefficient_variation (channel : Fin 2) (color : Fin 3)
    (phi delta : Scalar) :
    scalarCoefficient channel color (phi+delta) =
      scalarCoefficient channel color phi+scalarCoefficient channel color delta := map_add _ _ _

end LowEnergy.GaussComposite
