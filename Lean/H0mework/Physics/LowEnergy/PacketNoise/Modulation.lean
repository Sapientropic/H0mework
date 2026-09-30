import H0mework.Physics.LowEnergy.PacketNoise.Cosine
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Frequency translation and position modulation are the same L² operation,
with the original physical momentum convention k=2πξ. -/
set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace YangMills.FullPairing
noncomputable section

def positionPhase (shift x : Position) : ℂ :=
  Complex.exp (((2*Real.pi*inner ℝ shift x : ℝ) : ℂ)*Complex.I)

theorem positionPhase_continuous (shift : Position) : Continuous (positionPhase shift) := by
  unfold positionPhase
  fun_prop

theorem positionPhase_norm (shift x : Position) : ‖positionPhase shift x‖=1 :=
  Complex.norm_exp_ofReal_mul_I _

def phaseMatrix (shift x : Position) : FiberOperators := positionPhase shift x • 1

theorem phaseMatrix_continuous (shift : Position) : Continuous (phaseMatrix shift) :=
  (positionPhase_continuous shift).smul continuous_const

theorem phaseMatrix_bound (shift x : Position) : ‖phaseMatrix shift x‖≤1 := by
  rw [phaseMatrix,norm_smul,positionPhase_norm,one_mul]
  exact ContinuousLinearMap.norm_id_le

def modulation (shift : Position) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  multiplier (phaseMatrix shift) (phaseMatrix_continuous shift) 1 (phaseMatrix_bound shift) (by norm_num)

theorem modulation_ae (shift : Position) (field : FullMatterL2) :
    modulation shift field =ᵐ[volume] fun x => positionPhase shift x • field x := by
  filter_upwards [multiplierValue_ae (phaseMatrix shift) (phaseMatrix_continuous shift) 1
    (phaseMatrix_bound shift) field] with x hx
  exact hx

theorem schwartz_shift (shift : Position) (field : SchwartzMap Position Hilbert) :
    frequencyShift shift (field.toLp 2 volume)=(field.compSubConstCLM ℂ shift).toLp 2 volume := by
  apply Lp.ext
  have moved := (measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae (field.coeFn_toLp 2 volume)
  filter_upwards [frequencyShift_ae shift (field.toLp 2 volume),moved,
    (field.compSubConstCLM ℂ shift).coeFn_toLp 2 volume] with x hx hfield htranslated
  rw [hx,hfield,htranslated]
  rfl

theorem inverse_fourier_shift (shift : Position) (field : Position → Hilbert) (x : Position) :
    𝓕⁻ (fun frequency => field (frequency-shift)) x=positionPhase shift x • 𝓕⁻ field x := by
  have translated := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (-innerₗ Position) field (-shift)) x
  change VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ Position)
      (fun frequency => field (frequency-shift)) x=
    positionPhase shift x • VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ Position) field x
  simpa [positionPhase,Function.comp_def,sub_eq_add_neg,Circle.smul_def,Real.fourierChar_apply] using translated

theorem schwartz_modulation (shift : Position) (field : SchwartzMap Position Hilbert) :
    FullSpace.fourier.symm (frequencyShift shift (field.toLp 2 volume))=
      modulation shift (FullSpace.fourier.symm (field.toLp 2 volume)) := by
  rw [schwartz_shift]
  change 𝓕⁻ ((field.compSubConstCLM ℂ shift).toLp 2 volume)=modulation shift (𝓕⁻ (field.toLp 2 volume))
  rw [SchwartzMap.toLp_fourierInv_eq,SchwartzMap.toLp_fourierInv_eq]
  apply Lp.ext
  filter_upwards [(𝓕⁻ (field.compSubConstCLM ℂ shift)).coeFn_toLp 2 volume,
    modulation_ae shift ((𝓕⁻ field).toLp 2 volume),(𝓕⁻ field).coeFn_toLp 2 volume] with x hleft hright hfield
  rw [hleft,hright,hfield]
  simp only [SchwartzMap.fourierInv_coe]
  exact inverse_fourier_shift shift field x

theorem phaseShift_modulation (shift : Position) (field : FullMatterL2) :
    phaseShift shift field=modulation shift field := by
  have inverseIdentity (g : FullMatterL2) : FullSpace.fourier.symm (frequencyShift shift g)=modulation shift (FullSpace.fourier.symm g) := by
    apply DenseRange.induction_on (p := fun g : FullMatterL2 =>
      FullSpace.fourier.symm (frequencyShift shift g)=modulation shift (FullSpace.fourier.symm g))
      (SchwartzMap.denseRange_toLpCLM (E := Position) (F := Hilbert) (p := 2) (μ := volume) ENNReal.ofNat_ne_top) g
    · exact isClosed_eq
        (FullSpace.fourier.symm.continuous.comp (frequencyShift shift).continuous)
        ((modulation shift).continuous.comp FullSpace.fourier.symm.continuous)
    · intro f
      exact schwartz_modulation shift f
  have generated := inverseIdentity (FullSpace.fourier field)
  rw [FullSpace.fourier.symm_apply_apply] at generated
  exact generated

theorem phaseShift_position (shift : Position) (field : FullMatterL2) :
    phaseShift shift field =ᵐ[volume] fun x =>
      Complex.exp (((2*Real.pi*inner ℝ shift x : ℝ) : ℂ)*Complex.I) • field x := by
  rw [phaseShift_modulation]
  exact modulation_ae shift field

theorem physicalPhase_argument (shift x : Position) :
    2*Real.pi*inner ℝ shift x=∑ j : Fin 3,physicalMomentum shift j*x j := by
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,physicalMomentum,Finset.mul_sum,mul_assoc]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem phaseShift_physicalMomentum (shift : Position) (field : FullMatterL2) :
    phaseShift shift field =ᵐ[volume] fun x =>
      Complex.exp (((∑ j : Fin 3,physicalMomentum shift j*x j : ℝ) : ℂ)*Complex.I) • field x := by
  simpa only [physicalPhase_argument] using phaseShift_position shift field

theorem cosineShift_position (shift : Position) (field : FullMatterL2) :
    cosineShift shift field =ᵐ[volume] fun x =>
      ((Real.cos (2*Real.pi*inner ℝ shift x) : ℝ) : ℂ) • field x := by
  have expression : cosineShift shift field=(1/2 : ℂ) • (phaseShift shift field+phaseShift (-shift) field) := rfl
  rw [expression]
  filter_upwards [Lp.coeFn_smul (1/2 : ℂ) (phaseShift shift field+phaseShift (-shift) field),
    Lp.coeFn_add (phaseShift shift field) (phaseShift (-shift) field),phaseShift_position shift field,
    phaseShift_position (-shift) field] with x hscale hadd hplus hminus
  rw [hscale]
  simp only [Pi.smul_apply]
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hplus,hminus]
  simp only [← add_smul,smul_smul,inner_neg_left,mul_neg,Complex.ofReal_neg,neg_mul]
  congr 1
  rw [Complex.ofReal_cos,Complex.cos]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
