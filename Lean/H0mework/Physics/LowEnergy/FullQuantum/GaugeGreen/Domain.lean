import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Dirac

/-! The all-field Green is a two-sided inverse on the original maximal Fourier domain. -/
set_option autoImplicit false
open MeasureTheory
open scoped SchwartzMap InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource ScalarGreen
noncomputable section
attribute [local irreducible] fullG SpatialWeak.adjointDifferential

def originalKernel (point : BasePoint) (energy damping : ℝ) (gauge : GaugeProfile) (parameter : ℝ)
    (scalar : ScalarProfile) (field : SpatialGreen.Domain point energy damping) : FullMatterL2 :=
  SpatialGreen.dirac point energy damping field+(parameter : ℂ) • rawGauge point gauge field.val+
    (potential scalar field.val-backgroundY point field.val)

theorem fullG_domain (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (source : FullMatterL2) :
    MemLp (SpatialGreen.sourceField point energy damping (fullG point energy damping positive gauge parameter scalar source)) 2 volume :=
  (Lp.memLp _).ae_eq (fullG_original point energy damping positive gauge parameter scalar source).symm

def domainFullG (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (source : FullMatterL2) :
    SpatialGreen.Domain point energy damping :=
  ⟨fullG point energy damping positive gauge parameter scalar source,
    fullG_domain point energy damping positive gauge parameter scalar source⟩

theorem originalKernel_fullG (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (source : FullMatterL2) :
    originalKernel point energy damping gauge parameter scalar
      (domainFullG point energy damping positive gauge parameter scalar source)=source := by
  have original : SpatialGreen.dirac point energy damping
      (domainFullG point energy damping positive gauge parameter scalar source)=
      source-(parameter : ℂ) • rawGauge point gauge (fullG point energy damping positive gauge parameter scalar source)-
        (potential scalar (fullG point energy damping positive gauge parameter scalar source)-
          backgroundY point (fullG point energy damping positive gauge parameter scalar source)) := by
    apply fourier.injective
    apply Lp.ext
    exact (SpatialGreen.dirac_fourier_ae point energy damping
      (domainFullG point energy damping positive gauge parameter scalar source)).trans
      (fullG_original point energy damping positive gauge parameter scalar source)
  unfold originalKernel
  rw [original]
  dsimp only [domainFullG]
  abel

theorem fullG_originalKernel (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile)
    (field : SpatialGreen.Domain point energy damping) :
    fullG point energy damping positive gauge parameter scalar
      (originalKernel point energy damping gauge parameter scalar field)=field.val := by
  apply Eq.symm
  apply fullG_original_unique point energy damping positive gauge parameter scalar field.val
  have cancelled : originalKernel point energy damping gauge parameter scalar field-
      (parameter : ℂ) • rawGauge point gauge field.val-(potential scalar field.val-backgroundY point field.val)=
      SpatialGreen.dirac point energy damping field := by
    unfold originalKernel
    abel
  rw [cancelled]
  exact (SpatialGreen.dirac_fourier_ae point energy damping field).symm

theorem fullG_injective (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) :
    Function.Injective (fullG point energy damping positive gauge parameter scalar) := by
  intro first second same
  have domains : domainFullG point energy damping positive gauge parameter scalar first=
      domainFullG point energy damping positive gauge parameter scalar second := Subtype.ext same
  have read := congrArg (originalKernel point energy damping gauge parameter scalar) domains
  simpa only [originalKernel_fullG] using read

theorem fullG_nonzero (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (source : FullMatterL2) (nonzero : source≠0) :
    fullG point energy damping positive gauge parameter scalar source≠0 := by
  intro zero
  apply nonzero
  exact fullG_injective point energy damping positive gauge parameter scalar (zero.trans (map_zero _).symm)

theorem fullG_weak (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (source : FullMatterL2)
    (test : 𝓢(Position,Hilbert)) :
    let field := fullG point energy damping positive gauge parameter scalar source
    inner ℂ ((SpatialWeak.adjointDifferential point energy damping test).toLp 2 volume) field+
      (parameter : ℂ)*inner ℂ (test.toLp 2 volume) (rawGauge point gauge field)+
      inner ℂ (test.toLp 2 volume) (potential scalar field-backgroundY point field)=
      inner ℂ (test.toLp 2 volume) source := by
  dsimp only
  have weak := SpatialWeak.equation_weak point energy damping _ _
    (fullG_original point energy damping positive gauge parameter scalar source) test
  rw [inner_sub_right,inner_sub_right,inner_smul_right] at weak
  rw [weak]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
