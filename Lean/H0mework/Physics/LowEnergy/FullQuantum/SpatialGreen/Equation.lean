import H0mework.Physics.LowEnergy.FullQuantum.SpatialGreen.Multiplier

/-! The full source Dirac multiplier has an everywhere-defined bounded inverse on its true L² domain. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialGreen
open FullSpace Retarded Triangular YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
noncomputable section

def symbol (point : BasePoint) (energy damping : ℝ) (frequency : Position) : FiberOperators :=
  operator (diracKernel actual point (physicalMomentum frequency) (spectralParameter energy damping))

def sourceField (point : BasePoint) (energy damping : ℝ) (field : FullMatterL2) : Position → Hilbert :=
  fun frequency => symbol point energy damping frequency (fourier field frequency)

def Equation (point : BasePoint) (energy damping : ℝ) (field source : FullMatterL2) : Prop :=
  sourceField point energy damping field=ᵐ[volume] fourier source

theorem green_solves (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) : Equation point energy damping (green point energy damping positive source) source := by
  filter_upwards [green_fourier_ae point energy damping positive source] with frequency read
  change symbol point energy damping frequency (fourier (green point energy damping positive source) frequency)=_
  rw [read]
  exact congrArg (fun A : FiberOperators => A (fourier source frequency))
    (diracValue_two_sided point (physicalMomentum frequency) energy damping positive).1

theorem equation_unique (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (field source : FullMatterL2) (solves : Equation point energy damping field source) :
    field=green point energy damping positive source := by
  apply fourier.injective
  apply Lp.ext
  filter_upwards [solves,green_fourier_ae point energy damping positive source] with frequency equation read
  rw [read,← equation]
  exact (congrArg (fun A : FiberOperators => A (fourier field frequency))
    (diracValue_two_sided point (physicalMomentum frequency) energy damping positive).2).symm

theorem equation_iff (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (field source : FullMatterL2) :
    Equation point energy damping field source ↔ field=green point energy damping positive source := by
  constructor
  · exact equation_unique point energy damping positive field source
  · rintro rfl
    exact green_solves point energy damping positive source

def Domain (point : BasePoint) (energy damping : ℝ) :=
  {field : FullMatterL2 // MemLp (sourceField point energy damping field) 2 volume}

def dirac (point : BasePoint) (energy damping : ℝ) (field : Domain point energy damping) : FullMatterL2 :=
  fourier.symm (field.property.toLp _)

theorem dirac_fourier_ae (point : BasePoint) (energy damping : ℝ) (field : Domain point energy damping) :
    fourier (dirac point energy damping field)=ᵐ[volume] sourceField point energy damping field.val := by
  rw [dirac,fourier.apply_symm_apply]
  exact field.property.coeFn_toLp

theorem green_domain (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) : MemLp (sourceField point energy damping (green point energy damping positive source)) 2 volume :=
  (Lp.memLp (fourier source)).ae_eq (green_solves point energy damping positive source).symm

def domainGreen (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) : Domain point energy damping :=
  ⟨green point energy damping positive source,green_domain point energy damping positive source⟩

theorem dirac_green (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) : dirac point energy damping (domainGreen point energy damping positive source)=source := by
  apply fourier.injective
  apply Lp.ext
  exact (dirac_fourier_ae point energy damping (domainGreen point energy damping positive source)).trans
    (green_solves point energy damping positive source)

theorem green_dirac (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (field : Domain point energy damping) :
    green point energy damping positive (dirac point energy damping field)=field.val :=
  (equation_unique point energy damping positive field.val (dirac point energy damping field)
    (dirac_fourier_ae point energy damping field).symm).symm

theorem green_injective (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    Function.Injective (green point energy damping positive) := by
  intro left right same
  have domains : domainGreen point energy damping positive left=domainGreen point energy damping positive right :=
    Subtype.ext same
  have read := congrArg (dirac point energy damping) domains
  simpa only [dirac_green] using read

theorem nonzero_response (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) (nonzero : source≠0) : green point energy damping positive source≠0 := by
  intro zero
  apply nonzero
  exact green_injective point energy damping positive (zero.trans (map_zero _).symm)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialGreen
