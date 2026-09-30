import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Native

/-! The finite continuation solves the actual unbounded source free symbol plus every bounded native gauge field. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource PerturbedGreen
noncomputable section

def sourceField (point : BasePoint) (energy damping : ℝ) (field : FullMatterL2) : Position → Hilbert :=
  fun frequency => freeKernelOperator point (physicalMomentum frequency) energy damping (fourier field frequency)

def FourierEquation (point : BasePoint) (energy damping : ℝ) (W : SpatialOperators) (parameter : ℝ)
    (field source : FullMatterL2) : Prop :=
  sourceField point energy damping field=ᵐ[volume] fourier (source+(parameter : ℂ) • W field)

theorem freeR_solves (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    sourceField point energy damping (freeR point energy damping positive source)=ᵐ[volume] fourier source := by
  filter_upwards [freeR_fourier_ae point energy damping positive source] with frequency read
  change freeKernelOperator point (physicalMomentum frequency) energy damping
    (fourier (freeR point energy damping positive source) frequency)=_
  rw [read]
  exact congrArg (fun A : FiberOperators => A (fourier source frequency))
    (freeValue_two_sided point (physicalMomentum frequency) energy damping positive).1

theorem fourier_equation_iff (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (parameter : ℝ) (field source : FullMatterL2) :
    FourierEquation point energy damping W parameter field source ↔
      Equation point energy damping positive W parameter field source := by
  constructor
  · intro solves
    apply fourier.injective
    apply Lp.ext
    filter_upwards [solves,freeR_fourier_ae point energy damping positive (source+(parameter : ℂ) • W field)]
      with frequency equation read
    change freeKernelOperator point (physicalMomentum frequency) energy damping (fourier field frequency)=_ at equation
    rw [read,← equation]
    have identity := congrArg (fun A : FiberOperators => A (fourier field frequency))
      (freeValue_two_sided point (physicalMomentum frequency) energy damping positive).2
    simpa only [mul_apply_eq_comp,one_apply_eq_self] using identity.symm
  · intro solves
    change field=freeR point energy damping positive (source+(parameter : ℂ) • W field) at solves
    change sourceField point energy damping field=ᵐ[volume] _
    conv_lhs => rw [solves]
    exact freeR_solves point energy damping positive _

def nativeR (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) : SpatialOperators :=
  gaugeR point energy damping positive (gaugePotential profile) (gaugePotential_selfAdjoint profile) parameter

theorem nativeR_solves (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) (source : FullMatterL2) :
    FourierEquation point energy damping (gaugePotential profile) parameter
      (nativeR point energy damping positive profile parameter source) source :=
  (fourier_equation_iff point energy damping positive _ _ _ _).mpr
    (gaugeR_solves point energy damping positive _ (gaugePotential_selfAdjoint profile) parameter source)

theorem nativeR_unique (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) (field source : FullMatterL2)
    (solves : FourierEquation point energy damping (gaugePotential profile) parameter field source) :
    field=nativeR point energy damping positive profile parameter source :=
  gaugeR_unique point energy damping positive _ (gaugePotential_selfAdjoint profile) parameter field source
    ((fourier_equation_iff point energy damping positive _ _ _ _).mp solves)

theorem nativeR_bound (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) : ‖nativeR point energy damping positive profile parameter‖≤damping⁻¹ :=
  gaugeR_norm point energy damping positive _ (gaugePotential_selfAdjoint profile) parameter

def Domain (point : BasePoint) (energy damping : ℝ) :=
  {field : FullMatterL2 // MemLp (sourceField point energy damping field) 2 volume}

def nativeKernel (point : BasePoint) (energy damping : ℝ) (profile : GaugeProfile) (parameter : ℝ)
    (field : Domain point energy damping) : FullMatterL2 :=
  fourier.symm (field.property.toLp _)-(parameter : ℂ) • gaugePotential profile field.val

theorem nativeR_domain (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) (source : FullMatterL2) :
    MemLp (sourceField point energy damping (nativeR point energy damping positive profile parameter source)) 2 volume :=
  (Lp.memLp _).ae_eq (nativeR_solves point energy damping positive profile parameter source).symm

def domainR (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) (source : FullMatterL2) : Domain point energy damping :=
  ⟨nativeR point energy damping positive profile parameter source,
    nativeR_domain point energy damping positive profile parameter source⟩

theorem nativeKernel_fourier (point : BasePoint) (energy damping : ℝ) (profile : GaugeProfile) (parameter : ℝ)
    (field : Domain point energy damping) :
    FourierEquation point energy damping (gaugePotential profile) parameter field.val
      (nativeKernel point energy damping profile parameter field) := by
  unfold FourierEquation nativeKernel
  rw [sub_add_cancel,fourier.apply_symm_apply]
  exact field.property.coeFn_toLp.symm

theorem kernel_response (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) (source : FullMatterL2) :
    nativeKernel point energy damping profile parameter (domainR point energy damping positive profile parameter source)=source := by
  have equality : fourier (nativeKernel point energy damping profile parameter
      (domainR point energy damping positive profile parameter source)+(parameter : ℂ) •
        gaugePotential profile (nativeR point energy damping positive profile parameter source))=
      fourier (source+(parameter : ℂ) • gaugePotential profile (nativeR point energy damping positive profile parameter source)) := by
    apply Lp.ext
    exact (nativeKernel_fourier point energy damping profile parameter
      (domainR point energy damping positive profile parameter source)).symm.trans
      (nativeR_solves point energy damping positive profile parameter source)
  exact add_right_cancel (fourier.injective equality)

theorem response_kernel (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) (field : Domain point energy damping) :
    nativeR point energy damping positive profile parameter (nativeKernel point energy damping profile parameter field)=field.val :=
  (nativeR_unique point energy damping positive profile parameter field.val _
    (nativeKernel_fourier point energy damping profile parameter field)).symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
