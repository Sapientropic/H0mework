import H0mework.Physics.LowEnergy.FullQuantum.HistoryGreen.Native

/-! The genuine time response lies in the original maximal spatial domain and satisfies both inverse identities. -/
set_option autoImplicit false
open MeasureTheory
open scoped SchwartzMap InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryLaplace YangMills.FullPairing
noncomputable section
attribute [local irreducible] fullOperator value fullG SpatialWeak.adjointDifferential

theorem stationary_domain (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    MemLp (SpatialGreen.sourceField 0 energy damping
      (stationaryValue gauge coupling scalar energy damping (inversePrincipal 0 source))) 2 volume := by
  rw [stationary_diracValue_original gauge coupling scalar energy damping positive source]
  exact fullG_domain 0 energy damping positive gauge coupling scalar source

def domainStationary (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) : SpatialGreen.Domain 0 energy damping :=
  ⟨stationaryValue gauge coupling scalar energy damping (inversePrincipal 0 source),
    stationary_domain gauge coupling scalar energy damping positive source⟩

theorem originalKernel_stationary (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    originalKernel 0 energy damping gauge coupling scalar
      (domainStationary gauge coupling scalar energy damping positive source)=source := by
  have same : domainStationary gauge coupling scalar energy damping positive source=
      domainFullG 0 energy damping positive gauge coupling scalar source :=
    Subtype.ext (stationary_diracValue_original gauge coupling scalar energy damping positive source)
  rw [same,originalKernel_fullG]

theorem stationary_originalKernel (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (field : SpatialGreen.Domain 0 energy damping) :
    stationaryValue gauge coupling scalar energy damping
      (inversePrincipal 0 (originalKernel 0 energy damping gauge coupling scalar field))=field.val := by
  rw [stationary_diracValue_original gauge coupling scalar energy damping positive,fullG_originalKernel]

theorem stationary_original_weak (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) (test : 𝓢(Position,Hilbert)) :
    let field := stationaryValue gauge coupling scalar energy damping (inversePrincipal 0 source)
    inner ℂ ((SpatialWeak.adjointDifferential 0 energy damping test).toLp 2 volume) field+
      (coupling : ℂ)*inner ℂ (test.toLp 2 volume) (rawGauge 0 gauge field)+
      inner ℂ (test.toLp 2 volume) (potential scalar field-backgroundY 0 field)=
      inner ℂ (test.toLp 2 volume) source := by
  dsimp only
  rw [stationary_diracValue_original gauge coupling scalar energy damping positive]
  exact fullG_weak 0 energy damping positive gauge coupling scalar source test

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
