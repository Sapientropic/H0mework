import H0mework.Physics.LowEnergy.PacketFourier.Original
import H0mework.Physics.LowEnergy.FullQuantum.GaugeHistory.Primitive

/-! A real bounded P286 variation keeps the original coframe, temporal
principal and preparation. Its Hamiltonian contribution is generated through C0. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
open FullQuantum FullSpace PacketNoise PacketFourier GaugeGreen GaugeHistory
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section
attribute [local irreducible] freeAction inversePrincipal

def configuration (gauge : GaugeProfile) (epsilon : ℝ) : StageNineHolonomicConfiguration :=
  PerturbedGreen.varied actual (gaugeField gauge) (fun _ => 0) epsilon

theorem configuration_coframe (gauge : GaugeProfile) (epsilon : ℝ) :
    (configuration gauge epsilon).coframe=actual.coframe := rfl

theorem configuration_matter (gauge : GaugeProfile) (epsilon : ℝ) :
    (configuration gauge epsilon).matter=actual.matter := rfl

theorem configuration_dual (gauge : GaugeProfile) (epsilon : ℝ) :
    (configuration gauge epsilon).conjugateMatter=actual.conjugateMatter := rfl

theorem configuration_principal (gauge : GaugeProfile) (epsilon : ℝ) (point : BasePoint) :
    currentCoframeMatterTemporalPrincipal ((configuration gauge epsilon).coframe point)=
      currentCoframeMatterTemporalPrincipal (actual.coframe point) := rfl

theorem configuration_kernel (gauge : GaugeProfile) (epsilon : ℝ) (point : BasePoint)
    (momentum : Fin 3 → ℝ) (z : ℂ) :
    Triangular.diracKernel (configuration gauge epsilon) point momentum z=
      Triangular.diracKernel actual point momentum z+(epsilon : ℂ) •
        PerturbedGreen.insertion actual (gaugeField gauge) (fun _ => 0) point :=
  PerturbedGreen.varied_diracKernel actual (gaugeField gauge) (fun _ => 0) epsilon point momentum z

theorem configuration_kernel_ae (gauge : GaugeProfile) (epsilon : ℝ)
    (momentum : Fin 3 → ℝ) (z : ℂ) (field : FullMatterL2) :
    (fun x => YangMills.FullPairing.operator (Triangular.diracKernel (configuration gauge epsilon)
      (PerturbedGreen.spatialPoint x) momentum z) (field x))=ᵐ[volume]
      fun x => YangMills.FullPairing.operator (Triangular.diracKernel actual 0 momentum z) (field x)+
        (epsilon : ℂ) • rawGauge 0 gauge field x := by
  filter_upwards [rawGauge_ae gauge field] with x read
  rw [configuration_kernel,PerturbedGreen.actual_kernel_constant,
    Triangular.operator_add,Triangular.operator_smul]
  simp only [add_apply,smul_apply]
  rw [read]

def originalDomain (field : Quantum.Generator.domain freeAction) : SpatialGreen.Domain 0 0 1 :=
  ⟨field.val,(HistoryGenerator.generator_domain_iff_original 0 1 (by norm_num) field.val).mp field.property⟩

def primitiveHamiltonian (gauge : GaugeProfile) (epsilon : ℝ)
    (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  Complex.I • field.val-Complex.I • inversePrincipal 0
    (SpatialGreen.dirac 0 0 1 (originalDomain field)+(epsilon : ℂ) • rawGauge 0 gauge field.val)

theorem primitiveHamiltonian_source (gauge : GaugeProfile) (epsilon : ℝ)
    (field : Quantum.Generator.domain freeAction) :
    primitiveHamiltonian gauge epsilon field=
      sourceHamiltonian field+(epsilon : ℂ) • gaugePotential gauge field.val := by
  have original := source_hamiltonian_dirac 0 1 (by norm_num) (originalDomain field)
  have same : (⟨(originalDomain field).val,
      (HistoryGenerator.generator_domain_iff_original 0 1 (by norm_num) (originalDomain field).val).mpr
        (originalDomain field).property⟩ : Quantum.Generator.domain freeAction)=field := Subtype.ext rfl
  rw [same] at original
  simp only [Complex.ofReal_zero,Complex.ofReal_one,mul_one,zero_add] at original
  have sign : Complex.I*(epsilon : ℂ)*Complex.I= -(epsilon : ℂ) := by
    calc
      _ = (Complex.I*Complex.I)*(epsilon : ℂ) := by ring
      _ = _ := by simp
  rw [primitiveHamiltonian,original,map_add,map_smul,rawGauge,
    smul_apply,ContinuousLinearMap.comp_apply,map_smul,inversePrincipal_left]
  simp only [smul_add,smul_smul,← mul_assoc,sign,neg_smul]
  dsimp only [originalDomain]
  abel

def variedHamiltonian (gauge : GaugeProfile) (epsilon : ℝ)
    (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  sourceHamiltonian field+(epsilon : ℂ) • gaugePotential gauge field.val

def variedAdjointHamiltonian (gauge : GaugeProfile) (epsilon : ℝ)
    (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  conjugateHamiltonian field+(epsilon : ℂ) • (gaugePotential gauge).adjoint field.val

theorem variedHamiltonian_pair (gauge : GaugeProfile) (epsilon : ℝ)
    (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (variedHamiltonian gauge epsilon left) right.val=
      inner ℂ left.val (variedAdjointHamiltonian gauge epsilon right) := by
  simp only [variedHamiltonian,variedAdjointHamiltonian,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,Complex.conj_ofReal,sourceHamiltonian_pair,
    ContinuousLinearMap.adjoint_inner_right]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
