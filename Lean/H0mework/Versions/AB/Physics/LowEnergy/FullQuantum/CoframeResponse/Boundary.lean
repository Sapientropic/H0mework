import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.StateResponse.Connected
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Evolution

/-! The original independent dual fixes a temporal-momentum weight at the
preparation boundary. It is not moved through the full primal flow. -/
set_option autoImplicit false
open scoped Matrix InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
open DiracExteriorMatterAction DiracCliffordRepresentation
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open StageNineFullDiracAdjointMaterial StageNineCurrentCoframeMatterTemporalPrincipal
open YangMills.FullPairing QuantizationCheck.Fermion Fermion StateGreen
noncomputable section
attribute [local instance] Fermion.fullIndexOrder

theorem actual_dual_graph (point : BasePoint) (v : DiracExteriorMatterCarrier) :
    actual.conjugateMatter point v=(spinScale : ℂ)*fullCanonicalDiracAdjoint (actual.matter point) v := by
  conv_lhs => rw [← flipMatter_twice v]
  rw [dual_flip,← inner_embed]
  rw [Quantum.canonicalDual_full_response,Quantum.spinExchange_selfAdjoint,
    Quantum.coordinatePair_full,← natural_inner,actual_eq_twice_prepared,inner_smul_left]
  have same : Quantum.spinExchange v=flipMatter v := (flipMatter_source v).symm
  rw [same]
  change 2*(spinScale : ℂ)*inner ℂ (prepared point) (naturalCoordinates (flipMatter v))=
    (spinScale : ℂ)*(star (2 : ℂ)*inner ℂ (prepared point) (naturalCoordinates (flipMatter v)))
  norm_num
  ring

def boundaryWeight (C : StageNineHolonomicConfiguration) (point : BasePoint) : Mother :=
  (-Complex.I*((|(C.coframe point).det| : ℝ) : ℂ)*(spinScale : ℂ)) •
    Quantum.spinExchange.comp (currentCoframeMatterTemporalPrincipal (C.coframe point))

theorem boundaryWeight_original (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (v : DiracExteriorMatterCarrier) :
    normalizedMomentum C point (actual.conjugateMatter point) v=
      Quantum.coordinatePair (actual.matter point) (boundaryWeight C point v) := by
  rw [normalizedMomentum,LinearMap.smul_apply,LinearMap.comp_apply,actual_dual_graph]
  simp only [boundaryWeight,LinearMap.smul_apply,LinearMap.comp_apply,Kinetic.pair_smul_right]
  rw [Quantum.canonicalDual_full_response,Quantum.spinExchange_selfAdjoint]
  change _ * (_ * _) = _ * _
  ring

theorem boundaryWeight_actual (point : BasePoint) :
    boundaryWeight actual point=(spinScale : ℂ) • diracMatrixMatterAction diracGammaFive := by
  apply LinearMap.ext
  intro v
  simp only [boundaryWeight,LinearMap.smul_apply,LinearMap.comp_apply,actual_temporal_principal,
    map_smul]
  have time := Kinetic.exchange_time_action v
  change Quantum.spinExchange (diracMatrixMatterAction diracGammaZero v)=diracMatrixMatterAction diracGammaFive v at time
  rw [time]
  rw [actual_coframe,Stage9C.Dynamics.Homogeneous.homogeneousCoframe_det,abs_of_pos lapse_pos]
  simp only [smul_smul]
  have nonzero : (lapse : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  congr 1
  field_simp
  simp [Complex.I_sq]

def temporalForce (C : StageNineHolonomicConfiguration) (point : BasePoint) (A : Mother) : Mother :=
  (-Complex.I) • (currentCoframeMatterTemporalPrincipalInverse (C.coframe point)).comp A

def boundaryInsertion (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : Mother) : Mother :=
  (boundaryWeight C point).comp ((primal C point k (-t)).comp
    ((temporalForce C point A).comp (primal C point k t)))

theorem boundaryInsertion_original (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : Mother) :
    ((|(C.coframe point).det| : ℝ) : ℂ)*canonicalDual C point k t (actual.conjugateMatter point)
      (A (primal C point k t (actual.matter point)))=
      -Quantum.coordinatePair (actual.matter point) (boundaryInsertion C point k t A (actual.matter point)) := by
  simp only [canonicalDual,LinearMap.comp_apply,actual_dual_graph,
    boundaryInsertion,boundaryWeight,temporalForce,LinearMap.smul_apply,map_smul,
    Kinetic.pair_smul_right]
  rw [Quantum.canonicalDual_full_response,Quantum.spinExchange_selfAdjoint]
  ring_nf
  simp [Complex.I_sq]

def boundaryWord (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : Mother) : Module.End ℂ (Fock Quantum.Index) :=
  quantize (Quantum.operatorMatrix (boundaryWeight C point))*
    quantize (Quantum.operatorMatrix ((primal C point k (-t)).comp
      ((temporalForce C point A).comp (primal C point k t))))

theorem boundaryWord_pair (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : Mother) :
    read (preparedVector point) (boundaryWord C point k t A)=
      Quantum.coordinatePair (preparedMatter point) (boundaryInsertion C point k t A (preparedMatter point)) := by
  rw [boundaryWord,StateResponse.read_four_word,← Quantum.matrix_composition]
  change modePair (Quantum.coordinates (preparedMatter point))
    (Quantum.operatorMatrix (boundaryInsertion C point k t A)*ᵥQuantum.coordinates (preparedMatter point))=_
  rw [Quantum.matrix_action]
  rfl

theorem original_dual_full_CAR (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (A : Mother) :
    ((|(C.coframe point).det| : ℝ) : ℂ)*canonicalDual C point k t (actual.conjugateMatter point)
      (A (primal C point k t (actual.matter point)))=
      -4*read (preparedVector point) (boundaryWord C point k t A) := by
  rw [boundaryInsertion_original,boundaryWord_pair]
  have normalized : actual.matter point=(2 : ℂ) • preparedMatter point := by
    simp [preparedMatter,smul_smul]
  rw [normalized,map_smul,Quantum.coordinatePair_smul]
  norm_num

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
