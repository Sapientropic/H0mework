import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaColumn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
private abbrev sourceModeDecEq : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq
attribute [local instance] sourceModeDecEq

abbrev yukawaTargetMode (dual : Bool) : Mode :=
  if dual then Sum.inr ⟨1,Sum.inl yukawaOutputA⟩ else Sum.inl ⟨1,Sum.inl yukawaOutputA⟩

def yukawaWitness (dual : Bool) : FockFiber :=
  ActualMotherCAR.triple (rootMode dual (0,0,0)) (rootMode dual (0,1,0)) (yukawaTargetMode dual)

private theorem rootMode_eq (dual : Bool) (i j : NamedMode) :
    rootMode dual i = rootMode dual j ↔ i = j := (modeEmbedding dual).injective.eq_iff

private theorem targetMode_ne_input (dual : Bool) (i : NamedMode) :
    yukawaTargetMode dual ≠ rootMode dual i := by
  cases dual <;> simp [yukawaTargetMode,rootMode,rootIndex]

private theorem named_triple_return (dual : Bool) (i j k : NamedMode) :
    orderedTriple dual i j k = ActualMotherCAR.triple (rootMode dual i) (rootMode dual j) (rootMode dual k) := rfl

/-- An actual mother-CAR witness isolates exactly one source Yukawa matrix
entry of the fixed mixed-spectator candidate, including the epsilon phase. -/
theorem actual_candidate_Y_entry (dual : Bool) (H : Mode → Mode → ℂ) :
    inner ℂ (yukawaWitness dual) (GaussQuantumMultiplier.quantized H (candidate dual)) =
      (-2/3 : ℂ) * H (yukawaTargetMode dual) (rootMode dual (3,2,1)) := by
  classical
  simp only [candidate,epsilon,map_smul,map_sub,map_sum,inner_smul_right,inner_sub_right,inner_sum,
    yukawaWitness,named_triple_return,ActualMotherCAR.actual_quantized_triple_pair]
  cases dual <;> norm_num [Fin.sum_univ_succ,NamedMatterWedgeQt.colorSign,NamedMatterWedgeQt.colorPerm,
    ActualMotherCAR.tripleGram,ActualMotherCAR.delta,rootMode_eq,targetMode_ne_input,
    mul_ite,ite_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  all_goals simp +decide [yukawaTargetMode,rootMode]
  all_goals ring_nf

end LowEnergy.MixedSpectatorCandidate
