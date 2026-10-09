import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterWedgeCarrier
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.NamedMatterWedgeQt
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

def namedCode (i : NamedMode) : ℕ := 3 * i.1.val + i.2.val

theorem namedCode_injective : Function.Injective namedCode := by
  intro i j h
  have hi := i.2.isLt
  have hj := j.2.isLt
  have he : i.1.val = j.1.val ∧ i.2.val = j.2.val := by
    simp only [namedCode] at h
    omega
  exact Prod.ext (Fin.ext he.1) (Fin.ext he.2)

abbrev namedOrder : LinearOrder NamedMode := LinearOrder.lift' namedCode namedCode_injective
attribute [local instance] namedOrder

def tripleIndex (w : WedgeIndex) : Fin 3 ↪ NamedMode :=
  (w.val.orderEmbOfFin w.property).toEmbedding

theorem tripleIndex_set (w : WedgeIndex) :
    {tripleIndex w 0, tripleIndex w 1, tripleIndex w 2} = w.val := by
  have h := Finset.image_orderEmbOfFin_univ w.val w.property
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have he := h
  rw [hu] at he
  apply Finset.ext
  intro i
  have hm := congrArg (fun s : Finset NamedMode => i ∈ s) he
  simpa [tripleIndex, eq_comm] using (eq_iff_iff.mp hm)

def sourcePhase (dual : Bool) (w : WedgeIndex) : ℂ :=
  sign (rootMode dual (tripleIndex w 1)) {rootMode dual (tripleIndex w 2)} *
    sign (rootMode dual (tripleIndex w 0))
      {rootMode dual (tripleIndex w 1), rootMode dual (tripleIndex w 2)}

theorem actual_source_phase_square (dual : Bool) (w : WedgeIndex) :
    sourcePhase dual w * sourcePhase dual w = 1 := by
  unfold sourcePhase
  calc
    _ = (sign (rootMode dual (tripleIndex w 1)) {rootMode dual (tripleIndex w 2)} *
        sign (rootMode dual (tripleIndex w 1)) {rootMode dual (tripleIndex w 2)}) *
      (sign (rootMode dual (tripleIndex w 0))
        {rootMode dual (tripleIndex w 1), rootMode dual (tripleIndex w 2)} *
       sign (rootMode dual (tripleIndex w 0))
        {rootMode dual (tripleIndex w 1), rootMode dual (tripleIndex w 2)}) := by ring
    _ = 1 := by rw [QuantizationCheck.Fermion.sign_mul_self,
      QuantizationCheck.Fermion.sign_mul_self, mul_one]

theorem actual_source_phase_star (dual : Bool) (w : WedgeIndex) :
    star (sourcePhase dual w) = sourcePhase dual w := by
  simp only [sourcePhase, star_mul, LowEnergy.Fermion.star_sign]
  ring

def namedCARBasis (dual : Bool) (w : WedgeIndex) : FockFiber :=
  orderedTriple dual (tripleIndex w 0) (tripleIndex w 1) (tripleIndex w 2)

theorem actual_named_CAR_basis (dual : Bool) (w : WedgeIndex) :
    namedCARBasis dual w = sourcePhase dual w • fiberBasis dual w := by
  rw [namedCARBasis, actual_ordered_triple]
  · rw [tripleIndex_set]
    change sourcePhase dual w • occupationFiber dual w.val = sourcePhase dual w • fiberBasis dual w
    congr 1
    apply PiLp.ext
    intro v
    simp [occupationFiber, fiberBasis, EuclideanSpace.single]
  all_goals
    exact (tripleIndex w).injective.ne (by decide)

theorem actual_named_CAR_pair (dual : Bool) (w v : WedgeIndex) :
    inner ℂ (namedCARBasis dual w) (namedCARBasis dual v) = if w = v then 1 else 0 := by
  classical
  rw [actual_named_CAR_basis, actual_named_CAR_basis, inner_smul_left, inner_smul_right,
    actual_fiber_pair]
  by_cases h : w = v
  · subst v
    simp only [ite_true, mul_one, starRingEnd_apply, actual_source_phase_star]
    exact actual_source_phase_square dual w
  · simp [h]

end LowEnergy.NamedMatterWedgeQt
