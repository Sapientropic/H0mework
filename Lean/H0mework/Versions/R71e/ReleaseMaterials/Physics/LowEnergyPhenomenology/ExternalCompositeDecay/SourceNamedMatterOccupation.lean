import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussCARHistory
import H0mework.Physics.LowEnergy.Electromagnetic.Identification.Composite
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false
noncomputable section
namespace LowEnergy.NamedMatterWedgeQt
open SaturationMonoid.PhysicsCore
open LowEnergy.Electromagnetic.Identification
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreDifferential
open SourceQuantumGaugeSliceCoordinates
open SU7ExteriorMatterRestriction DiracExteriorMatterAction
open scoped BigOperators InnerProductSpace ContDiff

abbrev NamedMode := Fin 4 × Fin 3

def rootIndex (i : NamedMode) : LowEnergy.Quantum.Index :=
  ⟨i.1, Sum.inr (Sum.inl (Composite.matterBasis i.2))⟩

def rootMode (dual : Bool) (i : NamedMode) : Mode :=
  if dual then Sum.inr (rootIndex i) else Sum.inl (rootIndex i)

theorem actual_named_mode_read (i : NamedMode) (psi : DiracExteriorMatterCarrier) :
    LowEnergy.Quantum.coordinates psi (rootIndex i) =
      (su7ExteriorBasis 2).repr (psi i.1).2.1 (Composite.matterBasis i.2) := rfl

theorem rootIndex_injective : Function.Injective rootIndex := by
  intro i j h
  have hs : i.1 = j.1 := congrArg (fun q : LowEnergy.Quantum.Index => q.1) h
  have hc : Composite.matterBasis i.2 = Composite.matterBasis j.2 := by
    simpa only [rootIndex, Sum.inr.injEq, Sum.inl.injEq] using
      (congrArg (fun q : LowEnergy.Quantum.Index => q.2) h)
  have e := congrArg Subtype.val hc
  change ({Sum.inl i.2, Sum.inr (Sum.inr (Sum.inl 0))} :
    Finset SU7MotherLieAlgebra.SU7MotherIndex) =
    {Sum.inl j.2, Sum.inr (Sum.inr (Sum.inl 0))} at e
  have hm : Sum.inl i.2 ∈ ({Sum.inl j.2, Sum.inr (Sum.inr (Sum.inl 0))} :
      Finset SU7MotherLieAlgebra.SU7MotherIndex) := by rw [← e]; simp
  have hi : i.2 = j.2 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      Sum.inl_ne_inr, or_false] using hm
  exact Prod.ext hs hi

def modeEmbedding (dual : Bool) : NamedMode ↪ Mode where
  toFun := rootMode dual
  inj' := by
    intro i j h
    cases dual <;> apply rootIndex_injective <;> simpa [rootMode] using h

def occupation (dual : Bool) (w : Finset NamedMode) : Occupation :=
  w.map (modeEmbedding dual)

theorem occupation_card (dual : Bool) (w : Finset NamedMode) :
    (occupation dual w).card = w.card := Finset.card_map _

theorem occupation_injective (dual : Bool) : Function.Injective (occupation dual) :=
  Finset.map_injective (modeEmbedding dual)

abbrev WedgeIndex := {w : Finset NamedMode // w.card = 3}

theorem actual_wedge_card : Fintype.card WedgeIndex = 220 := by
  classical
  change Fintype.card {w : Finset NamedMode // w.card = 3} = 220
  rw [Fintype.card_of_subtype (Finset.powersetCard 3 (Finset.univ : Finset NamedMode))
    (by intro w; simp), Finset.card_powersetCard]
  norm_num [Fintype.card_prod]
  decide

def fiberBasis (dual : Bool) (w : WedgeIndex) : FockFiber :=
  EuclideanSpace.single (occupation dual w.val) 1

theorem actual_fiber_pair (dual : Bool) (w v : WedgeIndex) :
    inner ℂ (fiberBasis dual w) (fiberBasis dual v) = if w = v then 1 else 0 := by
  classical
  by_cases h : w = v
  · subst v
    simp [fiberBasis]
  · have ho : occupation dual v.val ≠ occupation dual w.val := by
      intro he
      exact h (Subtype.ext (occupation_injective dual he).symm)
    simp [fiberBasis, EuclideanSpace.inner_single_left, ho, h]

def profileTest (dual : Bool) (w : WedgeIndex)
    (f : GaussDensityCore.ScalarTest) : QuantumTest :=
  ⟨fun z => f z • fiberBasis dual w,
    f.contDiff.smul contDiff_const,
    f.hasCompactSupport.smul_right,
    (tsupport_smul_subset_left _ _).trans f.tsupport_subset⟩

theorem actual_source_profile (dual : Bool) (w : WedgeIndex)
    (f : GaussDensityCore.ScalarTest) (z : SourceCoordinateSlice) :
    profileTest dual w f z = f z • fiberBasis dual w := rfl

end LowEnergy.NamedMatterWedgeQt
