import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.Candidate
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedTransfer
noncomputable section
open CPS1Deformation CPS1ElectronicSource InnerProductSpace
open CPS1MolecularFrame.FiniteNormed
open scoped BigOperators Topology
variable {frame : CPS1Recycling.Frame}

abbrev SiteMode (source : CPS1ElectronicSource.State frame) :=
  CPS1MolecularFrame.ModeIndex source × Bool

def siteRaw (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (nuclear : CPS1MolecularFrame.NuclearIndex source) (index : SiteMode source) : SpinSpace :=
  rawJetAt source positions ((nuclear,index.1),index.2) 0

theorem site_raw_translation (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (nuclear : CPS1MolecularFrame.NuclearIndex source)
    (index : SiteMode source) :
    CPS1Following.translate (positions nuclear-sourcePositions source nuclear)
      (CPS1MolecularFrame.rawField source ((nuclear,index.1),index.2)) =
      siteRaw source positions nuclear index := by
  change CPS1Following.translate _ (PiLp.single 2 index.2 _) = PiLp.single 2 index.2 _
  rw [CPS1Following.translate,LinearIsometryEquiv.piLpCongrRight_single]
  change (PiLp.single 2 index.2
    (CPS1Following.spatialTranslate (positions nuclear-sourcePositions source nuclear)
      (orbitalField (CPS1MolecularFrame.position source nuclear) index.1.val 0)) : SpinSpace) = _
  rw [CPS1Following.spatial_translate_primitive]
  simp only [sourcePositions,sub_add_cancel]

theorem site_raw_independent (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    LinearIndependent ℂ (siteRaw source positions nuclear) := by
  have spatial : ∀ spin : Bool, LinearIndependent ℂ
      (fun mode : CPS1MolecularFrame.ModeIndex source => orbitalField (positions nuclear) mode.val 0) :=
    fun _ => orbitals_independent (positions nuclear) (spatialModes frame source.geometry.originJoint)
  have blocks : LinearIndependent ℂ (fun index : Σ _ : Bool, CPS1MolecularFrame.ModeIndex source =>
      (PiLp.single 2 index.1 (orbitalField (positions nuclear) index.2.val 0) : SpinSpace)) :=
    PiLp.linearIndependent_single (p := 2) (𝕜 := ℂ) (fun (_ : Bool) (mode : CPS1MolecularFrame.ModeIndex source) =>
      orbitalField (positions nuclear) mode.val 0) spatial
  have injective : Function.Injective (fun index : SiteMode source =>
      (⟨index.2,index.1⟩ : Σ _ : Bool, CPS1MolecularFrame.ModeIndex source)) := by
    intro left right same
    have spin := congrArg Sigma.fst same
    have mode : left.1 = right.1 := by
      cases left
      cases right
      cases same
      rfl
    exact Prod.ext mode spin
  exact blocks.comp (fun index : SiteMode source => ⟨index.2,index.1⟩) injective

def siteBasis (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (nuclear : CPS1MolecularFrame.NuclearIndex source) (index : SiteMode source) : SpinSpace :=
  gramSchmidtNormed ℂ (ordered (siteRaw source positions nuclear)) (Fintype.equivFin (SiteMode source) index)

theorem site_basis_orthonormal (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    Orthonormal ℂ (siteBasis source positions nuclear) := by
  exact (gramSchmidtNormed_orthonormal
    (CPS1PositivePulse.ordered_independent _ (site_raw_independent source positions nuclear))).comp
      (Fintype.equivFin (SiteMode source)) (Fintype.equivFin (SiteMode source)).injective

def siteSpace (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (nuclear : CPS1MolecularFrame.NuclearIndex source) : Submodule ℂ SpinSpace :=
  Submodule.span ℂ (Set.range (siteBasis source positions nuclear))

instance siteFiniteDimensional (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    FiniteDimensional ℂ (siteSpace source positions nuclear) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

instance siteComplete (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    CompleteSpace (siteSpace source positions nuclear) := FiniteDimensional.complete ℂ _

def siteProjection (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (nuclear : CPS1MolecularFrame.NuclearIndex source) : SpinSpace →L[ℂ] SpinSpace :=
  (siteSpace source positions nuclear).starProjection

private theorem finite_projection_apply {E ι : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (basis : ι → E) (orthogonal : Orthonormal ℂ basis)
    (covers : K = Submodule.span ℂ (Set.range basis)) (field : E) :
    K.starProjection field = ∑ index, inner ℂ (basis index) field • basis index := by
  let projected : E := ∑ index, inner ℂ (basis index) field • basis index
  have present : projected ∈ K := by
    rw [covers]
    apply Submodule.sum_mem
    intro index _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self index))
  have zero : K ≤ LinearMap.ker (innerSL ℂ (field-projected)).toLinearMap := by
    rw [covers]
    apply Submodule.span_le.mpr
    rintro _ ⟨index,rfl⟩
    change inner ℂ (field-projected) (basis index) = 0
    rw [inner_sub_left,orthogonal.inner_left_fintype]
    exact sub_eq_zero.mpr (inner_conj_symm (𝕜 := ℂ) field (basis index)).symm
  exact K.eq_starProjection_of_mem_of_inner_eq_zero present (fun field member => zero member)

theorem site_projection_apply (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (nuclear : CPS1MolecularFrame.NuclearIndex source)
    (field : SpinSpace) :
    siteProjection source positions nuclear field =
      ∑ index, inner ℂ (siteBasis source positions nuclear index) field •
        siteBasis source positions nuclear index := by
  exact finite_projection_apply (siteSpace source positions nuclear) (siteBasis source positions nuclear)
    (site_basis_orthonormal source positions nuclear) rfl field

theorem site_basis_span (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    siteSpace source positions nuclear = Submodule.span ℂ (Set.range (siteRaw source positions nuclear)) := by
  have range : Set.range (siteBasis source positions nuclear) =
      Set.range (gramSchmidtNormed ℂ (ordered (siteRaw source positions nuclear))) := by
    ext field
    constructor
    · rintro ⟨index,rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨index,rfl⟩
      refine ⟨(Fintype.equivFin (SiteMode source)).symm index,?_⟩
      simp only [siteBasis,Equiv.apply_symm_apply]
  rw [siteSpace,range,span_gramSchmidtNormed_range,span_gramSchmidt,range_ordered]

theorem site_basis_continuousAt {X : Type*} [TopologicalSpace X]
    (source : CPS1ElectronicSource.State frame) (positions : X → NuclearConfiguration source)
    (current : X) (continuous : ContinuousAt positions current)
    (nuclear : CPS1MolecularFrame.NuclearIndex source) (index : SiteMode source) :
    ContinuousAt (fun point => siteBasis source (positions point) nuclear index) current := by
  apply CPS1PositivePulse.canonical_normed_continuousAt
  · intro raw
    exact (raw_jet_hasFDerivAt source (positions current) ((nuclear,raw.1),raw.2) 0).continuousAt.comp continuous
  · exact site_raw_independent source (positions current) nuclear

theorem site_projection_continuousAt {X : Type*} [TopologicalSpace X]
    (source : CPS1ElectronicSource.State frame) (positions : X → NuclearConfiguration source)
    (fields : X → SpinSpace) (current : X) (positionsContinuous : ContinuousAt positions current)
    (fieldsContinuous : ContinuousAt fields current) (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    ContinuousAt (fun point => siteProjection source (positions point) nuclear (fields point)) current := by
  have same : (fun point => siteProjection source (positions point) nuclear (fields point)) =
      (fun point => ∑ index : SiteMode source,
        inner ℂ (siteBasis source (positions point) nuclear index) (fields point) •
          siteBasis source (positions point) nuclear index) := by
    funext point
    exact site_projection_apply source (positions point) nuclear (fields point)
  rw [same]
  apply tendsto_finsetSum Finset.univ
  intro index _
  exact ((site_basis_continuousAt source positions current positionsContinuous nuclear index).inner (𝕜 := ℂ)
    fieldsContinuous).smul (site_basis_continuousAt source positions current positionsContinuous nuclear index)

def phosphateAtom : CPS1EnzymeBath.Primary.Atom :=
  ⟨28,.P,0,false,"CHI_UNSPECIFIED",3,.source 28⟩

theorem phosphate_atom_source : phosphateAtom ∈ CPS1EnzymeBath.Primary.atp.atoms := by decide

theorem phosphate_bridge_source :
    (⟨25,28,1,false,"STEREONONE",0,false⟩ : CPS1EnzymeBath.Primary.Bond) ∈
      CPS1EnzymeBath.Primary.atp.bonds := by decide

structure Site (source : CPS1ElectronicSource.State frame) where
  component : CPS1EnzymeBath.Joint.Component
  atomSlot : Nat
  nuclear : CPS1MolecularFrame.NuclearIndex source

def selectSite? (source : CPS1ElectronicSource.State frame) : Option (Site source) := do
  let component ← source.geometry.originJoint.components.find? (fun current => current.kind == .atp)
  let atom ← (CPS1EnzymeBath.Joint.atoms frame source.geometry.originJoint).zipIdx.find?
    (fun row => row.1.origin == .bath component phosphateAtom)
  let nuclear ← (List.finRange source.geometry.nuclei.length).find? (fun index =>
    (CPS1MolecularFrame.nucleus source index).particle.address == .nucleus atom.2 &&
      (CPS1MolecularFrame.nucleus source index).particle.source == atom.1.descriptor)
  pure ⟨component,atom.2,nuclear⟩

end
end CPS1AddressedTransfer
