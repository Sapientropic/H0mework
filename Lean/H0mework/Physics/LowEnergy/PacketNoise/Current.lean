import H0mework.Physics.LowEnergy.PacketNoise.Hamiltonian
import H0mework.Physics.LowEnergy.PacketNoise.Modulation

/-! The original coframe current is defined on the source generator domain.
Its adjoint term acts on the complete product M_h Kf, retaining the derivative of the cosine. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace HistoryGenerator GaugeHistory Stage9C.Material.SpinPair
noncomputable section
attribute [local irreducible] freeAction chiral yukawaOperator

theorem boundary_cosine_commute (shift : Position) (field : FullMatterL2) :
    boundaryAction (cosineShift shift field)=cosineShift shift (boundaryAction field) := by
  apply Lp.ext
  filter_upwards [chiral.coeFn_compLpL (cosineShift shift field),cosineShift_position shift field,
    cosineShift_position shift (boundaryAction field),chiral.coeFn_compLpL field]
    with x boundaryCos cosineField cosineBoundary boundaryField
  change boundaryAction (cosineShift shift field) x=chiral (cosineShift shift field x) at boundaryCos
  change boundaryAction field x=chiral (field x) at boundaryField
  rw [boundaryCos,cosineField,cosineBoundary,boundaryField,map_smul]

theorem cosine_symmetric (shift : Position) (left right : FullMatterL2) :
    inner ℂ (cosineShift shift left) right=inner ℂ left (cosineShift shift right) := by
  have self : (cosineShift shift).adjoint=cosineShift shift := cosineShift_selfAdjoint shift
  simpa only [self] using ContinuousLinearMap.adjoint_inner_left (cosineShift shift) right left

def boundaryDomainLinear : Quantum.Generator.domain freeAction →ₗ[ℂ] Quantum.Generator.domain freeAction where
  toFun := boundaryDomain
  map_add' first second := Subtype.ext (map_add boundaryAction first.val second.val)
  map_smul' c field := Subtype.ext (map_smul boundaryAction c field.val)

def cosineDomainLinear (shift : Position) : Quantum.Generator.domain freeAction →ₗ[ℂ] Quantum.Generator.domain freeAction where
  toFun := cosineDomain shift
  map_add' first second := Subtype.ext (map_add (cosineShift shift) first.val second.val)
  map_smul' c field := Subtype.ext (map_smul (cosineShift shift) c field.val)

def sourceHamiltonianLinear : Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  Quantum.Generator.hamiltonian freeAction+yukawaOperator.toLinearMap.comp (Quantum.Generator.domain freeAction).subtype

def conjugateHamiltonianLinear : Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  Quantum.Generator.hamiltonian freeAction+yukawaOperator.adjoint.toLinearMap.comp (Quantum.Generator.domain freeAction).subtype

theorem sourceHamiltonianLinear_apply (field : Quantum.Generator.domain freeAction) :
    sourceHamiltonianLinear field=sourceHamiltonian field := rfl

theorem conjugateHamiltonianLinear_apply (field : Quantum.Generator.domain freeAction) :
    conjugateHamiltonianLinear field=conjugateHamiltonian field := rfl

def currentLinear (shift : Position) : Quantum.Generator.domain freeAction →ₗ[ℂ] FullMatterL2 :=
  (((lapse^2)⁻¹ : ℝ) : ℂ) •
    ((boundaryAction.toLinearMap.comp (cosineShift shift).toLinearMap).comp sourceHamiltonianLinear+
      conjugateHamiltonianLinear.comp ((cosineDomainLinear shift).comp boundaryDomainLinear))

def currentField (shift : Position) (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  currentLinear shift field

theorem currentField_apply (shift : Position) (field : Quantum.Generator.domain freeAction) :
    currentField shift field=(((lapse^2)⁻¹ : ℝ) : ℂ) •
      (boundaryAction (cosineShift shift (sourceHamiltonian field))+
        conjugateHamiltonian (cosineDomain shift (boundaryDomain field))) := rfl

theorem currentField_add (shift : Position) (first second : Quantum.Generator.domain freeAction) :
    currentField shift (first+second)=currentField shift first+currentField shift second := map_add _ _ _

theorem currentField_smul (shift : Position) (c : ℂ) (field : Quantum.Generator.domain freeAction) :
    currentField shift (c • field)=c • currentField shift field := map_smul _ _ _

theorem conjugateHamiltonian_pair (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (conjugateHamiltonian left) right.val=inner ℂ left.val (sourceHamiltonian right) := by
  have generated := congrArg (starRingEnd ℂ) (sourceHamiltonian_pair right left)
  simpa only [inner_conj_symm] using generated.symm

theorem currentField_pair (shift : Position) (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (currentField shift left) right.val=inner ℂ left.val (currentField shift right) := by
  simp only [currentField_apply,inner_smul_left,inner_smul_right,inner_add_left,inner_add_right]
  have real : (starRingEnd ℂ) (((lapse^2)⁻¹ : ℝ) : ℂ)=(((lapse^2)⁻¹ : ℝ) : ℂ) := by simp
  rw [real]
  congr 1
  rw [boundaryAction_symmetric,cosine_symmetric]
  have first := sourceHamiltonian_pair left (cosineDomain shift (boundaryDomain right))
  change inner ℂ (sourceHamiltonian left) (cosineShift shift (boundaryAction right.val))=
    inner ℂ left.val (conjugateHamiltonian (cosineDomain shift (boundaryDomain right))) at first
  rw [first,conjugateHamiltonian_pair]
  change inner ℂ left.val (conjugateHamiltonian (cosineDomain shift (boundaryDomain right)))+
      inner ℂ (cosineShift shift (boundaryAction left.val)) (sourceHamiltonian right)=_
  rw [cosine_symmetric,boundaryAction_symmetric]
  exact add_comm _ _

def currentMean (shift : Position) (field : Quantum.Generator.domain freeAction) : ℂ :=
  inner ℂ field.val (currentField shift field)

theorem currentMean_real (shift : Position) (field : Quantum.Generator.domain freeAction) :
    star (currentMean shift field)=currentMean shift field := by
  change (starRingEnd ℂ) (inner ℂ field.val (currentField shift field))=inner ℂ field.val (currentField shift field)
  rw [inner_conj_symm,currentField_pair]

theorem currentMean_im (shift : Position) (field : Quantum.Generator.domain freeAction) :
    (currentMean shift field).im=0 := Complex.conj_eq_iff_im.mp (currentMean_real shift field)

theorem currentMean_re_cast (shift : Position) (field : Quantum.Generator.domain freeAction) :
    ((currentMean shift field).re : ℂ)=currentMean shift field := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im,currentMean_im]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
