import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteOrdinary.Pointer
set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Evaluate
open scoped Matrix BigOperators
noncomputable section

def ordinaryLoadFullQ (a b : Basis) (ordered : a < b) :
    MatrixQ OrdinaryFull OrdinaryFull :=
  roleBlocksQ
    (bodyLiftQ (ordinaryLoadQ a b ordered) (oneDiagonalQ 97))
    (donorLiftQ (diagonalLoadQ 97) (onePCQ a b ordered))

def ordinaryWeakFullQ (a b : Basis) (ordered : a < b) :
    MatrixQ OrdinaryFull OrdinaryFull :=
  roleMixQ SquareRoot.Full.sine SquareRoot.Full.cosine
    (qkron (qkron (onePCQ a b ordered) (oneDiagonalQ 97)) freeEnvironmentQ)

theorem ordinary_load_full_source (a b : Basis) (ordered : a < b) :
    Spec.load.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      ordinaryLoadFullQ a b ordered := ordinary_load_source a b ordered

theorem ordinary_weak_full_source (a b : Basis) (ordered : a < b) :
    Spec.weak.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      ordinaryWeakFullQ a b ordered := ordinary_weak_restriction a b ordered

def ordinaryPointerPulseQ (A B : MatrixQ OrdinaryFull OrdinaryFull) :
    MatrixQ (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull) :=
  Matrix.fromBlocks A 0 0 (qscale phaseQ B)

private theorem pointer_pulse_restrict (a b : Basis) (ordered : a < b)
    (A B : MatrixQ Current.FullIndex Current.FullIndex)
    (A' B' : MatrixQ OrdinaryFull OrdinaryFull)
    (ha : A.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=A')
    (hb : B.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=B') :
    (Matrix.fromBlocks A 0 0 (qscale phaseQ B)).submatrix
      (ordinaryPointerAddress a b ordered) (ordinaryPointerAddress a b ordered)=
      ordinaryPointerPulseQ A' B' := by
  funext i j
  rcases i with (i | i) <;> rcases j with (j | j)
  all_goals simp only [ordinaryPointerAddress,ordinaryPointerPulseQ,Matrix.submatrix_apply,
    Matrix.fromBlocks]
  · exact congrFun (congrFun ha i) j
  · rfl
  · rfl
  · exact congrArg (Scalar.multiply phaseQ) (congrFun (congrFun hb i) j)

def ordinaryPointerLoadQ (a b : Basis) (ordered : a < b) :=
  ordinaryPointerPulseQ (ordinaryLoadFullQ a b ordered) (ordinaryLoadFullQ a b ordered)

def ordinaryPointerSupplyQ (a b : Basis) (ordered : a < b) :=
  ordinaryPointerPulseQ (ordinaryLoadFullQ a b ordered) (ordinarySupplyQ a b ordered)

def ordinaryPointerWeakQ (a b : Basis) (ordered : a < b) :=
  ordinaryPointerPulseQ (ordinaryLoadFullQ a b ordered) (ordinaryWeakFullQ a b ordered)

theorem ordinary_pointer_load_source (a b : Basis) (ordered : a < b) :
    Spec.pointerLoad.submatrix (ordinaryPointerAddress a b ordered)
      (ordinaryPointerAddress a b ordered)=ordinaryPointerLoadQ a b ordered := by
  exact pointer_pulse_restrict a b ordered _ _ _ _
    (ordinary_load_full_source a b ordered) (ordinary_load_full_source a b ordered)

theorem ordinary_pointer_supply_source (a b : Basis) (ordered : a < b) :
    Spec.pointerSupply.submatrix (ordinaryPointerAddress a b ordered)
      (ordinaryPointerAddress a b ordered)=ordinaryPointerSupplyQ a b ordered := by
  exact pointer_pulse_restrict a b ordered _ _ _ _
    (ordinary_load_full_source a b ordered) (ordinary_supply_restriction a b ordered)

theorem ordinary_pointer_weak_source (a b : Basis) (ordered : a < b) :
    Spec.pointerWeak.submatrix (ordinaryPointerAddress a b ordered)
      (ordinaryPointerAddress a b ordered)=ordinaryPointerWeakQ a b ordered := by
  exact pointer_pulse_restrict a b ordered _ _ _ _
    (ordinary_load_full_source a b ordered) (ordinary_weak_full_source a b ordered)

theorem ordinary_pointer_load_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryPointerLoadQ a b ordered)=
      coordinateLoad (s(a,b)) (ordinaryFullEquiv a b ordered.ne) := by
  rw [← ordinary_pointer_load_source,qvalue_submatrix,Spec.pointerLoad_value]
  rfl

theorem ordinary_pointer_supply_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryPointerSupplyQ a b ordered)=
      coordinateSupply (s(a,b)) (ordinaryFullEquiv a b ordered.ne) := by
  rw [← ordinary_pointer_supply_source,qvalue_submatrix,Spec.pointerSupply_value]
  rfl

theorem ordinary_pointer_weak_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryPointerWeakQ a b ordered)=
      coordinateWeak (s(a,b)) (ordinaryFullEquiv a b ordered.ne) := by
  rw [← ordinary_pointer_weak_source,qvalue_submatrix,Spec.pointerWeak_value]
  rfl

def ordinaryEntranceQ (a b : Basis) (ordered : a < b) :
    MatrixQ (OrdinaryFull ⊕ OrdinaryFull) ((Fin 2 × Fin 2) × Fin 2) :=
  qmultiply (ordinarySourceColumnsQ a b ordered) (ordinaryReceivedQ a b ordered)

theorem ordinary_entrance_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryEntranceQ a b ordered)=
      entranceColumns (s(a,b)) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
        (ordinaryFullEquiv a b ordered.ne) ordinaryInjection := by
  rw [ordinaryEntranceQ,qvalue_multiply,ordinary_source_columns_value,
    ordinaryReceivedQ_value]
  change sourceColumns (s(a,b)) (ordinaryFullEquiv a b ordered.ne) ordinaryInjection *
      LoadExecution.receivedWord.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b) =
    sourceColumns (s(a,b)) (ordinaryFullEquiv a b ordered.ne) ordinaryInjection *
      (localReceivedWord (s(a,b))).submatrix (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
        (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
  have same : LoadExecution.receivedWord.submatrix (Scaled.Order.orbitPCE a b)
      (Scaled.Order.orbitPCE a b) =
      (localReceivedWord (s(a,b))).submatrix (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
        (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne) := by
    simp only [localReceivedWord,restrict,Matrix.submatrix_submatrix]
    have address : (Subtype.val ∘ (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne :
        ((Fin 2 × Fin 2) × Fin 2) ≃ BodyFiber (s(a,b))))=
        Scaled.Order.orbitPCE a b := rfl
    rw [address]
  exact congrArg (fun M => sourceColumns (s(a,b))
    (ordinaryFullEquiv a b ordered.ne) ordinaryInjection * M) same

def ordinaryNineColumnsQ (a b : Basis) (ordered : a < b) :
    MatrixQ (OrdinaryFull ⊕ OrdinaryFull) ((Fin 2 × Fin 2) × Fin 2) :=
  qmultiply (ordinaryPointerLoadQ a b ordered)
    (qmultiply (ordinaryPointerSupplyQ a b ordered)
      (qmultiply (ordinaryPointerSupplyQ a b ordered) (ordinaryEntranceQ a b ordered)))

theorem ordinary_nine_columns_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryNineColumnsQ a b ordered)=
      nineColumns (s(a,b)) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
        (ordinaryFullEquiv a b ordered.ne) ordinaryInjection := by
  simp only [ordinaryNineColumnsQ,qvalue_multiply,ordinary_pointer_load_value,
    ordinary_pointer_supply_value,ordinary_entrance_value]
  rfl

def ordinaryElevenColumnsQ (a b : Basis) (ordered : a < b) :
    MatrixQ (OrdinaryFull ⊕ OrdinaryFull) ((Fin 2 × Fin 2) × Fin 2) :=
  qmultiply (ordinaryPointerLoadQ a b ordered)
    (qmultiply (ordinaryPointerWeakQ a b ordered) (ordinaryNineColumnsQ a b ordered))

theorem ordinary_eleven_columns_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryElevenColumnsQ a b ordered)=
      elevenColumns (s(a,b)) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
        (ordinaryFullEquiv a b ordered.ne) ordinaryInjection := by
  simp only [ordinaryElevenColumnsQ,qvalue_multiply,ordinary_pointer_load_value,
    ordinary_pointer_weak_value,ordinary_nine_columns_value]
  rfl


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
