import H0mework.Realization.MappingCone.HomotopyFunctoriality

/-!
# Total-fibre symmetry for a homotopy-commutative cochain square

A homotopy-commutative square has two iterated mapping-cocone constructions:
first across its rows and then down, or first down its columns and then
across.  They are canonically isomorphic as cochain complexes.  Degreewise
the isomorphism fixes the upper-left coordinate, exchanges the two edge
coordinates, and negates the lower-right coordinate.

The construction consumes only the four actual arrows and their actual
homotopy.  It does not accept a quasi-isomorphism, acyclicity receipt,
derived comparison, finite model, or domain-specific compatibility law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace CochainMappingCoconeTotalFiberSymmetry

open CategoryTheory
open CochainComplex.HomComplex
open CochainMappingCoconeDegreewiseKernel
open CochainMappingCoconeHomotopyFunctoriality

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Limits.HasBinaryBiproducts C]
variable {A B C' D : CochainComplex C ℤ}

variable (horizontalSource : A ⟶ B) (horizontalTarget : C' ⟶ D)
variable (verticalLeft : A ⟶ C') (verticalRight : B ⟶ D)
variable (square : Homotopy
  (verticalLeft ≫ horizontalTarget)
  (horizontalSource ≫ verticalRight))

set_option backward.isDefEq.respectTransparency false in
theorem mappingCocone_delta_snd
    {K L : CochainComplex C ℤ} (phi : K ⟶ L) :
    δ (-1) 0 (CochainComplex.mappingCocone.snd phi) +
      Cochain.ofHom (CochainComplex.mappingCocone.fst phi ≫ phi) = 0 := by
  unfold CochainComplex.mappingCocone.snd
  rw [Cochain.δ_leftShift
    (CochainComplex.mappingCone.snd phi) (-1) (-1) 0
      (zero_add (-1)) 1 (by omega)]
  rw [CochainComplex.mappingCone.δ_snd]
  simp [CochainComplex.mappingCocone.fst,
    Cochain.ofHom_comp]

@[reassoc] theorem mappingCocone_d_snd
    {K L : CochainComplex C ℤ} (phi : K ⟶ L)
    (source target : ℤ) (related : source + 1 = target) :
    (CochainComplex.mappingCocone phi).d source target ≫
        (CochainComplex.mappingCocone.snd phi).v target source (by omega) =
      -((CochainComplex.mappingCocone.fst phi).f source ≫ phi.f source) -
        (CochainComplex.mappingCocone.snd phi).v
          source (source + (-1)) rfl ≫ L.d (source + (-1)) source := by
  have generated := Cochain.congr_v (mappingCocone_delta_snd phi)
    source source (add_zero source)
  simp only [Cochain.add_v, Cochain.ofHom_v, HomologicalComplex.comp_f,
    Cochain.zero_v] at generated
  rw [δ_v (-1) 0 (by omega)
    (CochainComplex.mappingCocone.snd phi)
    source source (add_zero source)
    (source + (-1)) target rfl related] at generated
  rw [show Int.negOnePow 0 = 1 by rfl, one_smul] at generated
  rw [add_eq_zero_iff_eq_neg] at generated
  rw [← generated]
  abel

noncomputable def horizontalMap :
    CochainComplex.mappingCocone horizontalSource ⟶
      CochainComplex.mappingCocone horizontalTarget :=
  mappingCoconeMap horizontalSource horizontalTarget
    verticalLeft verticalRight square

noncomputable def verticalMap :
    CochainComplex.mappingCocone verticalLeft ⟶
      CochainComplex.mappingCocone verticalRight :=
  mappingCoconeMap verticalLeft verticalRight
    horizontalSource horizontalTarget square.symm

abbrev HorizontalTotal :=
  CochainComplex.mappingCocone
    (horizontalMap horizontalSource horizontalTarget verticalLeft verticalRight square)

abbrev VerticalTotal :=
  CochainComplex.mappingCocone
    (verticalMap horizontalSource horizontalTarget verticalLeft verticalRight square)

noncomputable def transposeComponent (degree : ℤ) :
    (HorizontalTotal horizontalSource horizontalTarget verticalLeft verticalRight square).X degree ⟶
      (VerticalTotal horizontalSource horizontalTarget verticalLeft verticalRight square).X degree :=
  let horizontal := horizontalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let vertical := verticalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let previous := degree + (-1)
  let previousPrevious := previous + (-1)
  let outerSource := CochainComplex.mappingCocone.fst horizontal
  let outerTarget := CochainComplex.mappingCocone.snd horizontal
  let sourceCoordinate := degreeLift verticalLeft degree
    (outerSource.f degree ≫
      (CochainComplex.mappingCocone.fst horizontalSource).f degree)
    (outerTarget.v degree previous rfl ≫
      (CochainComplex.mappingCocone.fst horizontalTarget).f previous)
  let targetCoordinate := degreeLift verticalRight previous
    (outerSource.f degree ≫
      (CochainComplex.mappingCocone.snd horizontalSource).v
        degree previous rfl)
    (-(outerTarget.v degree previous rfl ≫
      (CochainComplex.mappingCocone.snd horizontalTarget).v
        previous previousPrevious rfl))
  degreeLift vertical degree sourceCoordinate targetCoordinate

noncomputable def untransposeComponent (degree : ℤ) :
    (VerticalTotal horizontalSource horizontalTarget verticalLeft verticalRight square).X degree ⟶
      (HorizontalTotal horizontalSource horizontalTarget verticalLeft verticalRight square).X degree :=
  let horizontal := horizontalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let vertical := verticalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let previous := degree + (-1)
  let previousPrevious := previous + (-1)
  let outerSource := CochainComplex.mappingCocone.fst vertical
  let outerTarget := CochainComplex.mappingCocone.snd vertical
  let sourceCoordinate := degreeLift horizontalSource degree
    (outerSource.f degree ≫
      (CochainComplex.mappingCocone.fst verticalLeft).f degree)
    (outerTarget.v degree previous rfl ≫
      (CochainComplex.mappingCocone.fst verticalRight).f previous)
  let targetCoordinate := degreeLift horizontalTarget previous
    (outerSource.f degree ≫
      (CochainComplex.mappingCocone.snd verticalLeft).v
        degree previous rfl)
    (-(outerTarget.v degree previous rfl ≫
      (CochainComplex.mappingCocone.snd verticalRight).v
        previous previousPrevious rfl))
  degreeLift horizontal degree sourceCoordinate targetCoordinate

@[reassoc (attr := simp)] theorem transposeComponent_A
    (degree : ℤ) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square degree ≫
      (CochainComplex.mappingCocone.fst
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f degree ≫
      (CochainComplex.mappingCocone.fst verticalLeft).f degree =
    (CochainComplex.mappingCocone.fst
        (horizontalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f degree ≫
      (CochainComplex.mappingCocone.fst horizontalSource).f degree := by
  simp [transposeComponent]

@[reassoc (attr := simp)] theorem transposeComponent_C
    (degree : ℤ) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square degree ≫
      (CochainComplex.mappingCocone.fst
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f degree ≫
      (CochainComplex.mappingCocone.snd verticalLeft).v
        degree (degree + (-1)) rfl =
    (CochainComplex.mappingCocone.snd
        (horizontalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v degree (degree + (-1)) rfl ≫
      (CochainComplex.mappingCocone.fst horizontalTarget).f
        (degree + (-1)) := by
  simp [transposeComponent]

@[reassoc] theorem transposeComponent_C_at
    (degree previous : ℤ) (degree_previous : degree + (-1) = previous) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square degree ≫
      (CochainComplex.mappingCocone.fst
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f degree ≫
      (CochainComplex.mappingCocone.snd verticalLeft).v
        degree previous degree_previous =
    (CochainComplex.mappingCocone.snd
        (horizontalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v degree previous degree_previous ≫
      (CochainComplex.mappingCocone.fst horizontalTarget).f previous := by
  subst previous
  exact transposeComponent_C horizontalSource horizontalTarget verticalLeft
    verticalRight square degree

@[reassoc (attr := simp)] theorem transposeComponent_B
    (degree : ℤ) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square degree ≫
      (CochainComplex.mappingCocone.snd
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v degree (degree + (-1)) rfl ≫
      (CochainComplex.mappingCocone.fst verticalRight).f
        (degree + (-1)) =
    (CochainComplex.mappingCocone.fst
        (horizontalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f degree ≫
      (CochainComplex.mappingCocone.snd horizontalSource).v
        degree (degree + (-1)) rfl := by
  simp [transposeComponent]

@[reassoc] theorem transposeComponent_B_at
    (degree previous : ℤ) (degree_previous : degree + (-1) = previous) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square degree ≫
      (CochainComplex.mappingCocone.snd
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v degree previous degree_previous ≫
      (CochainComplex.mappingCocone.fst verticalRight).f previous =
    (CochainComplex.mappingCocone.fst
        (horizontalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f degree ≫
      (CochainComplex.mappingCocone.snd horizontalSource).v
        degree previous degree_previous := by
  subst previous
  exact transposeComponent_B horizontalSource horizontalTarget verticalLeft
    verticalRight square degree

@[reassoc (attr := simp)] theorem transposeComponent_D
    (degree : ℤ) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square degree ≫
      (CochainComplex.mappingCocone.snd
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v degree (degree + (-1)) rfl ≫
      (CochainComplex.mappingCocone.snd verticalRight).v
        (degree + (-1)) (degree + (-1) + (-1)) rfl =
    -((CochainComplex.mappingCocone.snd
        (horizontalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v degree (degree + (-1)) rfl ≫
      (CochainComplex.mappingCocone.snd horizontalTarget).v
        (degree + (-1)) (degree + (-1) + (-1)) rfl) := by
  simp [transposeComponent]

@[reassoc] theorem transposeComponent_D_at
    (degree previous previousPrevious : ℤ)
    (degree_previous : degree + (-1) = previous)
    (previous_previous : previous + (-1) = previousPrevious) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square degree ≫
      (CochainComplex.mappingCocone.snd
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v degree previous degree_previous ≫
      (CochainComplex.mappingCocone.snd verticalRight).v
        previous previousPrevious previous_previous =
    -((CochainComplex.mappingCocone.snd
        (horizontalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v degree previous degree_previous ≫
      (CochainComplex.mappingCocone.snd horizontalTarget).v
        previous previousPrevious previous_previous) := by
  subst previousPrevious
  subst previous
  exact transposeComponent_D horizontalSource horizontalTarget verticalLeft
    verticalRight square degree

noncomputable def componentIso (degree : ℤ) :
    (HorizontalTotal horizontalSource horizontalTarget verticalLeft verticalRight square).X degree ≅
      (VerticalTotal horizontalSource horizontalTarget verticalLeft verticalRight square).X degree where
  hom := transposeComponent horizontalSource horizontalTarget verticalLeft verticalRight square degree
  inv := untransposeComponent horizontalSource horizontalTarget verticalLeft verticalRight square degree
  hom_inv_id := by
    apply degree_hom_ext
      (horizontalMap horizontalSource horizontalTarget verticalLeft verticalRight square) degree
    · apply degree_hom_ext horizontalSource degree <;>
        simp [transposeComponent, untransposeComponent, Category.assoc]
    · apply degree_hom_ext horizontalTarget (degree + (-1)) <;>
        simp [transposeComponent, untransposeComponent, Category.assoc]
  inv_hom_id := by
    apply degree_hom_ext
      (verticalMap horizontalSource horizontalTarget verticalLeft verticalRight square) degree
    · apply degree_hom_ext verticalLeft degree <;>
        simp [transposeComponent, untransposeComponent, Category.assoc]
    · apply degree_hom_ext verticalRight (degree + (-1)) <;>
        simp [transposeComponent, untransposeComponent, Category.assoc]

theorem transposeComponent_A_comm
    (source target : ℤ) (_related : (ComplexShape.up ℤ).Rel source target) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square source ≫
      (VerticalTotal horizontalSource horizontalTarget verticalLeft
        verticalRight square).d source target ≫
      (CochainComplex.mappingCocone.fst
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f target ≫
      (CochainComplex.mappingCocone.fst verticalLeft).f target =
    (HorizontalTotal horizontalSource horizontalTarget verticalLeft
        verticalRight square).d source target ≫
      transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square target ≫
      (CochainComplex.mappingCocone.fst
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f target ≫
      (CochainComplex.mappingCocone.fst verticalLeft).f target := by
  let horizontal := horizontalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let vertical := verticalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  calc
    _ = (CochainComplex.mappingCocone.fst horizontal).f source ≫
          (CochainComplex.mappingCocone.fst horizontalSource).f source ≫
          A.d source target := by
      rw [← (CochainComplex.mappingCocone.fst vertical).comm_assoc,
        ← (CochainComplex.mappingCocone.fst verticalLeft).comm,
        transposeComponent_A_assoc]
    _ = (HorizontalTotal horizontalSource horizontalTarget verticalLeft
          verticalRight square).d source target ≫
        (CochainComplex.mappingCocone.fst horizontal).f target ≫
        (CochainComplex.mappingCocone.fst horizontalSource).f target := by
      rw [(CochainComplex.mappingCocone.fst horizontalSource).comm,
        (CochainComplex.mappingCocone.fst horizontal).comm_assoc]
    _ = _ := by
      have generated := congrArg
        (fun arrow =>
          (HorizontalTotal horizontalSource horizontalTarget verticalLeft
            verticalRight square).d source target ≫ arrow)
        (transposeComponent_A horizontalSource horizontalTarget verticalLeft
          verticalRight square target).symm
      simpa only [horizontal, vertical, Category.assoc] using generated

theorem transposeComponent_C_comm
    (source target : ℤ) (related : (ComplexShape.up ℤ).Rel source target) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square source ≫
      (VerticalTotal horizontalSource horizontalTarget verticalLeft
        verticalRight square).d source target ≫
      (CochainComplex.mappingCocone.fst
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f target ≫
      (CochainComplex.mappingCocone.snd verticalLeft).v
        target source (by
          have relation : source + 1 = target := related
          omega) =
    (HorizontalTotal horizontalSource horizontalTarget verticalLeft
        verticalRight square).d source target ≫
      transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square target ≫
      (CochainComplex.mappingCocone.fst
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).f target ≫
      (CochainComplex.mappingCocone.snd verticalLeft).v
        target source (by
          have relation : source + 1 = target := related
          omega) := by
  have related_eq : source + 1 = target := related
  let horizontal := horizontalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let vertical := verticalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let common :=
    -((CochainComplex.mappingCocone.fst horizontal).f source ≫
        (CochainComplex.mappingCocone.fst horizontalSource).f source ≫
        verticalLeft.f source) -
      (CochainComplex.mappingCocone.snd horizontal).v
          source (source + (-1)) rfl ≫
        (CochainComplex.mappingCocone.fst horizontalTarget).f
          (source + (-1)) ≫ C'.d (source + (-1)) source
  calc
    _ = common := by
      rw [← (CochainComplex.mappingCocone.fst vertical).comm_assoc,
        mappingCocone_d_snd verticalLeft source target related_eq]
      simp only [Preadditive.comp_sub, Preadditive.comp_neg]
      rw [transposeComponent_A_assoc, transposeComponent_C_assoc]
    _ = _ := by
      have transposeTarget :
          transposeComponent horizontalSource horizontalTarget verticalLeft
              verticalRight square target ≫
            (CochainComplex.mappingCocone.fst vertical).f target ≫
            (CochainComplex.mappingCocone.snd verticalLeft).v
              target source (by omega) =
          (CochainComplex.mappingCocone.snd horizontal).v
              target source (by omega) ≫
            (CochainComplex.mappingCocone.fst horizontalTarget).f source := by
        exact transposeComponent_C_at horizontalSource horizontalTarget
          verticalLeft verticalRight square target source (by omega)
      have targetCoordinate := congrArg
        (fun arrow =>
          (HorizontalTotal horizontalSource horizontalTarget verticalLeft
            verticalRight square).d source target ≫ arrow)
        transposeTarget.symm
      rw [← targetCoordinate]
      rw [← Category.assoc,
        mappingCocone_d_snd horizontal source target related_eq]
      simp only [Preadditive.sub_comp, Preadditive.neg_comp,
        Category.assoc]
      have horizontalFst := congrArg (fun arrow => arrow.f source)
        (mappingCoconeMap_fst horizontalSource horizontalTarget
          verticalLeft verticalRight square)
      change horizontal.f source ≫
          (CochainComplex.mappingCocone.fst horizontalTarget).f source =
        (CochainComplex.mappingCocone.fst horizontalSource).f source ≫
          verticalLeft.f source at horizontalFst
      rw [horizontalFst]
      rw [← (CochainComplex.mappingCocone.fst horizontalTarget).comm]

set_option backward.isDefEq.respectTransparency false in
theorem transposeComponent_B_comm
    (source target : ℤ) (related : (ComplexShape.up ℤ).Rel source target) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square source ≫
      (VerticalTotal horizontalSource horizontalTarget verticalLeft
        verticalRight square).d source target ≫
      (CochainComplex.mappingCocone.snd
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v target source (by
            have relation : source + 1 = target := by
              simpa only [ComplexShape.up_Rel] using related
            omega) ≫
      (CochainComplex.mappingCocone.fst verticalRight).f source =
    (HorizontalTotal horizontalSource horizontalTarget verticalLeft
        verticalRight square).d source target ≫
      transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square target ≫
      (CochainComplex.mappingCocone.snd
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v target source (by
            have relation : source + 1 = target := by
              simpa only [ComplexShape.up_Rel] using related
            omega) ≫
      (CochainComplex.mappingCocone.fst verticalRight).f source := by
  have related_eq : source + 1 = target := related
  let horizontal := horizontalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let vertical := verticalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let common :=
    -((CochainComplex.mappingCocone.fst horizontal).f source ≫
        (CochainComplex.mappingCocone.fst horizontalSource).f source ≫
        horizontalSource.f source) -
      (CochainComplex.mappingCocone.fst horizontal).f source ≫
        (CochainComplex.mappingCocone.snd horizontalSource).v
          source (source + (-1)) rfl ≫ B.d (source + (-1)) source
  calc
    _ = common := by
      rw [mappingCocone_d_snd_assoc vertical source target related_eq]
      simp only [Preadditive.comp_sub, Preadditive.comp_neg,
        Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc]
      have verticalFst := congrArg (fun arrow => arrow.f source)
        (mappingCoconeMap_fst verticalLeft verticalRight
          horizontalSource horizontalTarget square.symm)
      change vertical.f source ≫
          (CochainComplex.mappingCocone.fst verticalRight).f source =
        (CochainComplex.mappingCocone.fst verticalLeft).f source ≫
          horizontalSource.f source at verticalFst
      rw [verticalFst]
      rw [← (CochainComplex.mappingCocone.fst verticalRight).comm]
      rw [transposeComponent_A_assoc, transposeComponent_B_assoc]
    _ = _ := by
      have transposeTarget :=
        transposeComponent_B_at horizontalSource horizontalTarget
          verticalLeft verticalRight square target source (by omega)
      have targetCoordinate := congrArg
        (fun arrow =>
          (HorizontalTotal horizontalSource horizontalTarget verticalLeft
            verticalRight square).d source target ≫ arrow)
        transposeTarget.symm
      rw [← targetCoordinate]
      rw [← (CochainComplex.mappingCocone.fst horizontal).comm_assoc,
        mappingCocone_d_snd horizontalSource source target related_eq]
      simp only [Preadditive.comp_sub, Preadditive.comp_neg]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem transposeComponent_D_comm
    (source target : ℤ) (related : (ComplexShape.up ℤ).Rel source target) :
    transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square source ≫
      (VerticalTotal horizontalSource horizontalTarget verticalLeft
        verticalRight square).d source target ≫
      (CochainComplex.mappingCocone.snd
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v target source (by
            have relation : source + 1 = target := by
              simpa only [ComplexShape.up_Rel] using related
            omega) ≫
      (CochainComplex.mappingCocone.snd verticalRight).v
        source (source + (-1)) rfl =
    (HorizontalTotal horizontalSource horizontalTarget verticalLeft
        verticalRight square).d source target ≫
      transposeComponent horizontalSource horizontalTarget verticalLeft
        verticalRight square target ≫
      (CochainComplex.mappingCocone.snd
        (verticalMap horizontalSource horizontalTarget verticalLeft
          verticalRight square)).v target source (by
            have relation : source + 1 = target := by
              simpa only [ComplexShape.up_Rel] using related
            omega) ≫
      (CochainComplex.mappingCocone.snd verticalRight).v
        source (source + (-1)) rfl := by
  have related_eq : source + 1 = target := related
  let horizontal := horizontalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let vertical := verticalMap horizontalSource horizontalTarget
    verticalLeft verticalRight square
  let previous := source + (-1)
  let previousPrevious := previous + (-1)
  let common :=
    -((CochainComplex.mappingCocone.snd horizontal).v
        source previous rfl ≫
      (CochainComplex.mappingCocone.fst horizontalTarget).f previous ≫
      horizontalTarget.f previous) -
    ((CochainComplex.mappingCocone.fst horizontal).f source ≫
      (CochainComplex.mappingCocone.fst horizontalSource).f source ≫
      square.hom source previous) +
    ((CochainComplex.mappingCocone.fst horizontal).f source ≫
      (CochainComplex.mappingCocone.snd horizontalSource).v
        source previous rfl ≫ verticalRight.f previous) -
    ((CochainComplex.mappingCocone.snd horizontal).v
        source previous rfl ≫
      (CochainComplex.mappingCocone.snd horizontalTarget).v
        previous previousPrevious rfl ≫ D.d previousPrevious previous)
  have horizontalSnd := Cochain.congr_v
    (mappingCoconeMap_snd horizontalSource horizontalTarget
      verticalLeft verticalRight square)
    source previous rfl
  have horizontalSndComponent :
      horizontal.f source ≫
          (CochainComplex.mappingCocone.snd horizontalTarget).v
            source previous rfl =
        (CochainComplex.mappingCocone.snd horizontalSource).v
            source previous rfl ≫ verticalRight.f previous -
          (CochainComplex.mappingCocone.fst horizontalSource).f source ≫
            square.hom source previous := by
    simpa [horizontal, horizontalMap, Cochain.comp_v,
      Cochain.ofHomotopy] using horizontalSnd
  have verticalSnd := Cochain.congr_v
    (mappingCoconeMap_snd verticalLeft verticalRight
      horizontalSource horizontalTarget square.symm)
    source previous rfl
  have verticalSndComponent :
      vertical.f source ≫
          (CochainComplex.mappingCocone.snd verticalRight).v
            source previous rfl =
        (CochainComplex.mappingCocone.snd verticalLeft).v
            source previous rfl ≫ horizontalTarget.f previous +
          (CochainComplex.mappingCocone.fst verticalLeft).f source ≫
            square.hom source previous := by
    simpa [vertical, verticalMap, Cochain.comp_v,
      Cochain.ofHomotopy] using verticalSnd
  calc
    _ = common := by
      rw [mappingCocone_d_snd_assoc vertical source target related_eq]
      simp only [Preadditive.comp_sub, Preadditive.comp_neg,
        Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc]
      rw [verticalSndComponent]
      rw [mappingCocone_d_snd verticalRight previous source (by omega)]
      simp only [Preadditive.comp_add, Preadditive.comp_sub,
        Preadditive.comp_neg]
      rw [transposeComponent_A_assoc, transposeComponent_B_assoc,
        transposeComponent_C_assoc, transposeComponent_D_assoc]
      simp only [Preadditive.neg_comp]
      dsimp only [common, horizontal, previous, previousPrevious]
      simp only [Category.assoc]
      abel
    _ = _ := by
      have transposeTarget :=
        transposeComponent_D_at horizontalSource horizontalTarget
          verticalLeft verticalRight square target source previous
          (by omega) rfl
      have targetCoordinate := congrArg
        (fun arrow =>
          (HorizontalTotal horizontalSource horizontalTarget verticalLeft
            verticalRight square).d source target ≫ arrow)
        transposeTarget.symm
      rw [← targetCoordinate]
      simp only [Preadditive.comp_neg]
      rw [mappingCocone_d_snd_assoc horizontal source target related_eq]
      simp only [Preadditive.sub_comp,
        Preadditive.neg_comp, Category.assoc]
      rw [horizontalSndComponent]
      rw [mappingCocone_d_snd horizontalTarget previous source (by omega)]
      simp only [Preadditive.comp_sub, Preadditive.comp_neg]
      dsimp only [common, horizontal, previous, previousPrevious]
      abel

noncomputable def totalIso :
    HorizontalTotal horizontalSource horizontalTarget verticalLeft verticalRight square ≅
      VerticalTotal horizontalSource horizontalTarget verticalLeft verticalRight square :=
  HomologicalComplex.Hom.isoOfComponents
    (componentIso horizontalSource horizontalTarget verticalLeft verticalRight square)
    (by
      intro source target related
      have related_eq : source + 1 = target := related
      apply degree_hom_ext_at
        (verticalMap horizontalSource horizontalTarget verticalLeft verticalRight square)
        target source (by omega)
      · apply degree_hom_ext_at verticalLeft target source (by omega)
        · simpa only [componentIso, ← Category.assoc] using
            (transposeComponent_A_comm horizontalSource horizontalTarget
              verticalLeft verticalRight square source target related)
        · simpa only [componentIso, ← Category.assoc] using
            (transposeComponent_C_comm horizontalSource horizontalTarget
              verticalLeft verticalRight square source target related)
      · apply degree_hom_ext verticalRight source
        · simpa only [componentIso, ← Category.assoc] using
            (transposeComponent_B_comm horizontalSource horizontalTarget
              verticalLeft verticalRight square source target related)
        · simpa only [componentIso, ← Category.assoc] using
            (transposeComponent_D_comm horizontalSource horizontalTarget
              verticalLeft verticalRight square source target related)
    )

/-- First-class actual square for rooted/dependent consumers.  It stores
only the four complexes, four arrows, and the homotopy already present in
the calculation; the total-fibre isomorphism remains a generated readout. -/
structure HomotopyCommutativeCochainSquareAt
    (C : Type u) [Category.{v} C] [Preadditive C]
    [Limits.HasBinaryBiproducts C] where
  upperLeft : CochainComplex C ℤ
  upperRight : CochainComplex C ℤ
  lowerLeft : CochainComplex C ℤ
  lowerRight : CochainComplex C ℤ
  horizontalSource : upperLeft ⟶ upperRight
  horizontalTarget : lowerLeft ⟶ lowerRight
  verticalLeft : upperLeft ⟶ lowerLeft
  verticalRight : upperRight ⟶ lowerRight
  square : Homotopy
    (verticalLeft ≫ horizontalTarget)
    (horizontalSource ≫ verticalRight)

namespace HomotopyCommutativeCochainSquareAt

variable (actual : HomotopyCommutativeCochainSquareAt C)

abbrev horizontalTotal := HorizontalTotal actual.horizontalSource
  actual.horizontalTarget actual.verticalLeft actual.verticalRight actual.square

abbrev verticalTotal := VerticalTotal actual.horizontalSource
  actual.horizontalTarget actual.verticalLeft actual.verticalRight actual.square

/-- The package never stores a comparison: it regenerates the canonical
strict chain isomorphism from its actual square. -/
noncomputable def generatedTotalIso :
    actual.horizontalTotal ≅ actual.verticalTotal :=
  totalIso actual.horizontalSource actual.horizontalTarget
    actual.verticalLeft actual.verticalRight actual.square

end HomotopyCommutativeCochainSquareAt

end

end CochainMappingCoconeTotalFiberSymmetry
end SaturationMonoid
