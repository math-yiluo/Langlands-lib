/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel

/-! # Universal whole-cochain scalar reduction counit

Source: Stacks 06YY and 0940--0941; the whole-sequence derived balancing construction.
(blueprint: lem-pur-scalar-source-counit-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
-- The converse derived-adjunction argument, retaining an arbitrary output functor.
private theorem mate_rightKan
    {A B C D H : Type*} [Category A] [Category B] [Category C] [Category D] [Category H]
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    {Q : A ⥤ C} {P : B ⥤ D} {LD : C ⥤ D} {RD : D ⥤ C} (b : LD ⊣ RD)
    (β : R ⋙ Q ⟶ P ⋙ RD) (Z : D ⥤ H)
    (hβ : ∀ X : C ⥤ H, (RD ⋙ X).IsLeftKanExtension
      ((Functor.associator R Q X).inv ≫ Functor.whiskerRight β X ≫
        (Functor.associator P RD X).hom)) :
    (LD ⋙ Z).IsRightKanExtension
      ((Functor.associator Q LD Z).inv ≫
        Functor.whiskerRight ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β)) Z ≫
          (Functor.associator L P Z).hom) := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β))
  let ε := (Functor.associator Q LD Z).inv ≫ Functor.whiskerRight α Z ≫
    (Functor.associator L P Z).hom
  let βX (X : C ⥤ H) := (Functor.associator R Q X).inv ≫
    Functor.whiskerRight β X ≫ (Functor.associator P RD X).hom
  let ν (Y : Functor.RightExtension Q (L ⋙ P ⋙ Z)) : R ⋙ Q ⋙ Y.left ⟶ P ⋙ Z :=
    { app := fun j ↦ Y.hom.app (R.obj j) ≫ Z.map (P.map (a.counit.app j))
      naturality := by
        intro j k f
        dsimp only [Functor.comp_map]
        rw [← Category.assoc]
        rw [show Y.left.map (Q.map (R.map f)) ≫ Y.hom.app (R.obj k) =
          Y.hom.app (R.obj j) ≫ Z.map (P.map (L.map (R.map f))) from
            Y.hom.naturality (R.map f)]
        simp only [Category.assoc]
        rw [← Z.map_comp, ← P.map_comp, show L.map (R.map f) ≫ a.counit.app k =
          a.counit.app j ≫ f from a.counit.naturality f, P.map_comp, Z.map_comp] }
  let t (Y : Functor.RightExtension Q (L ⋙ P ⋙ Z)) : RD ⋙ Y.left ⟶ Z :=
    have := hβ Y.left
    (RD ⋙ Y.left).descOfIsLeftKanExtension (βX Y.left) Z (ν Y)
  have ht (Y : Functor.RightExtension Q (L ⋙ P ⋙ Z)) (j : B) :
      Y.left.map (β.app j) ≫ (t Y).app (P.obj j) = (ν Y).app j := by
    have := hβ Y.left
    simpa only [βX, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Category.id_comp,
      Category.comp_id] using
      (RD ⋙ Y.left).descOfIsLeftKanExtension_fac_app (βX Y.left) Z (ν Y) j
  let γ (Y : Functor.RightExtension Q (L ⋙ P ⋙ Z)) : Y.left ⟶ LD ⋙ Z :=
    { app := fun j ↦ Y.left.map (b.unit.app j) ≫ (t Y).app (LD.obj j)
      naturality := by
        intro j k f
        dsimp only [Functor.comp_map]
        rw [← Y.left.map_comp_assoc, show f ≫ b.unit.app k =
          b.unit.app j ≫ RD.map (LD.map f) from b.unit.naturality f, Y.left.map_comp,
          Category.assoc]
        have hn := (t Y).naturality (LD.map f)
        dsimp only [Functor.comp_map] at hn
        rw [hn, Category.assoc] }
  have hf (Y : Functor.RightExtension Q (L ⋙ P ⋙ Z)) :
      Functor.whiskerLeft Q (γ Y) ≫ ε = Y.hom := by
    ext j
    simp only [ε, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Category.id_comp, Category.comp_id]
    change (Y.left.map (b.unit.app (Q.obj j)) ≫ (t Y).app (LD.obj (Q.obj j))) ≫
      Z.map (α.app j) = Y.hom.app j
    have hn := (t Y).naturality (α.app j)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← Y.left.map_comp]
    have hu := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ β) j
    change Q.map (a.unit.app j) ≫ β.app (L.obj j) =
      b.unit.app (Q.obj j) ≫ RD.map (α.app j) at hu
    rw [← hu, Y.left.map_comp, Category.assoc, ht]
    change Y.left.map (Q.map (a.unit.app j)) ≫
      (Y.hom.app (R.obj (L.obj j)) ≫ Z.map (P.map (a.counit.app (L.obj j)))) = _
    have hy := Y.hom.naturality (a.unit.app j)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.whiskeringLeft_obj_obj] at hy
    rw [← Category.assoc, hy]
    simp only [Category.assoc]
    erw [← Z.map_comp, ← P.map_comp, a.left_triangle_components,
      P.map_id, Z.map_id, Category.comp_id]
    rfl
  constructor
  refine ⟨IsTerminal.ofUniqueHom
    (fun Y ↦ CostructuredArrow.homMk (γ Y) (hf Y)) ?_⟩
  intro Y m
  apply CostructuredArrow.hom_ext
  let μ : Y.left ⟶ LD ⋙ Z := m.left
  let s : RD ⋙ Y.left ⟶ Z :=
    { app := fun j ↦ μ.app (RD.obj j) ≫ Z.map (b.counit.app j)
      naturality := by
        intro j k f
        dsimp only [Functor.comp_map]
        rw [μ.naturality_assoc]
        simp only [Functor.comp_map, Category.assoc]
        rw [← Z.map_comp, show LD.map (RD.map f) ≫ b.counit.app k =
          b.counit.app j ≫ f from b.counit.naturality f, Z.map_comp] }
  have hs : s = t Y := by
    have := hβ Y.left
    apply (RD ⋙ Y.left).hom_ext_of_isLeftKanExtension (βX Y.left)
    ext j
    simp only [βX, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Category.id_comp, Category.comp_id]
    change Y.left.map (β.app j) ≫ s.app (P.obj j) =
      Y.left.map (β.app j) ≫ (t Y).app (P.obj j)
    rw [ht]
    dsimp only [s]
    have hn := μ.naturality (β.app j)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← Category.assoc, hn, Category.assoc, ← Z.map_comp]
    have hc := mateEquiv_counit_symm a b (TwoSquare.mk _ _ _ _ β) j
    change LD.map (β.app j) ≫ b.counit.app (P.obj j) =
      α.app (R.obj j) ≫ P.map (a.counit.app j) at hc
    rw [hc, Z.map_comp, ← Category.assoc]
    have hm := NatTrans.congr_app (CostructuredArrow.w m) (R.obj j)
    simp only [NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
      Functor.whiskerLeft_app, Functor.RightExtension.mk_hom,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.whiskerRight_app, Category.comp_id] at hm
    change μ.app (Q.obj (R.obj j)) ≫
      (𝟙 _ ≫ Z.map (α.app (R.obj j))) = Y.hom.app (R.obj j) at hm
    simp only [Category.id_comp] at hm
    rw [hm]
  ext j
  change μ.app j = Y.left.map (b.unit.app j) ≫ (t Y).app (LD.obj j)
  rw [← hs]
  dsimp only [s]
  have hn := μ.naturality (b.unit.app j)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc, hn, Category.assoc]
  erw [← Z.map_comp, b.left_triangle_components, Z.map_id, Category.comp_id]
  rfl

private theorem precomp_rightKan
    {A B C H : Type*} [Category A] [Category B] [Category C] [Category H]
    (q : A ⥤ B) [((Functor.whiskeringLeft A B H).obj q).Full]
    [((Functor.whiskeringLeft A B H).obj q).Faithful] (Q : B ⥤ C) (F : B ⥤ H)
    (L : C ⥤ H) (ε : Q ⋙ L ⟶ F) [L.IsRightKanExtension ε] :
    L.IsRightKanExtension
      ((Functor.associator q Q L).hom ≫ Functor.whiskerLeft q ε) := by
  let V := (Functor.whiskeringLeft A B H).obj q
  let β (Y : Functor.RightExtension (q ⋙ Q) (q ⋙ F)) : Q ⋙ Y.left ⟶ F :=
    V.preimage ((Functor.associator q Q Y.left).inv ≫ Y.hom)
  have hβ (Y : Functor.RightExtension (q ⋙ Q) (q ⋙ F)) :
      Functor.whiskerLeft q (β Y) =
        (Functor.associator q Q Y.left).inv ≫ Y.hom := V.map_preimage _
  let γ (Y : Functor.RightExtension (q ⋙ Q) (q ⋙ F)) :=
    L.liftOfIsRightKanExtension ε Y.left (β Y)
  constructor
  refine ⟨IsTerminal.ofUniqueHom (fun Y ↦ CostructuredArrow.homMk (γ Y) ?_) ?_⟩
  · ext j
    have h := L.liftOfIsRightKanExtension_fac_app ε Y.left (β Y) (q.obj j)
    have hb := NatTrans.congr_app (hβ Y) j
    simp only [NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Category.id_comp] at hb
    change (γ Y).app (Q.obj (q.obj j)) ≫
      ((Functor.associator q Q L).hom.app j ≫ ε.app (q.obj j)) = Y.hom.app j
    dsimp only [Functor.associator_hom_app]
    erw [Category.id_comp]
    exact h.trans hb
  · intro Y m
    apply CostructuredArrow.hom_ext
    apply L.hom_ext_of_isRightKanExtension ε
    apply V.map_injective
    ext j
    have hm := NatTrans.congr_app (CostructuredArrow.w m) j
    have hg := L.liftOfIsRightKanExtension_fac_app ε Y.left (β Y) (q.obj j)
    have hb := NatTrans.congr_app (hβ Y) j
    simp only [NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Category.id_comp] at hb
    change m.left.app (Q.obj (q.obj j)) ≫ ε.app (q.obj j) =
      (γ Y).app (Q.obj (q.obj j)) ≫ ε.app (q.obj j)
    change m.left.app (Q.obj (q.obj j)) ≫
      ((Functor.associator q Q L).hom.app j ≫ ε.app (q.obj j)) = Y.hom.app j at hm
    let μ : Y.left ⟶ L := m.left
    have hm' : μ.app (Q.obj (q.obj j)) ≫ (𝟙 _ ≫ ε.app (q.obj j)) =
        Y.hom.app j := hm
    simp only [Category.id_comp] at hm'
    exact hm'.trans (hg.trans hb).symm

namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Tensor by the finite free constant coefficient ring preserves the universal
whole-system reduction counit, prior to finite evaluation.
Source: Stacks 06YY (derived extension of scalars), 0940--0941 (the ringed sequence site).
Proof: on the sequence site, ordinary quotient extension is left adjoint to the
ordinary completed limit. Derive this adjunction using K-flat replacements for the
left adjoint and K-injective replacements for the right adjoint. The normalized
right-derived limit comparison in NativeConstantSupportModel identifies its mate
with the displayed cochain counit. Restriction from quotient coefficients to
constant integral coefficients leaves underlying complexes unchanged and takes a
K-flat quotient extension to a complex acyclic for this composite. Tensor by B is
finite free, hence exact and preserves these acyclic replacements. Thus the
composite computes the total left derived functor of ordinary reduction followed
by constant tensor, with precisely the displayed counit. Its derived universal
property on the homotopy category also holds along Q on cochain complexes,
since every functor to a derived category and every comparison here identifies
chain homotopic maps. This gives the stated right Kan extension, including
naturality in every cochain map. No finite-evaluation faithfulness is used.
(blueprint: lem-pur-scalar-source-counit-universal). -/
theorem scalarSourceCounit_universal (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) :
    letI := (tensor_exact l E F i W).1
    letI := (tensor_exact l E F i W).2
    letI := ordinaryReduction_additive l E W
    letI := systemRestriction_additive l E W
    let O := ordinaryReduction l E W ⋙ systemRestriction l E W
    letI : O.Additive := inferInstanceAs
      ((ordinaryReduction l E W ⋙ systemRestriction l E W).Additive)
    let γ (P : CochainComplex (scalarReductionSource l E W) ℤ) :=
      S.reduction.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
        (systemReductionCounit l E W S).app ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map
          (((ordinaryReduction l E W).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          (((ordinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)
    let δ (P : CochainComplex (scalarReductionSource l E W) ℤ) :
        (reduction l E W S).obj (DerivedCategory.Q.obj P) ⟶
          DerivedCategory.Q.obj ((O.mapHomologicalComplex (.up ℤ)).obj P) :=
      (systemU l E W).map (γ P) ≫
        (systemRestriction l E W).mapDerivedCategoryFactors.hom.app
          (((ordinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)
    letI : (O ⋙ tensor l E F i W).Additive := inferInstance
    ∃ α : DerivedCategory.Q ⋙ (reduction l E W S ⋙ T l E F i W) ⟶
        ((O ⋙ tensor l E F i W).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q,
      (∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
        α.app P = (T l E F i W).map (δ P) ≫
          (tensor l E F i W).mapDerivedCategoryFactors.hom.app
            ((O.mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (reduction l E W S ⋙ T l E F i W).IsRightKanExtension α := by
  let := (tensor_exact l E F i W).1
  let := (tensor_exact l E F i W).2
  let O := ordinaryReduction l E W ⋙ systemRestriction l E W
  let Z := systemU l E W ⋙ T l E F i W
  let b := S.adjunction.ofNatIsoRight (reductionRightComparison l E W).symm
  have hβ (X : DerivedCategory (scalarReductionSource l E W) ⥤
      Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) :
      ((ordinaryLimit l E W).rightDerivedFunctor ⋙ X).IsLeftKanExtension
        ((Functor.associator _ _ X).inv ≫
          Functor.whiskerRight (ordinaryLimit l E W).rightDerivedFunctorUnit X ≫
            (Functor.associator _ _ X).hom) := by
    let βX := (Functor.associator _ _ X).inv ≫
      Functor.whiskerRight (ordinaryLimit l E W).rightDerivedFunctorUnit X ≫
        (Functor.associator _ _ X).hom
    have h := (HomotopyCategory.KInjectives.localizerMorphism
      (coefficientSequenceModules l E W)).isRightDerivedFunctor_of_isRightDerivabilityStructure
        βX (by
        intro K
        obtain ⟨K, hK, rfl⟩ := K.mk_surjective
        let := hK
        simp only [βX, NatTrans.comp_app, Functor.associator_inv_app,
          Functor.associator_hom_app, Functor.whiskerRight_app,
          Category.id_comp, Category.comp_id]
        change IsIso (X.map ((ordinaryLimit l E W).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj K)))
        infer_instance)
    exact h.isLeftKanExtension
  have hh := mate_rightKan ((ordinaryReductionAdj l E W).mapHomotopyCategory (.up ℤ))
    b (ordinaryLimit l E W).rightDerivedFunctorUnit Z hβ
  let q := HomotopyCategory.quotient (scalarReductionSource l E W) (.up ℤ)
  let εh := (Functor.associator DerivedCategory.Qh S.reduction Z).inv ≫
    Functor.whiskerRight (systemReductionCounit l E W S) Z ≫
      (Functor.associator _ _ Z).hom
  have : (S.reduction ⋙ Z).IsRightKanExtension εh := hh
  have hc := precomp_rightKan q DerivedCategory.Qh _ _ εh
  let j₀ := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((ordinaryReduction l E W).mapHomotopyCategoryFactors (.up ℤ))
      (DerivedCategory.Qh ⋙ Z) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((ordinaryReduction l E W).mapHomologicalComplex (.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _) Z)
  let j₁ := Functor.isoWhiskerLeft
    ((ordinaryReduction l E W).mapHomologicalComplex (.up ℤ))
    ((Functor.associator DerivedCategory.Q (systemU l E W) (T l E F i W)).symm ≪≫
      Functor.isoWhiskerRight (systemRestriction l E W).mapDerivedCategoryFactors
        (T l E F i W) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((systemRestriction l E W).mapHomologicalComplex (.up ℤ))
        (tensor l E F i W).mapDerivedCategoryFactors)
  let α := (Functor.associator q DerivedCategory.Qh (S.reduction ⋙ Z)).hom ≫
    Functor.whiskerLeft q εh ≫ j₀.hom ≫ j₁.hom
  refine ⟨α, ?_, ?_⟩
  · intro P
    have hi : (DerivedCategory.quotientCompQhIso _).inv.app P = 𝟙 _ := rfl
    simp only [hi, S.reduction.map_id, Category.id_comp]
    simp only [α, εh, j₀, j₁, Z, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.trans_hom,
      Iso.symm_hom, Functor.comp_map, Functor.map_comp, Category.id_comp,
      Category.comp_id, Category.assoc]
    erw [Category.id_comp, Category.id_comp]
    rfl
  · let εc := (Functor.associator q DerivedCategory.Qh (S.reduction ⋙ Z)).hom ≫
      Functor.whiskerLeft q εh
    have : (S.reduction ⋙ Z).IsRightKanExtension εc := hc
    have h := (Functor.isRightKanExtension_iff_of_iso₂ εc
      (εc ≫ (j₀ ≪≫ j₁).hom) (j₀ ≪≫ j₁) (Iso.refl _) (by simp)).mp hc
    change (S.reduction ⋙ Z).IsRightKanExtension α
    have he : α = εc ≫ (j₀ ≪≫ j₁).hom := by
      dsimp only [α, εc, Iso.trans_hom]
      simp only [Category.assoc]
    rw [he]
    exact h

end WeilConjectures.PurStrictScalar
