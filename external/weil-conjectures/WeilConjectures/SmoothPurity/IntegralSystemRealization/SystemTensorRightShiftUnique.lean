/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorShiftProperties
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass

/-! # Unique normalized shift in the signed strict-system second slot -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u a b c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SystemTensorRightShiftProof

-- Extend a prescribed isomorphism from a full resolving class, using right fractions.
-- This is the resolving-class argument of Stacks 06YJ and 04VC.

private theorem descendGood
    {M : Type a} [Category.{b} M] [Abelian M] [HasDerivedCategory M]
    {D : Type c} [Category.{d} D] (p : ObjectProperty (CochainComplex M ℤ))
    (hres : ∀ K, ∃ (P : CochainComplex M ℤ) (s : P ⟶ K), QuasiIso s ∧ p P)
    (F G : DerivedCategory M ⥤ D)
    (t : p.ι ⋙ DerivedCategory.Q ⋙ F ≅ p.ι ⋙ DerivedCategory.Q ⋙ G) :
    ∃! β : F ≅ G, ∀ P : p.FullSubcategory,
      β.hom.app (DerivedCategory.Q.obj P.obj) = t.hom.app P := by
  classical
  let H := HomotopyCategory.quotient M (.up ℤ)
  let W := HomotopyCategory.quasiIso M (.up ℤ)
  have hr : ∀ X, ∃ (Y : HomotopyCategory M (.up ℤ)) (s : Y ⟶ X), p Y.as ∧ W s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, s, hs, hP⟩ := hres K
    exact ⟨H.obj P, H.map s, hP,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  let α (X : HomotopyCategory M (.up ℤ)) (hX : p X.as) := t.hom.app ⟨X.as, hX⟩
  have hinv : W.IsInvertedBy (DerivedCategory.Qh ⋙ F) := by
    intro X Y f hf
    have := Localization.inverts DerivedCategory.Qh W f hf
    change IsIso (F.map (DerivedCategory.Qh.map f))
    infer_instance
  have hn : ∀ X Y (hX : p X.as) (hY : p Y.as) (s : X ⟶ Y),
      (DerivedCategory.Qh ⋙ F).map s ≫ α Y hY =
        α X hX ≫ (DerivedCategory.Qh ⋙ G).map s := by
    intro X Y hX hY s
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := H.map_surjective s
    exact t.hom.naturality (ObjectProperty.homMk f : (⟨P, hX⟩ : p.FullSubcategory) ⟶ ⟨Q, hY⟩)
  obtain ⟨τ, hτ⟩ := exists_natTrans_from_resolvingClass W
    (fun X ↦ p X.as) hr (DerivedCategory.Qh ⋙ F) (DerivedCategory.Qh ⋙ G) hinv α hn
  let FF := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh W D
  let β := FF.preimage τ
  have hβ : Functor.whiskerLeft DerivedCategory.Qh β = τ := FF.map_preimage τ
  have he (P : p.FullSubcategory) : β.app (DerivedCategory.Q.obj P.obj) = t.hom.app P :=
    (congr_app hβ (H.obj P.obj)).trans (hτ (H.obj P.obj) P.property)
  have hk (K : CochainComplex M ℤ) : IsIso (β.app (DerivedCategory.Q.obj K)) := by
    obtain ⟨P, s, hs, hP⟩ := hres K
    have := hs
    have hi : IsIso (β.app (DerivedCategory.Q.obj P)) := by
      rw [he ⟨P, hP⟩]
      infer_instance
    have hc : IsIso (F.map (DerivedCategory.Q.map s) ≫ β.app (DerivedCategory.Q.obj K)) := by
      rw [β.naturality]
      infer_instance
    exact (isIso_comp_left_iff _ _).1 hc
  have hi (X : DerivedCategory M) : IsIso (β.app X) := by
    let e := DerivedCategory.Q.objObjPreimageIso X
    have := hk (DerivedCategory.Q.objPreimage X)
    have hc : IsIso (F.map e.hom ≫ β.app X) := by
      rw [β.naturality]
      infer_instance
    exact (isIso_comp_left_iff _ _).1 hc
  have : IsIso β := NatIso.isIso_of_isIso_app β
  refine ⟨asIso β, he, ?_⟩
  intro β' he'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso M (.up ℤ))
  intro K
  obtain ⟨P, s, hs, hP⟩ := hres K
  have := hs
  change β'.hom.app _ = β.app _
  apply (cancel_epi (F.map (DerivedCategory.Q.map s))).1
  rw [β'.hom.naturality, β.naturality, he' ⟨P, hP⟩, he ⟨P, hP⟩]

private theorem representatives
    {M : Type a} [Category.{b} M] [Abelian M] [HasDerivedCategory M]
    (p : ObjectProperty (CochainComplex M ℤ))
    (hres : ∀ K, ∃ (P : CochainComplex M ℤ) (s : P ⟶ K), QuasiIso s ∧ p P)
    (X : DerivedCategory M) :
    ∃ P : p.FullSubcategory, Nonempty (DerivedCategory.Q.obj P.obj ≅ X) := by
  obtain ⟨P, s, hs, hP⟩ := hres (DerivedCategory.Q.objPreimage X)
  have := hs
  exact ⟨⟨P, hP⟩, ⟨asIso (DerivedCategory.Q.map s) ≪≫
    DerivedCategory.Q.objObjPreimageIso X⟩⟩

private theorem representativeExt
    {K : Type a} {D : Type b} [Category.{c} D] {E : Type d} [Category E]
    (L : K → D) (repr : ∀ X, ∃ P, Nonempty (L P ≅ X))
    {F G : D ⥤ E} (α β : F ⟶ G) (h : ∀ P, α.app (L P) = β.app (L P)) :
    α = β := by
  ext X
  obtain ⟨P, ⟨e⟩⟩ := repr X
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality, β.naturality, h P]

private theorem descendPair
    {M : Type a} [Category.{b} M] [Abelian M] [HasDerivedCategory M]
    {D : Type c} [Category.{d} D]
    (p : ObjectProperty (CochainComplex M ℤ))
    (hres : ∀ K, ∃ (P : CochainComplex M ℤ) (s : P ⟶ K), QuasiIso s ∧ p P)
    (F G : DerivedCategory M × DerivedCategory M ⥤ D)
    (t : ((p.ι ⋙ DerivedCategory.Q).prod (p.ι ⋙ DerivedCategory.Q)) ⋙ F ≅
      ((p.ι ⋙ DerivedCategory.Q).prod (p.ι ⋙ DerivedCategory.Q)) ⋙ G) :
    ∃ σ : F ≅ G, ∀ P Q : p.FullSubcategory,
      σ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
        t.hom.app (P, Q) := by
  classical
  have first (P : p.FullSubcategory) :
      ∃ e : (Functor.curry.obj F).obj (DerivedCategory.Q.obj P.obj) ≅
          (Functor.curry.obj G).obj (DerivedCategory.Q.obj P.obj),
        ∀ Q : p.FullSubcategory,
          e.hom.app (DerivedCategory.Q.obj Q.obj) = t.hom.app (P, Q) := by
    let tP : p.ι ⋙ DerivedCategory.Q ⋙
        (Functor.curry.obj F).obj (DerivedCategory.Q.obj P.obj) ≅
        p.ι ⋙ DerivedCategory.Q ⋙
          (Functor.curry.obj G).obj (DerivedCategory.Q.obj P.obj) :=
      NatIso.ofComponents (fun Q ↦ t.app (P, Q)) (fun f ↦ by
        have hid := DerivedCategory.Q.map_id P.obj
        simpa only [Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
          Functor.curry_obj_obj_map, ObjectProperty.FullSubcategory.id_hom, hid,
          Iso.app_hom] using
          t.hom.naturality (Prod.mkHom (𝟙 P) f))
    exact (descendGood p hres _ _ tP).exists
  choose e he using first
  let t₁ : p.ι ⋙ DerivedCategory.Q ⋙ Functor.curry.obj F ≅
      p.ι ⋙ DerivedCategory.Q ⋙ Functor.curry.obj G :=
    NatIso.ofComponents e (by
      intro P P' f
      apply representativeExt (fun Q : p.FullSubcategory ↦ DerivedCategory.Q.obj Q.obj)
        (representatives p hres)
      intro Q
      change F.map (Prod.mkHom (DerivedCategory.Q.map f.hom) (𝟙 _)) ≫
          (e P').hom.app (DerivedCategory.Q.obj Q.obj) =
        (e P).hom.app (DerivedCategory.Q.obj Q.obj) ≫
          G.map (Prod.mkHom (DerivedCategory.Q.map f.hom) (𝟙 _))
      rw [he, he]
      have hid := DerivedCategory.Q.map_id Q.obj
      simpa only [Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
        ObjectProperty.FullSubcategory.id_hom, hid] using
        t.hom.naturality (Prod.mkHom f (𝟙 Q)))
  obtain ⟨γ, hγ, _⟩ := descendGood p hres (Functor.curry.obj F)
    (Functor.curry.obj G) t₁
  let σ := (Functor.currying.counitIso.app F).symm ≪≫
    Functor.uncurry.mapIso γ ≪≫ Functor.currying.counitIso.app G
  refine ⟨σ, ?_⟩
  intro P Q
  change 𝟙 _ ≫ (γ.hom.app (DerivedCategory.Q.obj P.obj)).app
    (DerivedCategory.Q.obj Q.obj) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  exact (congr_app (hγ P) (DerivedCategory.Q.obj Q.obj)).trans (he P Q)

private def secondShiftIso
    {D : Type a} [Category.{b} D] [HasShift D ℤ]
    (T : D ⥤ D ⥤ D) [∀ X, (T.obj X).CommShift ℤ]
    [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ] (r : ℤ) :
    (𝟭 D).prod (shiftFunctor D r) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor D r :=
  NatIso.ofComponents (fun X ↦ ((T.obj X.1).commShiftIso r).app X.2) (by
    rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨f, g⟩
    change ((T.map f).app (Q⟦r⟧) ≫ (T.obj P').map (g⟦r⟧')) ≫
        ((T.obj P').commShiftIso r).hom.app Q' =
      ((T.obj P).commShiftIso r).hom.app Q ≫
        ((T.map f).app Q ≫ (T.obj P').map g)⟦r⟧'
    rw [Category.assoc, (T.obj P').commShiftIso_hom_naturality g r,
      ← Category.assoc, ← NatTrans.shift_app_comm (T.map f), Category.assoc,
      CategoryTheory.Functor.map_comp])

private def modelShiftIso
    {A : Type a} [Category A] {B : Type b} [Category B]
    {C : Type c} [Category C] {D : Type d} [Category D]
    (I : A ⥤ B) (S : A ⥤ A) (V : B ⥤ B)
    (H : C ⥤ C) (Z : D ⥤ D) (T : B ⥤ C) (L : C ⥤ D)
    (γ : S ⋙ I ≅ I ⋙ V) (τ : V ⋙ T ≅ T ⋙ H) (q : H ⋙ L ≅ L ⋙ Z) :
    S ⋙ I ⋙ T ⋙ L ≅ (I ⋙ T ⋙ L) ⋙ Z :=
  Functor.isoWhiskerRight γ (T ⋙ L) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft I τ) L ≪≫
      Functor.isoWhiskerLeft (I ⋙ T) q

private def conjugateShift
    {A : Type a} [Category A] {B : Type b} [Category B]
    (J : A ⥤ B) (S : A ⥤ A) (Z : B ⥤ B)
    (V : B × B ⥤ B) (U : A × A ⥤ B)
    (a : ((𝟭 A).prod S) ⋙ J.prod J ≅ J.prod J ⋙ (𝟭 B).prod Z)
    (c : U ≅ J.prod J ⋙ V)
    (t : ((𝟭 A).prod S) ⋙ U ≅ U ⋙ Z) :
    J.prod J ⋙ (𝟭 B).prod Z ⋙ V ≅ J.prod J ⋙ V ⋙ Z :=
  Functor.isoWhiskerRight a.symm V ≪≫
    Functor.isoWhiskerLeft ((𝟭 A).prod S) c.symm ≪≫ t ≪≫
      Functor.isoWhiskerRight c Z

private theorem conjugateShift_hom_app
    {A : Type a} [Category A] {B : Type b} [Category B]
    (J : A ⥤ B) (S : A ⥤ A) (Z : B ⥤ B)
    (V : B × B ⥤ B) (U : A × A ⥤ B)
    (a : ((𝟭 A).prod S) ⋙ J.prod J ≅ J.prod J ⋙ (𝟭 B).prod Z)
    (c : U ≅ J.prod J ⋙ V)
    (t : ((𝟭 A).prod S) ⋙ U ≅ U ⋙ Z) (X Y : A) :
    V.map (a.hom.app (X, Y)) ≫
        (conjugateShift J S Z V U a c t).hom.app (X, Y) =
      c.inv.app (X, S.obj Y) ≫ t.hom.app (X, Y) ≫ Z.map (c.hom.app (X, Y)) := by
  dsimp only [conjugateShift, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← V.map_comp_assoc, Iso.hom_inv_id_app, V.map_id, Category.id_comp]
  rfl

private theorem modelShiftIso_hom_app
    {A : Type a} [Category A] {B : Type b} [Category B]
    {C : Type c} [Category C] {D : Type d} [Category D]
    (I : A ⥤ B) (S : A ⥤ A) (V : B ⥤ B)
    (H : C ⥤ C) (Z : D ⥤ D) (T : B ⥤ C) (L : C ⥤ D)
    (γ : S ⋙ I ≅ I ⋙ V) (τ : V ⋙ T ≅ T ⋙ H) (q : H ⋙ L ≅ L ⋙ Z) (X : A) :
    (modelShiftIso I S V H Z T L γ τ q).hom.app X =
      L.map (T.map (γ.hom.app X)) ≫ L.map (τ.hom.app (I.obj X)) ≫
        q.hom.app (T.obj (I.obj X)) := rfl

end SystemTensorRightShiftProof

open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralSystemRealization

attribute [local irreducible] pullbackTensorCalculus
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev Complex (W : Scheme.{u}) :=
  CochainComplex (coefficientSequenceModules l E W) ℤ

private abbrev ring (W : Scheme.{u}) :=
  (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E W)

private def rightShiftIso (W : Scheme.{u}) (P Q : Complex l E W) (r : ℤ) :
    (systemTotalTensor l E W).obj (P, Q⟦r⟧) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦r⟧ :=
  CochainComplex.mapBifunctorShift₂Iso P Q (curriedTensor _) r

private def cochainRightShift (W : Scheme.{u}) (r : ℤ) :
    completedTensorShiftSecond (Complex l E W) r ⋙ systemTotalTensor l E W ≅
      systemTotalTensor l E W ⋙ shiftFunctor (Complex l E W) r :=
  by
  exact SystemTensorRightShiftProof.secondShiftIso
    (curriedTensor (coefficientSequenceModules l E W)).map₂CochainComplex r

private theorem cochainRightShift_hom_app (W : Scheme.{u}) (r : ℤ)
    (P Q : Complex l E W) :
    (cochainRightShift l E W r).hom.app (P, Q) =
      (rightShiftIso l E W P Q r).hom := rfl

attribute [local irreducible] cochainRightShift

private def flatShift (W : Scheme.{u}) (r : ℤ)
    (stable : ∀ Q : Complex l E W, systemKFlat l E W Q →
      systemKFlat l E W (Q⟦r⟧)) :
    ObjectProperty.FullSubcategory (systemKFlat l E W) ⥤
      ObjectProperty.FullSubcategory (systemKFlat l E W) where
  obj Q := ⟨Q.obj⟦r⟧, stable Q.obj Q.property⟩
  map f := ObjectProperty.homMk (f.hom⟦r⟧')
  map_id _ := by
    apply ObjectProperty.hom_ext
    exact (shiftFunctor (Complex l E W) r).map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (shiftFunctor (Complex l E W) r).map_comp f.hom g.hom

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh

private def resolvingShiftIso (W : Scheme.{u}) (r : ℤ)
    (stable : ∀ Q : Complex l E W, systemKFlat l E W Q →
      systemKFlat l E W (Q⟦r⟧)) :
    (((coefficientKFlatInclusion.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)) ⋙ DerivedCategory.Q).prod
      ((coefficientKFlatInclusion.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)) ⋙ DerivedCategory.Q)) ⋙
      (completedTensorShiftSecond (System l E W) r ⋙
        (calculus l E W).systemClosed.tensor) ≅
    (((coefficientKFlatInclusion.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)) ⋙ DerivedCategory.Q).prod
      ((coefficientKFlatInclusion.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)) ⋙ DerivedCategory.Q)) ⋙
      ((calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r) := by
  let I := coefficientKFlatInclusion.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  let J := I ⋙ DerivedCategory.Q
  let c := (calculus l E W).systemTensorModel.comparison
  let a : ((𝟭 _).prod (flatShift l E W r stable)) ⋙ J.prod J ≅
      J.prod J ⋙ completedTensorShiftSecond (System l E W) r :=
    NatIso.prod (Iso.refl J) (Functor.isoWhiskerLeft I (DerivedCategory.Q.commShiftIso r))
  let t : ((𝟭 _).prod (flatShift l E W r stable)) ⋙
      ((I.prod I) ⋙ systemTotalTensor l E W ⋙ DerivedCategory.Q) ≅
      ((I.prod I) ⋙ systemTotalTensor l E W ⋙ DerivedCategory.Q) ⋙
        shiftFunctor (System l E W) r :=
    SystemTensorRightShiftProof.modelShiftIso (I.prod I)
      ((𝟭 _).prod (flatShift l E W r stable))
      (completedTensorShiftSecond (Complex l E W) r)
      (shiftFunctor (Complex l E W) r) (shiftFunctor (System l E W) r)
      (systemTotalTensor l E W) DerivedCategory.Q (eqToIso (by rfl))
      (cochainRightShift l E W r) (DerivedCategory.Q.commShiftIso r)
  exact SystemTensorRightShiftProof.conjugateShift J (flatShift l E W r stable)
    (shiftFunctor (System l E W) r) (calculus l E W).systemClosed.tensor _ a c t

private theorem signedSection {C : Type a} [Category.{b} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{c}}
    {X Y X' Y' : SheafOfModules.{c} R}
    (a : X ⟶ Y) (b : Y ⟶ Y') (c : X ⟶ X') (d : X' ⟶ Y')
    (s : ℤˣ) (h : a ≫ b = s • (c ≫ d)) (U : Cᵒᵖ) (x : X.val.obj U) :
    b.val.app U (a.val.app U x) = d.val.app U (s • c.val.app U x) := by
  let H := SheafOfModules.evaluation (R := R) U
  have : H.Additive := inferInstanceAs
    ((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U).Additive)
  have he := congrArg (fun k ↦ H.map k x) h
  simp only [Units.smul_def, Functor.map_comp, Functor.map_zsmul,
    ModuleCat.comp_apply] at he
  change b.val.app U (a.val.app U x) = (s : ℤ) • d.val.app U (c.val.app U x) at he
  simpa only [Units.smul_def, _root_.map_zsmul] using he

private theorem rightShiftFormula (W : Scheme.{u}) (P Q : Complex l E W) (r : ℤ) :
    systemTensorRightFormula l E W P Q r (rightShiftIso l E W P Q r) := by
  intro i j U x y
  let R := coefficientSequenceCommRingSheaf l E W
  let T := curriedTensor (coefficientSequenceModules l E W)
  have h := CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
    P Q T r i j (i + j) rfl (j + r) (i + (j + r)) rfl (by omega)
  change _ = (i * r).negOnePow • (T.obj (P.X i)).map (𝟙 _) ≫ _ at h
  rw [CategoryTheory.Functor.map_id, Category.id_comp, mul_comm i r] at h
  exact signedSection _ _ _ _ _ h U
    (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (ring l E W).obj)).unit.app
        ((P.X i).val ⊗ (Q.X (j + r)).val) ≫
      (SheafOfModules.tensorObjIsoSheafification (R := R)
        (P.X i) (Q.X (j + r))).inv.val).app U
          (x ⊗ₜ[R.obj.obj U] y))

private theorem shiftedKFlat (W : Scheme.{u}) (Q : Complex l E W)
    (hQ : systemKFlat l E W Q) (r : ℤ) : systemKFlat l E W (Q⟦r⟧) := by
  intro F hF i
  have h := hQ F hF
  have hs : (((systemTotalTensor l E W).obj (F, Q))⟦r⟧).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h ⊢
    rw [← HomotopyCategory.shift_quotient_obj]
    exact (HomotopyCategory.subcategoryAcyclic (coefficientSequenceModules l E W)).le_shift
      r _ h
  exact (hs i).of_iso (rightShiftIso l E W F Q r).symm

private theorem tensorSectionExt (W : Scheme.{u})
    (M N H : coefficientSequenceModules l E W)
    {f g : M ⊗ N ⟶ H}
    (h : ∀ U x y,
      f.val.app U (((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (𝟙 (ring l E W).obj)).unit.app (M.val ⊗ N.val) ≫
        (SheafOfModules.tensorObjIsoSheafification M N).inv.val).app U
          (x ⊗ₜ[(coefficientSequenceCommRingSheaf l E W).obj.obj U] y)) =
      g.val.app U (((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (𝟙 (ring l E W).obj)).unit.app (M.val ⊗ N.val) ≫
        (SheafOfModules.tensorObjIsoSheafification M N).inv.val).app U
          (x ⊗ₜ[(coefficientSequenceCommRingSheaf l E W).obj.obj U] y))) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ring l E W).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h U

private theorem rightFormulaExt (W : Scheme.{u}) (P Q : Complex l E W) (r : ℤ)
    (α β : (systemTotalTensor l E W).obj (P, Q⟦r⟧) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦r⟧)
    (hα : systemTensorRightFormula l E W P Q r α)
    (hβ : systemTensorRightFormula l E W P Q r β) : α = β := by
  apply Iso.ext
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  subst k
  apply tensorSectionExt l E W
  intro U x y
  exact (hα i j U x y).trans (hβ i j U x y).symm

private theorem flatResolution (W : Scheme.{u}) (K : Complex l E W) :
    ∃ (P : Complex l E W) (s : P ⟶ K), QuasiIso s ∧ systemKFlat l E W P := by
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) K
  exact ⟨P, s, hs, hP⟩

attribute [local irreducible] coefficientTotalTensor

private theorem normalizedComponent (W : Scheme.{u}) (r : ℤ)
    (σ : completedTensorShiftSecond (System l E W) r ⋙
        (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r)
    (P Q : Complex l E W) (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q)
    (h : σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (resolvingShiftIso l E W r (fun Q hQ ↦ shiftedKFlat l E W Q hQ r)).hom.app
        (⟨P, hP⟩, ⟨Q, hQ⟩)) :
    ∃ (hS : systemKFlat l E W (Q⟦r⟧))
      (α : (systemTotalTensor l E W).obj (P, Q⟦r⟧) ≅
        ((systemTotalTensor l E W).obj (P, Q))⟦r⟧),
      systemTensorRightFormula l E W P Q r α ∧
      (calculus l E W).systemClosed.tensor.map
        (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (Q⟦r⟧)))
        (Y := (DerivedCategory.Q.obj P, (DerivedCategory.Q.obj Q)⟦r⟧))
        (𝟙 _, (DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
          σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        P (Q⟦r⟧) hP hS).inv ≫
      DerivedCategory.Q.map α.hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
      (shiftFunctor (System l E W) r).map
        (((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          P Q hP hQ).hom) := by
  refine ⟨shiftedKFlat l E W Q hQ r, rightShiftIso l E W P Q r,
    rightShiftFormula l E W P Q r, ?_⟩
  rw [h]
  unfold resolvingShiftIso
  let I := coefficientKFlatInclusion.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  let J := I ⋙ DerivedCategory.Q
  let S := flatShift l E W r (fun Q hQ ↦ shiftedKFlat l E W Q hQ r)
  refine (SystemTensorRightShiftProof.conjugateShift_hom_app J S
    (shiftFunctor (System l E W) r) (calculus l E W).systemClosed.tensor
    ((I.prod I) ⋙ systemTotalTensor l E W ⋙ DerivedCategory.Q)
    (NatIso.prod (Iso.refl J)
      (Functor.isoWhiskerLeft I (DerivedCategory.Q.commShiftIso r)))
    (calculus l E W).systemTensorModel.comparison _ ⟨P, hP⟩ ⟨Q, hQ⟩).trans ?_
  have ht := SystemTensorRightShiftProof.modelShiftIso_hom_app (I.prod I)
    ((𝟭 _).prod S) (completedTensorShiftSecond (Complex l E W) r)
    (shiftFunctor (Complex l E W) r) (shiftFunctor (System l E W) r)
    (systemTotalTensor l E W) DerivedCategory.Q (eqToIso (by rfl))
    (cochainRightShift l E W r) (DerivedCategory.Q.commShiftIso r)
    (⟨P, hP⟩, ⟨Q, hQ⟩)
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    (systemTotalTensor l E W).map_id, DerivedCategory.Q.map_id, Category.id_comp] at ht
  refine (congrArg (fun f ↦
    (calculus l E W).systemTensorModel.comparison.inv.app (⟨P, hP⟩, S.obj ⟨Q, hQ⟩) ≫
      f ≫ (shiftFunctor (System l E W) r).map
        ((calculus l E W).systemTensorModel.comparison.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)))
      ht).trans ?_
  dsimp only [I, J, S, flatShift, coefficientKFlatInclusion,
    Functor.prod_obj, Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj]
  simpa only [Category.assoc, CoefficientTensorModels.iso, Iso.app_hom, Iso.app_inv] using
    congrArg (fun f ↦
    ((calculus l E W).systemTensorModel.iso
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
      P (Q⟦r⟧) hP (shiftedKFlat l E W Q hQ r)).inv ≫
    DerivedCategory.Q.map f ≫
    (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
    (shiftFunctor (System l E W) r).map
      (((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        P Q hP hQ).hom)) (cochainRightShift_hom_app l E W r P Q)

private theorem normalizedExt (W : Scheme.{u}) (r : ℤ)
    (σ τ : completedTensorShiftSecond (System l E W) r ⋙
        (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r)
    (hσ : systemTensorRightProperty l E W r σ)
    (hτ : systemTensorRightProperty l E W r τ) : σ = τ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rcases X with ⟨M, N⟩
  obtain ⟨P, ⟨eP⟩⟩ := SystemTensorRightShiftProof.representatives
    (systemKFlat l E W) (flatResolution l E W) M
  obtain ⟨Q, ⟨eQ⟩⟩ := SystemTensorRightShiftProof.representatives
    (systemKFlat l E W) (flatResolution l E W) N
  have hc : σ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      τ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) := by
    obtain ⟨hS, α, hα, hs⟩ := hσ P.obj Q.obj P.property Q.property
    obtain ⟨hS', β, hβ, ht⟩ := hτ P.obj Q.obj P.property Q.property
    have hab := rightFormulaExt l E W P.obj Q.obj r α β hα hβ
    subst β
    let b := (calculus l E W).systemClosed.tensor.mapIso
      (Iso.prod (Iso.refl (DerivedCategory.Q.obj P.obj))
        ((DerivedCategory.Q.commShiftIso r).app Q.obj))
    exact (cancel_epi b.hom).1 (hs.trans ht.symm)
  let e := eP.prod eQ
  apply (cancel_epi
    ((completedTensorShiftSecond (System l E W) r ⋙
      (calculus l E W).systemClosed.tensor).map e.hom)).1
  rw [σ.hom.naturality, τ.hom.naturality, hc]

/-- Existence and uniqueness for the signed strict-system second slot.
Source: Stacks 011G, 012Z, 014E, 06YU, 0941; blueprint purity transport, Step 2
(blueprint: lem-pur-system-tensor-right-shift-unique).

Proof: Reindex total tensor by (i,j) ↦ (i,j+r), multiplying its (i,j)
summand by (-1)^(ri). The first differential changes i by one and hence changes
this coefficient by (-1)^r; the second preserves it. These are exactly the two
signs needed for a cochain map to the shifted total. Reverse reindexing gives
its inverse. The maps commute with restrictions and coefficient transitions
and are natural in both inputs. Shifts preserve K-flatness; descend through
the recorded K-flat tensor models. This gives the stated property for every
K-flat pair. For uniqueness the generator formula determines the cochain maps,
the model equation determines the derived components on K-flat representatives,
and naturality along resolving isomorphisms determines all other components.
Extensionality of natural isomorphisms finishes. -/
theorem systemTensorRightShift_existsUnique (W : Scheme.{u}) (r : ℤ) :
    ∃! σ : completedTensorShiftSecond (System l E W) r ⋙
        (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r,
      systemTensorRightProperty l E W r σ := by
  let t := resolvingShiftIso l E W r (fun Q hQ ↦ shiftedKFlat l E W Q hQ r)
  obtain ⟨σ, hσ⟩ := SystemTensorRightShiftProof.descendPair
    (systemKFlat l E W) (flatResolution l E W) _ _ t
  have hn : systemTensorRightProperty l E W r σ := by
    intro P Q hP hQ
    exact normalizedComponent l E W r σ P Q hP hQ (hσ ⟨P, hP⟩ ⟨Q, hQ⟩)
  exact ⟨σ, hn, fun τ hτ ↦ normalizedExt l E W r τ σ hτ hn⟩

end WeilConjectures.IntegralSystemRealization
