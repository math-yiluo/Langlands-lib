/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.WeilSheaf.FiniteLeray
import WeilConjectures.WeilSheaf.DirectImageRestriction
import WeilConjectures.WeilSheaf.UpperStarComp
import WeilConjectures.WeilSheaf.IsotypicPullback
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.WeilSheaf.Localization
import WeilConjectures.WeilSheaf.ProperBaseChange
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Proper/open interchange for native Weil complexes

Source: Stacks Project, Tag 0F7B, `lemma-shriek-proper-and-open`, for the geometric
pattern; the native bounded constructible coefficient realization and proof are those of
(blueprint: lem-sf-native-weil-open-proper-interchange).

The source is the bounded constructible full subcategory of the ordinary native derived
category. The target is the ordinary derived category of all pro-etale Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

namespace CategoryTheory

private theorem inverseMate_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (M : C) :
    (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ β)).app M) =
      L₂.map (G.map (a₁.unit.app M)) ≫
        L₂.map (β.app (L₁.obj M)) ≫ a₂.counit.app (H.obj (L₁.obj M)) := by
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_id, Category.id_comp]
  change _ ≫ _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.comp_id]

private noncomputable def inverseMateNatTrans
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) : G ⋙ L₂ ⟶ L₁ ⋙ H where
  app M := L₂.map (G.map (a₁.unit.app M)) ≫
    L₂.map (β.app (L₁.obj M)) ≫ a₂.counit.app (H.obj (L₁.obj M))
  naturality M N f := by
    have h := (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ β))).naturality f
    simpa only [inverseMate_app] using h

end CategoryTheory

namespace AlgebraicGeometry

private noncomputable def nativeOpenAdjunction
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U S : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [S.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j := by
  apply IsoAlgebra.mapOfNatIsoLeftAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l _)
    (ProEtale.adicUpperStarLowerStarAdjunction l _)
    _ _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l j _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar l _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j _)
  intro K
  exact ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    _ K

private theorem nativeOpenAdjunction_unit_isIso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U S : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [S.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] :
    IsIso (nativeOpenAdjunction k₀ l j).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have h : IsIso ((IsoAlgebra.forget _).map
      ((nativeOpenAdjunction k₀ l j).unit.app M)) := by
    change IsIso ((ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier)
    infer_instance
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)

end AlgebraicGeometry

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private noncomputable def exactDerivedAdjunction (adj : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory := by
  letI : CatCommSq (L.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (R.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q R.mapDerivedCategory := ⟨R.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

private theorem exactDerivedAdjunction_unit_isIso (adj : L ⊣ R) [IsIso adj.unit] :
    IsIso adj.exactDerivedAdjunction.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  let M : CochainComplex C ℤ := DerivedCategory.Q.objPreimage K
  have hM : IsIso (adj.exactDerivedAdjunction.unit.app
      (DerivedCategory.Q.obj M)) := by
    unfold exactDerivedAdjunction
    rw [Adjunction.localization_unit_app]
    have : ∀ n : ℤ, IsIso
        (((adj.mapHomologicalComplex (.up ℤ)).unit.app M).f n) := by
      intro n
      change IsIso (adj.unit.app (M.X n))
      infer_instance
    have := HomologicalComplex.Hom.isIso_of_components
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app M)
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso adj.exactDerivedAdjunction.unit
    (DerivedCategory.Q.objObjPreimageIso K)).mp hM

private theorem exactDerivedAdjunction_counit_isIso_of_isZero
    {Z : Type*} [Category Z] [Abelian Z] [HasDerivedCategory Z]
    (adj : L ⊣ R) [IsIso adj.unit]
    (iUp : D ⥤ Z) [iUp.Additive]
    [PreservesFiniteLimits iUp] [PreservesFiniteColimits iUp]
    (h₀ : ∀ M, IsZero (iUp.obj (L.obj M)))
    (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (R.obj F) → IsZero F)
    {K : DerivedCategory D} (hK : IsZero (iUp.mapDerivedCategory.obj K)) :
    IsIso (adj.exactDerivedAdjunction.counit.app K) := by
  let adj' := adj.exactDerivedAdjunction
  have := adj.exactDerivedAdjunction_unit_isIso
  obtain ⟨W, v, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    (adj'.counit.app K)
  have hr : IsIso (R.mapDerivedCategory.map (adj'.counit.app K)) :=
    IsIso.of_isIso_fac_left (adj'.right_triangle_components K)
  have hi : IsIso (iUp.mapDerivedCategory.map (adj'.counit.app K)) :=
    isIso_of_source_target_iso_zero _
      (DerivedCategory.isZero_mapDerivedCategory_obj_mapDerivedCategory_obj h₀ _).isoZero
      hK.isoZero
  have hW : IsZero W := DerivedCategory.isZero_of_isZero_mapDerivedCategory_obj hdet
    ((Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      (iUp.mapDerivedCategory.map_distinguished _ hT)).2 hi)
    ((Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      (R.mapDerivedCategory.map_distinguished _ hT)).2 hr)
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 hW

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

attribute [local irreducible] nativeOpenAdjunction

private noncomputable def nativeOpenBaseChangeMap
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {V U P X : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
    [P.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (q : V ⟶ U) (b : V ⟶ P) (j : U ⟶ X) (p : P ⟶ X)
    [q.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    (sq : CommSq q b j p) :
    ProEtaleWeilSheaf.lowerStar k₀ l p ⋙ ProEtaleWeilSheaf.upperStar k₀ l j ⟶
      ProEtaleWeilSheaf.upperStar k₀ l b ⋙ ProEtaleWeilSheaf.lowerStar k₀ l q :=
  inverseMateNatTrans (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l b)
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j)
    (ProEtaleWeilSheaf.lowerStarSquareIso k₀ l sq.w.symm).hom

@[reassoc]
private theorem adicLowerStarCongr_trans
    (l : ℕ) [Fact l.Prime] {P X : Scheme.{u}} {f g h : P ⟶ X}
    (e : f = g) (e' : g = h) (M : ProEtale.AdicSheaf l P) :
    (ProEtale.adicLowerStarCongr l e).hom.app M ≫
      (ProEtale.adicLowerStarCongr l e').hom.app M =
        (ProEtale.adicLowerStarCongr l (e.trans e')).hom.app M := by
  subst e
  subst e'
  apply Mod.hom_ext
  simp only [Mod.comp_hom', ProEtale.adicLowerStarCongr_hom_app_hom,
    ProEtale.lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

private theorem adicLowerStarCongr_inv
    (l : ℕ) [Fact l.Prime] {P X : Scheme.{u}} {f g : P ⟶ X}
    (e : f = g) (M : ProEtale.AdicSheaf l P) :
    (ProEtale.adicLowerStarCongr l e).inv.app M =
      (ProEtale.adicLowerStarCongr l e.symm).hom.app M := by
  subst e
  apply Mod.hom_ext
  rfl

private theorem nativeLowerStarSquareIso_underlying
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {V U P X : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
    [P.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (q : V ⟶ U) (b : V ⟶ P) (j : U ⟶ X) (p : P ⟶ X)
    [q.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    (sq : CommSq q b j p) (M : ProEtaleWeilSheaf k₀ l V) :
    ((ProEtaleWeilSheaf.lowerStarSquareIso k₀ l sq.w.symm).hom.app M).hom.f =
      (ProEtale.adicSquareLowerStarIso l
        (CommSq.mk (show Scheme.Hom.geometricFiberMap q (comp_over q _) ≫
            Scheme.Hom.geometricFiberMap j (comp_over j _) =
          Scheme.Hom.geometricFiberMap b (comp_over b _) ≫
            Scheme.Hom.geometricFiberMap p (comp_over p _) by
          rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
          exact Scheme.Hom.geometricFiberMap_congr sq.w _ _))).hom.app M.carrier := by
  simp only [ProEtaleWeilSheaf.lowerStarSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, IsoAlgebra.comp_hom_f,
    ProEtaleWeilSheaf.lowerStarCompIso_hom_app_hom_f,
    ProEtaleWeilSheaf.lowerStarCompIso_inv_app_hom_f,
    ProEtaleWeilSheaf.lowerStarCongr_hom_app_hom_f,
    Iso.trans_inv, ProEtale.adicSquareLowerStarIso]
  simp only [Category.assoc, adicLowerStarCongr_inv]
  rw [adicLowerStarCongr_trans_assoc, adicLowerStarCongr_trans_assoc]

private theorem nativeUpperStar_map_hom_f
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {V P : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [P.Over (Spec (CommRingCat.of k₀))]
    (b : V ⟶ P) [b.IsOver (Spec (CommRingCat.of k₀))]
    {M N : ProEtaleWeilSheaf k₀ l P} (f : M ⟶ N) :
    ((ProEtaleWeilSheaf.upperStar k₀ l b).map f).hom.f =
      (ProEtale.adicUpperStar l (Scheme.Hom.geometricFiberMap b (comp_over b _))).map
        f.hom.f := rfl

section NativeOpenBaseChange

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {V U P X : Scheme.{u}}
  [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
  [P.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (q : V ⟶ U) (b : V ⟶ P) (j : U ⟶ X) (p : P ⟶ X)
  [q.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
  [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
  [IsOpenImmersion b] [IsOpenImmersion j]

omit [IsOpenImmersion b] [IsOpenImmersion j] in
private theorem nativeOpenBaseChangeMap_underlying (sq : CommSq q b j p)
    (M : ProEtaleWeilSheaf k₀ l P) :
    ((nativeOpenBaseChangeMap k₀ l q b j p sq).app M).hom.f =
      (ProEtale.adicBaseChangeMap l
        (CommSq.mk (show Scheme.Hom.geometricFiberMap q (comp_over q _) ≫
            Scheme.Hom.geometricFiberMap j (comp_over j _) =
          Scheme.Hom.geometricFiberMap b (comp_over b _) ≫
            Scheme.Hom.geometricFiberMap p (comp_over p _) by
          rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
          exact Scheme.Hom.geometricFiberMap_congr sq.w _ _))).app M.carrier := by
  simp only [nativeOpenBaseChangeMap, inverseMateNatTrans,
    ProEtale.adicBaseChangeMap, inverseMate_app,
    IsoAlgebra.comp_hom_f, ProEtaleWeilSheaf.lowerStar_map_hom_f,
    nativeUpperStar_map_hom_f,
    ProEtaleWeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_f,
    ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f]
  rw [nativeLowerStarSquareIso_underlying k₀ l q b j p sq]
  rfl

attribute [local irreducible] nativeOpenBaseChangeMap

private theorem nativeOpenBaseChangeMap_isIso (hsq : IsPullback q b j p) :
    IsIso (nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq) := by
  have hgeo := Scheme.Hom.isPullback_geometricFiberMap_of_isPullback (k := k₀) hsq
    (comp_over q _) (comp_over b _) (comp_over j _) (comp_over p _)
  have := ProEtale.isIso_adicBaseChangeMap_of_isPullback l hgeo
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : IsIso ((IsoAlgebra.forget _).map
      ((nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq).app M)) := by
    change IsIso (((nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq).app M).hom.f)
    rw [nativeOpenBaseChangeMap_underlying]
    infer_instance
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)

private noncomputable def nativeDerivedOpenBaseChangeIso (hsq : IsPullback q b j p) :
    (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
      (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory ≅
        (ProEtaleWeilSheaf.upperStar k₀ l b).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor := by
  have := nativeOpenBaseChangeMap_isIso k₀ l q b j p hsq
  have := (nativeOpenAdjunction k₀ l b).preservesKInjectiveComplexes
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (asIso (nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq)) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (ProEtaleWeilSheaf.upperStar k₀ l b).rightDerivedFunctorIsoMapDerivedCategory _

end NativeOpenBaseChange

private noncomputable def nativeOpenExtensionCompIso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {A B C : Scheme.{u}}
    [A.Over (Spec (CommRingCat.of k₀))] [B.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₀))]
    (s : A ⟶ B) (b : B ⟶ C)
    [s.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion s] [IsOpenImmersion b] :
    ProEtaleWeilSheaf.extensionByZero k₀ l s ⋙
      ProEtaleWeilSheaf.extensionByZero k₀ l b ≅
        ProEtaleWeilSheaf.extensionByZero k₀ l (s ≫ b) :=
  (((nativeOpenAdjunction k₀ l s).comp (nativeOpenAdjunction k₀ l b)).ofNatIsoRight
    (ProEtaleWeilSheaf.upperStarCompIso k₀ l s b).symm).leftAdjointUniq
      (nativeOpenAdjunction k₀ l (s ≫ b))

private noncomputable def nativeOpenFactorRestrictionIso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {A B C : Scheme.{u}}
    [A.Over (Spec (CommRingCat.of k₀))] [B.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₀))]
    (s : A ⟶ B) (b : B ⟶ C) (a : A ⟶ C)
    [s.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [a.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion a] (h : s ≫ b = a) :
    ProEtaleWeilSheaf.extensionByZero k₀ l a ⋙
      ProEtaleWeilSheaf.upperStar k₀ l b ≅
        ProEtaleWeilSheaf.extensionByZero k₀ l s := by
  subst a
  have := nativeOpenAdjunction_unit_isIso k₀ l b
  exact Functor.isoWhiskerRight (nativeOpenExtensionCompIso k₀ l s b).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (nativeOpenAdjunction k₀ l b).unit).symm ≪≫
    Functor.rightUnitor _

private theorem nativeOpenExtension_disjoint
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U X Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) (i : Z ⟶ X)
    [j.IsOver (Spec (CommRingCat.of k₀))] [i.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j] (h : Set.range j.base ∩ Set.range i.base = ∅)
    (M : ProEtaleWeilSheaf k₀ l U) :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l i).obj
      ((ProEtaleWeilSheaf.extensionByZero k₀ l j).obj M)) := by
  apply (ProEtaleWeilSheaf.isZero_iff _).2
  apply ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek
    (Scheme.Hom.geometricFiberMap j (comp_over j _))
    (Scheme.Hom.geometricFiberMap i (comp_over i _)) _ M.carrier
  rw [Scheme.Hom.range_geometricFiberMap, Scheme.Hom.range_geometricFiberMap,
    ← Set.preimage_inter, h]
  simp

private noncomputable def nativeOpenProperRestrictionIso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {U' P U X : Scheme.{u}}
    [U'.Over (Spec (CommRingCat.of k₀))] [P.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (j' : U' ⟶ P) (p' : U' ⟶ U) (j : U ⟶ X) (p : P ⟶ X)
    [j'.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j'] [IsOpenImmersion j] [IsProper p] [IsProper p']
    (hc : j' ≫ p = p' ≫ j) :
    ((ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor) ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory ≅
          (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor := by
  let V := pullback p j
  let b : V ⟶ P := pullback.fst p j
  let q : V ⟶ U := pullback.snd p j
  let s : U' ⟶ V := pullback.lift j' p' hc
  let : V.Over (Spec (CommRingCat.of k₀)) :=
    ⟨b ≫ P ↘ Spec (CommRingCat.of k₀)⟩
  have : b.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : q.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    dsimp only [q, b]
    rw [← comp_over j (Spec (CommRingCat.of k₀)), ← Category.assoc,
      ← pullback.condition, Category.assoc, comp_over]
    rfl⟩
  have hsb : s ≫ b = j' := pullback.lift_fst _ _ _
  have hsq : s ≫ q = p' := pullback.lift_snd _ _ _
  have : s.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change s ≫ b ≫ P ↘ Spec (CommRingCat.of k₀) = _
    rw [← Category.assoc, hsb, comp_over]⟩
  have : IsOpenImmersion b := inferInstanceAs (IsOpenImmersion (pullback.fst p j))
  have : IsProper q := inferInstanceAs (IsProper (pullback.snd p j))
  have : IsOpenImmersion (s ≫ b) := hsb.symm ▸ inferInstance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s b
  have : IsProper (s ≫ q) := hsq.symm ▸ inferInstance
  have : IsProper s := IsProper.of_comp s q
  let eb : (ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.upperStar k₀ l b).mapDerivedCategory ≅
        (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (nativeOpenFactorRestrictionIso k₀ l s b j' hsb)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (nativeDerivedOpenBaseChangeIso k₀ l q b j p
      (IsPullback.of_hasPullback p j).flip) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eb _ ≪≫
    Functor.isoWhiskerRight
      ((ProEtaleWeilSheaf.extensionByZero k₀ l s).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
        Functor.rightDerivedFunctorNatIso
          (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l s))) _ ≪≫
    (ProEtaleWeilSheaf.rightDerivedLowerStarCompIso k₀ l s q).symm ≪≫
    Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l hsq)

attribute [local irreducible] nativeDerivedOpenBaseChangeIso nativeOpenProperRestrictionIso

private theorem nativeProperBoundaryZero
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {U' P U X Z : Scheme.{u}}
    [U'.Over (Spec (CommRingCat.of k₀))] [P.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (P ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    (j' : U' ⟶ P) (p' : U' ⟶ U) (j : U ⟶ X) (p : P ⟶ X) (i : Z ⟶ X)
    [j'.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    [i.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j'] [QuasiCompact j'] [IsOpenImmersion j]
    [IsProper p] [IsClosedImmersion i]
    (hc : j' ≫ p = p' ≫ j)
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : WeilComplex k₀ l U') :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory.obj K.obj))) := by
  let d : pullback p i ⟶ P := pullback.fst p i
  let q : pullback p i ⟶ Z := pullback.snd p i
  let : (pullback p i).Over (Spec (CommRingCat.of k₀)) :=
    ⟨d ≫ P ↘ Spec (CommRingCat.of k₀)⟩
  have : d.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : q.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    dsimp only [q, d]
    rw [← comp_over i (Spec (CommRingCat.of k₀)), ← Category.assoc,
      ← pullback.condition, Category.assoc, comp_over]
    rfl⟩
  have : IsProper q := inferInstanceAs (IsProper (pullback.snd p i))
  have hJK : WeilComplex.objectProperty k₀ l P
      ((ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory.obj K.obj) :=
    ⟨(ProEtaleWeilSheaf.extensionByZero k₀ l j').bounded_mapDerivedCategory_obj K.property.1,
      fun n ↦ (WeilSheaf.objectProperty k₀ l P).prop_of_iso
        (((ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategoryHomologyFunctorIso
          n).app K.obj) (WeilSheaf.isAdicConstructibleSheaf_extensionByZero
            j' _ (K.property.2 n))⟩
  let JK : WeilComplex k₀ l P := ⟨_, hJK⟩
  have hdisj : Set.range j'.base ∩ Set.range d.base = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    rintro x ⟨⟨a, rfl⟩, ⟨z, hz⟩⟩
    have he : i.base (q.base z) = j.base (p'.base a) := by
      calc
        i.base (q.base z) = p.base (d.base z) := by
          exact (congrArg (fun f : pullback p i ⟶ X ↦ f.base z)
            (pullback.condition (f := p) (g := i))).symm
        _ = p.base (j'.base a) := by rw [hz]
        _ = j.base (p'.base a) := congrArg (fun f : U' ⟶ X ↦ f.base a) hc
    exact hij.disjoint.le_bot ⟨⟨q.base z, he⟩, ⟨p'.base a, rfl⟩⟩
  have hz : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l d).mapDerivedCategory.obj JK.obj) :=
    DerivedCategory.isZero_mapDerivedCategory_obj_mapDerivedCategory_obj
      (nativeOpenExtension_disjoint k₀ l j' d hdisj) K.obj
  obtain ⟨e⟩ := WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper
    (f := p) (f' := q) (g := i) (g' := d) inferInstance
    (IsPullback.of_hasPullback p i) JK
  exact ((ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor.map_isZero hz).of_iso
    ((WeilComplex.objectProperty k₀ l Z).ι.mapIso e)

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilComplex

/-- Proper/open interchange for a commutative, possibly non-Cartesian square of finite-type
schemes over a finite field, with proper vertical maps and quasi-compact open horizontal maps.
Both the isomorphism and its inverse are morphisms in the native derived category and hence
include the Weil structure.

Source: Stacks Project, Tag 0F7B, `lemma-shriek-proper-and-open`, for the proper/open pattern;
the native coefficient realization uses the following argument
(blueprint: lem-sf-native-weil-open-proper-interchange).

Proof:
1. Form $V=X'\times_XU$, with $b:V\to X'$ and $q:V\to U$, and let $s:U'\to V$ be induced by
$(j',p')$. The base-change lemma makes $b$ open; $s$ identifies $U'$ with the open subscheme
$j'(U')$ of $V$, since $j'$ factors through $b$ and both are open embeddings. Proper base change
for morphisms of schemes makes $q$ proper, hence separated. Since $qs=p'$ is proper,
proper-over-separated makes $s$ proper; a proper immersion is closed. Thus $s$ is clopen, with
open-and-closed complement $C$ in $V$. These are constructions over $k_0$. All schemes remain
finite type: $q$ and $s$ are proper, and finite-type morphisms compose. Moreover $b$ is
quasi-compact: a quasi-compact open immersion is finite type (locally it is an open embedding,
hence locally of finite type), and finite type is stable under base change. No absolute
separatedness was used.

2. On geometric base changes write the same letters for the maps. The framework identifies the
site of an open with the localized site, and its coefficient ring is the restriction of $B$. The
ringed-site adjunction gives exact functors $a_!\dashv a^*$ for each open $a=j,j',b,s$. These
adjunctions lift to native Weil sheaves: the adjunction bijection sends $u:a_!M\to N$ to $a^*u$
composed with the unit. Naturality of unit and counit under Frobenius identifies the
commuting-structure-map condition on the two sides, so it restricts to a bijection on
equivariant morphisms. Exactness is detected by the exact conservative native forgetful functor.
Both functors preserve quasi-isomorphisms, and adjunction localization gives $J_a\dashv a^*$ in
ordinary native derived categories. The open unit $a^*J_a\cong1$ is the termwise sheaf unit.

3. Apply the arbitrary-ring clopen gluing equivalence to $V=U'\amalg C$ and $B_V$. Since both
components are defined over $k_0$, Frobenius preserves each of them. Under this equivalence a
Frobenius isomorphism is a pair of Frobenius isomorphisms; imposing the commuting condition on a
morphism also does so componentwise. We therefore obtain the same exact product equivalence for
native Weil sheaves. In it $s_!$ is $M\mapsto(M,0)$, also equal to $s_*$, and $s^*$ is first
projection. Thus $s_!$ is right adjoint to the exact $s^*$. The right-adjoint lemma shows that
$s_!$ preserves K-injectives. Likewise $b^*$ preserves K-injectives, since it is right adjoint
to the exact $b_!$ of step 2.

4. Let $K\in\mathrm{WC}^{\mathrm{der}}(U')$. Native sheaf categories are Grothendieck abelian,
so the general functorial-resolution lemma supplies a native K-injective representative $I$ for
$K$, and a K-injective resolution $t:j'_!I\to L$ on $X'$. The sheaf adjunctions of step 2 give,
naturally in $M,N$,
$$\operatorname{Hom}(b_!s_!M,N)\cong\operatorname{Hom}(M,s^*b^*N)=\operatorname{Hom}(M,j'^*N)\co
ng\operatorname{Hom}(j'_!M,N).$$
Thus $b_!s_!\cong j'_!$ by uniqueness of a left adjoint; applying $b^*$ and its invertible open
unit gives $b^*j'_!\cong s_!$ already on sheaves, hence termwise. Both $s_!I$ and $b^*L$ are
K-injective by step 3. Therefore $b^*t:s_!I\to b^*L$ is a quasi-isomorphism between K-injectives
and is a homotopy equivalence. Applying the additive functor $q_*$ keeps it a homotopy
equivalence.

5. Direct image and open restriction give $j^*p_*L=q_*b^*L$: on an object $T\to\bar U$ both
sides evaluate $L$ on $T\times_{\bar X}\bar X'$. The coefficient actions are the same
precomposition of locally finite functions. The clopen section formula gives $q_*s_!I=p'_*I$:
evaluation on $T\times_{\bar U}\bar V$ takes the product of $I(T\times_{\bar U}\bar U')$ with
the zero module from $C$. These identities respect Frobenius, since the fibre-product
identifications commute with its action. The homotopy equivalence of step 4 and the K-injective
evaluation of total right derived functors now give an isomorphism
$$r_K:j^*Rp_*J_{j'}K\xrightarrow{\sim}Rp'_*K.$$ It is natural: a morphism of derived inputs is
represented by a unique homotopy class between their K-injective representatives; applying the
displayed section identities to that class commutes with $t$. Changing the resolutions gives the
same morphism by the same unique homotopy comparison. This calculation requires no proper
base-change assertion for arbitrary unbounded modules.

6. Define $\gamma_K:J_jRp'_*K\to Rp_*J_{j'}K$ to be the adjunct of $r_K^{-1}$ under the native
derived adjunction of step 2. It is natural in $K$, since $r$ and that adjunction are natural.
If $\eta$ is the open unit, its defining equality is $j^*\gamma_K\circ\eta_{Rp'_*K}=r_K^{-1}$.
The unit is invertible, so $j^*\gamma_K$ is an isomorphism. This constructs an actual native
morphism; no lifting of an underlying derived morphism through a forgetful functor is being
assumed.

7. Write $\operatorname{For}$ for forgetting the Weil structure, also on derived categories. The
underlying module-sheaf categories on the chosen small pro-etale sites are Grothendieck abelian
by the arbitrary-ringed-site theorem, and Frobenius pullbacks are additive autoequivalences (the
geometric Frobenius is a scheme automorphism). Thus the fixed-pair comparison applies to the
actual left exact direct image: it gives a natural identification $\operatorname{For}Rp_*\cong
R\bar p_*\operatorname{For}$, and derived forgetting is conservative. It commutes with termwise
open extension and restriction directly from the definition of the lifted operations. We use
this comparison to prove vanishing of objects and finally to detect invertibility of the already
constructed $\gamma$, not to infer equality of native morphisms from their underlying morphisms.

8. Give $Z=X\setminus j(U)$ its reduced induced closed subscheme structure $i:Z\hookrightarrow
X$. Put $P=X'\times_XZ$, with $d:P\hookrightarrow X'$ and $p_Z:P\to Z$. Base change makes $d$
closed and $p_Z$ proper; $P$ is complementary to the open $b:V\hookrightarrow X'$. Closed
immersions are quasi-compact: over an affine they are
$\operatorname{Spec}(A/I)\to\operatorname{Spec}A$. They are proper and thus finite type;
consequently $Z,P$ are finite type over $k_0$. After base change to the algebraic closure $k$,
the base $\bar X$ is finite type over $k$, $\bar p$ is proper and $\bar i$ is a quasi-compact
closed (in particular locally closed) immersion. On $\bar Z,\bar P$ retain the inverse-image
rings $\bar i^{-1}B_X,\bar d^{-1}B_{X'}$; no identification with $B_Z,B_P$ or scalar-extension
assertion is needed.

9. First take a constructible native sheaf $F$ on $U'$, in degree zero, and put
$M=\operatorname{For}(j'_!F)$. Exact constructibility preservation for the native open extension
says that $M$ satisfies precisely the finite locally closed stratification and pro-etale locally
finite-free hypothesis of continuous-adic proper base change. The ring $\mathcal R_{\bar X'}$
there is $B_{X'}$ here: its presheaf consists of the same locally finite-span continuous
functions, already a sheaf in the framework. Since $j'=bs$, $M=b_!\operatorname{For}(s_!F)$, so
the ringed open-closed vanishing gives $\bar d^{-1}M=0$. Apply continuous-adic proper base
change with $p=\bar p$, $h=\bar i$ and this sheaf $M$ to obtain $$\bar i^{-1}R\bar
p_*(M[0])\cong Rp_{\bar Z*}((\bar d^{-1}M)[0])=0.$$ By step 7 this is $\bar
i^{-1}\operatorname{For}(Rp_*J_{j'}(F[0]))=0$. Only a constructible sheaf in degree zero has
been passed to that base-change lemma.

10. Set $T(K)=\bar i^{-1}\operatorname{For}(Rp_*J_{j'}K)$. On $D^+(\mathcal W_{U'})$ this is
triangulated: $j'_!$, forgetting, and the topos inverse image with inverse-image coefficients
are exact, and the right derived functor of the additive left exact $p_*$ is triangulated on
$D^+$: its hypothesis holds because $\mathcal W_{X'}$ is Grothendieck abelian and hence has
enough injectives. Choose $a\le b$ containing the cohomological support of $K$. The canonical
truncation triangle for each $n$ has third term $H^n(K)[-n]$. Start with $\tau_{\le a-1}K=0$,
which follows from the cohomology isomorphism criterion. Suppose $T(\tau_{\le n-1}K)=0$. The
sheaf $H^n(K)$ is constructible by the definition of the source category, so step 9 and shift
compatibility give $T(H^n(K)[-n])=0$. Apply $T$ to that triangle: its long exact cohomology
sequence forces all cohomology of $T(\tau_{\le n}K)$ to vanish, hence that object is zero.
Finite induction up to $b$, with $\tau_{\le b}K\cong K$, proves $T(K)=0$. This finite argument
makes no assertion for an arbitrary unbounded source.

11. The closed restriction of $\operatorname{For}(J_jRp'_*K)$ is zero termwise by $\bar
i^{-1}\bar j_!=0$; that of $\operatorname{For}(Rp_*J_{j'}K)$ is zero by step 10. The open
restriction of $\operatorname{For}(\gamma_K)$ is an isomorphism by step 6. Exact inverse images
commute with cohomology, as follows by applying them to kernels and images. For any $n$ put
$N=H^n\operatorname{For}(J_jRp'_*K)$ and $N'=H^n\operatorname{For}(Rp_*J_{j'}K)$. Both closed
restrictions vanish. The ringed open-closed localization sequence consequently identifies the
counits $\bar j_!\bar j^{-1}N\to N$ and $\bar j_!\bar j^{-1}N'\to N'$ as isomorphisms. Their
naturality identifies $H^n\operatorname{For}(\gamma_K)$ with extension by zero of its open
restriction, an isomorphism. The cohomology criterion implies that
$\operatorname{For}(\gamma_K)$ is invertible, and conservative derived forgetting implies that
$\gamma_K$ is invertible in $D(\mathcal W_X)$. These components give the required natural
isomorphism; naturality of the inverse follows by multiplying the naturality square by the
component inverses. Those inverses are native morphisms too, so include Frobenius compatibility.
-/
theorem nonempty_extensionByZero_rightDerivedLowerStar_iso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {U' X' U X : Scheme.{u}}
    [U'.Over (Spec (CommRingCat.of k₀))] [X'.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (j' : U' ⟶ X') (p' : U' ⟶ U) (p : X' ⟶ X) (j : U ⟶ X)
    [j'.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
    [p.IsOver (Spec (CommRingCat.of k₀))] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsProper p] [IsProper p'] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion j'] [QuasiCompact j'] (hcomm : j' ≫ p = p' ≫ j) :
    Nonempty
      ((WeilComplex.objectProperty k₀ l U').ι ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ≅
        (WeilComplex.objectProperty k₀ l U').ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor) := by
  let C : TopologicalSpace.Closeds X :=
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let Z := (Scheme.IdealSheafData.vanishingIdeal C).subscheme
  let i : Z ⟶ X := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have : IsClosedImmersion i :=
    inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal C).subschemeι)
  let : Z.Over (Spec (CommRingCat.of k₀)) := ⟨i ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (i ≫ X ↘ Spec (CommRingCat.of k₀)))
  have hrange : Set.range i.base = (Set.range j.base)ᶜ :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (by simp [Scheme.IdealSheafData.coe_support_vanishingIdeal, C])
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [hrange]
    exact isCompl_compl.symm
  let I := (WeilComplex.objectProperty k₀ l U').ι
  let F := (ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory ⋙
    (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor
  let R := (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory
  let J := (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory
  let P' := (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor
  let adj := nativeOpenAdjunction k₀ l j
  have := nativeOpenAdjunction_unit_isIso k₀ l j
  let adj' : J ⊣ R := adj.exactDerivedAdjunction
  let r : F ⋙ R ≅ P' := nativeOpenProperRestrictionIso k₀ l j' p' j p hcomm
  let ε : (I ⋙ F) ⋙ (R ⋙ J) ⟶ (I ⋙ F) ⋙ 𝟭 _ :=
    Functor.whiskerLeft (I ⋙ F) adj'.counit
  have hε : IsIso ε := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact adj.exactDerivedAdjunction_counit_isIso_of_isZero
      (ProEtaleWeilSheaf.upperStar k₀ l i)
      (nativeOpenExtension_disjoint k₀ l j i (by
        rw [Set.inter_comm]
        exact hij.disjoint.eq_bot))
      (ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij)
      (nativeProperBoundaryZero k₀ l j' p' j p i hcomm hij K)
  change Nonempty (I ⋙ P' ⋙ J ≅ I ⋙ F)
  exact ⟨Functor.isoWhiskerLeft I
      (Functor.isoWhiskerRight r.symm J ≪≫ Functor.associator F R J) ≪≫
    (Functor.associator I F (R ⋙ J)).symm ≪≫ asIso ε ≪≫
    Functor.rightUnitor (I ⋙ F)⟩

end AlgebraicGeometry.WeilComplex
