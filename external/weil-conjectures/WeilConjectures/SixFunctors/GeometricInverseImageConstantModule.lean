/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.LeftExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.ConstantLeftModuleTransport
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.Algebra.Category.ModuleCat.Biproducts

set_option linter.privateModule false

/-!
# Geometric inverse image preserves constant module sheaves

Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV
(auxiliary; not a blueprint node).

The constant module sheaf is represented by `siteConstantModuleFunctorGeneral`. The
recorded geometric-morphism lift supplies the module inverse image and its underlying
set comparison; the theorem states the resulting canonical constant-module
isomorphisms and their naturality in the coefficient module.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private def pointCofan (E : Type u) : Cofan (fun _ : E ↦ PUnit.{u + 1}) :=
  Cofan.mk E (fun e ↦ TypeCat.ofHom (fun _ ↦ e))

private def pointCofanIsColimit (E : Type u) : IsColimit (pointCofan E) :=
  Cofan.IsColimit.mk _ (fun s ↦ TypeCat.ofHom (fun e ↦ s.inj e PUnit.unit))
    (by intros; ext x; cases x; rfl)
    (by intro s f h; ext e; exact ConcreteCategory.congr_hom (h e) PUnit.unit)

private def mapPointCofanIsColimit {A : Type*} [Category A]
    (F : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F] (E : Type u) :
    IsColimit (Cofan.mk (F.obj E)
      (fun e : E ↦ F.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ e)))) :=
  isColimitCofanMkObjOfIsColimit F _ _ (pointCofanIsColimit E)

private def pointComparisonHom {A : Type*} [Category A]
    (F G : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F]
    (p : F.obj PUnit.{u + 1} ⟶ G.obj PUnit.{u + 1}) (E : Type u) : F.obj E ⟶ G.obj E :=
  (mapPointCofanIsColimit F E).desc (Cofan.mk (G.obj E)
    (fun e ↦ p ≫ G.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ e))))

private theorem pointComparisonHom_fac {A : Type*} [Category A]
    (F G : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F]
    (p : F.obj PUnit.{u + 1} ⟶ G.obj PUnit.{u + 1}) (E : Type u) (e : E) :
    F.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ e)) ≫ pointComparisonHom F G p E =
      p ≫ G.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ e)) :=
  (mapPointCofanIsColimit F E).fac _ (Discrete.mk e)

private def pointComparison {A : Type*} [Category A]
    (F G : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F]
    [PreservesColimitsOfSize.{u, u} G] (p : F.obj PUnit.{u + 1} ≅ G.obj PUnit.{u + 1})
    (E : Type u) : F.obj E ≅ G.obj E where
  hom := pointComparisonHom F G p.hom E
  inv := pointComparisonHom G F p.inv E
  hom_inv_id := by
    apply Cofan.IsColimit.hom_ext (mapPointCofanIsColimit F E)
    intro e
    dsimp
    rw [← Category.assoc, pointComparisonHom_fac, Category.assoc, pointComparisonHom_fac]
    simp
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext (mapPointCofanIsColimit G E)
    intro e
    dsimp
    rw [← Category.assoc, pointComparisonHom_fac, Category.assoc, pointComparisonHom_fac]
    simp

private def pointComparisonNatIso {A : Type*} [Category A]
    (F G : Type u ⥤ A) [PreservesColimitsOfSize.{u, u} F]
    [PreservesColimitsOfSize.{u, u} G] (p : F.obj PUnit.{u + 1} ≅ G.obj PUnit.{u + 1}) :
    F ≅ G :=
  NatIso.ofComponents (pointComparison F G p) (by
    intro E E' f
    apply Cofan.IsColimit.hom_ext (mapPointCofanIsColimit F E)
    intro e
    dsimp [pointComparison]
    rw [← Category.assoc, ← F.map_comp]
    change F.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ f e)) ≫ _ = _
    rw [pointComparisonHom_fac, ← Category.assoc, pointComparisonHom_fac,
      Category.assoc, ← G.map_comp]
    rfl)

private def naturalAdditiveMap
    (R : Type u) [CommRing R] (F G : ModuleCat.{u} R ⥤ AddCommGrpCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (n : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) : F ⟶ G := by
  let E := AddCommGrpCat.leftExactFunctorForgetEquivalence (ModuleCat.{u} R)
  let n' : E.functor.obj (LeftExactFunctor.of F) ⟶
      E.functor.obj (LeftExactFunctor.of G) := ObjectProperty.homMk n
  exact (E.functor.preimage n').hom

private theorem naturalAdditiveMap_forget
    (R : Type u) [CommRing R] (F G : ModuleCat.{u} R ⥤ AddCommGrpCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (n : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) :
    Functor.whiskerRight (naturalAdditiveMap R F G n) (forget AddCommGrpCat) = n := by
  let E := AddCommGrpCat.leftExactFunctorForgetEquivalence (ModuleCat.{u} R)
  let n' : E.functor.obj (LeftExactFunctor.of F) ⟶
      E.functor.obj (LeftExactFunctor.of G) := ObjectProperty.homMk n
  exact congrArg (fun f ↦ f.hom) (E.functor.map_preimage n')

private def abelianLiftSetNatTrans
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    (R : Type u) [CommRing R]
    (F G : ModuleCat.{u} R ⥤ Sheaf K AddCommGrpCat.{u})
    [∀ U : Dᵒᵖ, PreservesFiniteLimits (F ⋙ (sheafSections K AddCommGrpCat).obj U)]
    [∀ U : Dᵒᵖ, PreservesFiniteLimits (G ⋙ (sheafSections K AddCommGrpCat).obj U)]
    (n : F ⋙ ConstantLeftModuleInverseImage.U K ⟶
      G ⋙ ConstantLeftModuleInverseImage.U K) : F ⟶ G := by
  let a (U : Dᵒᵖ) := naturalAdditiveMap R
    (F ⋙ (sheafSections K AddCommGrpCat).obj U)
    (G ⋙ (sheafSections K AddCommGrpCat).obj U)
    (Functor.whiskerRight n ((sheafSections K (Type u)).obj U))
  have ha (U : Dᵒᵖ) (M : ModuleCat.{u} R) :
      (forget AddCommGrpCat).map ((a U).app M) = (n.app M).hom.app U := by
    exact congrArg (fun t ↦ t.app M) (naturalAdditiveMap_forget R
      (F ⋙ (sheafSections K AddCommGrpCat).obj U)
      (G ⋙ (sheafSections K AddCommGrpCat).obj U)
      (Functor.whiskerRight n ((sheafSections K (Type u)).obj U)))
  refine
    { app := fun M ↦
        { hom :=
            { app := fun U ↦ (a U).app M
              naturality := ?_ } }
      naturality := ?_ }
  · rename_i M
    intro U V f
    apply (forget AddCommGrpCat).map_injective
    change (forget AddCommGrpCat).map ((F.obj M).obj.map f) ≫
        (forget AddCommGrpCat).map ((a V).app M) =
      (forget AddCommGrpCat).map ((a U).app M) ≫
        (forget AddCommGrpCat).map ((G.obj M).obj.map f)
    rw [ha, ha]
    exact (n.app M).hom.naturality f
  · intro M N f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply (forget AddCommGrpCat).map_injective
    change (forget AddCommGrpCat).map ((F.map f).hom.app U) ≫
        (forget AddCommGrpCat).map ((a U).app N) =
      (forget AddCommGrpCat).map ((a U).app M) ≫
        (forget AddCommGrpCat).map ((G.map f).hom.app U)
    rw [ha, ha]
    exact congrArg (fun t ↦ t.hom.app U) (n.naturality f)

private theorem abelianLiftSetNatTrans_forget
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    (R : Type u) [CommRing R]
    (F G : ModuleCat.{u} R ⥤ Sheaf K AddCommGrpCat.{u})
    [∀ U : Dᵒᵖ, PreservesFiniteLimits (F ⋙ (sheafSections K AddCommGrpCat).obj U)]
    [∀ U : Dᵒᵖ, PreservesFiniteLimits (G ⋙ (sheafSections K AddCommGrpCat).obj U)]
    (n : F ⋙ ConstantLeftModuleInverseImage.U K ⟶
      G ⋙ ConstantLeftModuleInverseImage.U K) :
    Functor.whiskerRight (abelianLiftSetNatTrans K R F G n)
      (ConstantLeftModuleInverseImage.U K) = n := by
  apply NatTrans.ext
  funext M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app M) (naturalAdditiveMap_forget R
      (F ⋙ (sheafSections K AddCommGrpCat).obj U)
      (G ⋙ (sheafSections K AddCommGrpCat).obj U)
      (Functor.whiskerRight n ((sheafSections K (Type u)).obj U)))

private def constantScalar (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (r : R) :
    M ⟶ M := ModuleCat.ofHom (LinearMap.lsmul R M r)

end CategoryTheory
