/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# The derived base change map `g^* Rf_* ⟶ Rf'_* g'^*` on `D⁺`

For a commutative square of schemes `g' ≫ f = f' ≫ g` (notation as in
`WeilConjectures.SixFunctors.BaseChange.Square`) the pullbacks `g^*`, `g'^*` are exact and
descend to the bounded below derived categories as `D g^*⁺`, `D g'^*⁺`
(`CategoryTheory.Functor.mapDerivedCategoryPlus`), and the pushforwards have bounded below
right derived functors `R f_*⁺`, `R f'_*⁺` (`CategoryTheory.Functor.rightDerivedFunctorPlus`).

The **derived base change map** `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus sq :
R f_*⁺ ⋙ D g^*⁺ ⟶ D g'^*⁺ ⋙ R f'_*⁺` is defined by the universal property of the right
derived functor: `R f_*⁺ ⋙ D g^*⁺` is a right derived functor of `f_* ⋙ Qh ⋙ D g^*⁺` (the
unit of `R f_*⁺` is an isomorphism on injective complexes), and the derived base change map is
the unique natural transformation out of it which, on the image of a bounded below complex
`K` of sheaves on `X`, restricts along the unit `g^* f_* K ⟶ g^* R f_*⁺ K` to the levelwise
underived base change map `g^* f_* K ⟶ f'_* g'^* K` followed by the unit
`f'_* g'^* K ⟶ R f'_*⁺ (g'^* K)`, modulo the isomorphisms
`Functor.mapDerivedCategoryPlusFactorsh`
(`AlgebraicGeometry.Etale.baseChangeMapHomotopyPlus`,
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app`,
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_ext`). This is the statement that the
derived base change map is computed by the underived one on injective resolutions.

If the pushforwards `f_*` and `f'_*` are exact (e.g. `f` finite), no resolutions are needed:
the derived base change map is an isomorphism as soon as the underived one is
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIso_baseChangeMap`).

Finally, `AlgebraicGeometry.Etale.IsBaseChangeIso A f` is the property that the derived base
change map is an isomorphism for every cartesian square on `f`, and
`AlgebraicGeometry.Etale.IsBaseChangeIsoSheaf A f` the corresponding property of the underived
map.
(blueprint: `definition-derived-base-change-map`, `prose-04-06`,
`def:weil-pbc-property`)

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

section Derived

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The unit exhibiting `R f_*⁺ ⋙ D g^*⁺` as a right derived functor of
`f_* ⋙ Qh ⋙ D g^*⁺`: the unit of `R f_*⁺` whiskered with `D g^*⁺`
(`CategoryTheory.Functor.isRightDerivedFunctor_rightDerivedFunctorPlus_comp_right`). -/
noncomputable abbrev Etale.rightDerivedLowerStarPlusCompUpperStarUnit (f : X ⟶ Y) (g : Y' ⟶ Y) :
    (f)_*[A].mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
        ((g)^*[A]).mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ (f)_*[A].rightDerivedFunctorPlus ⋙
        ((g)^*[A]).mapDerivedCategoryPlus :=
  Functor.whiskerRight (f)_*[A].rightDerivedFunctorPlusUnith ((g)^*[A]).mapDerivedCategoryPlus ≫
    (Functor.associator _ _ _).hom

instance Etale.isRightDerivedFunctor_rightDerivedLowerStarPlus_comp_upperStar
    (f : X ⟶ Y) (g : Y' ⟶ Y) :
    ((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus).IsRightDerivedFunctor
      (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g)
      (HomotopyCategory.Plus.quasiIso _) :=
  inferInstance

/-- **The base change map on the homotopy category**: the natural transformation
`f_* ⋙ Qh ⋙ D g^*⁺ ⟶ Qh ⋙ D g'^*⁺ ⋙ R f'_*⁺` which on a bounded below complex `K` is the
levelwise underived base change map `g^* f_* K ⟶ f'_* g'^* K` followed by the unit
`f'_* g'^* K ⟶ R f'_*⁺ (g'^* K)`, modulo the isomorphisms
`Functor.mapDerivedCategoryPlusFactorsh`
(`AlgebraicGeometry.Etale.baseChangeMapHomotopyPlus_app`). -/
noncomputable def Etale.baseChangeMapHomotopyPlus (sq : CommSq g' f' f g) :
    (f)_*[A].mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
        ((g)^*[A]).mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ ((g')^*[A]).mapDerivedCategoryPlus ⋙
        (f')_*[A].rightDerivedFunctorPlus :=
  Functor.whiskerLeft (f)_*[A].mapHomotopyCategoryPlus
      ((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl ((f)_*[A] ⋙ (g)^*[A]))).hom DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl ((g')^*[A] ⋙ (f')_*[A]))).inv DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((g')^*[A]).mapHomotopyCategoryPlus
      (f')_*[A].rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv
      (f')_*[A].rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

omit [HasSmallSiteSheafify A] in
/-- The components of `AlgebraicGeometry.Etale.baseChangeMapHomotopyPlus`. -/
lemma Etale.baseChangeMapHomotopyPlus_app (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.baseChangeMapHomotopyPlus A sq).app K =
      ((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app K) ≫
        (f')_*[A].rightDerivedFunctorPlusUnith.app (((g')^*[A]).mapHomotopyCategoryPlus.obj K) ≫
        (f')_*[A].rightDerivedFunctorPlus.map
          (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp only [Etale.baseChangeMapHomotopyPlus, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, id_comp, comp_id]
  simp

/-- **The derived base change map** `g^* R f_* ⟶ R f'_* g'^*` on the bounded below derived
categories, as a natural transformation `R f_*⁺ ⋙ D g^*⁺ ⟶ D g'^*⁺ ⋙ R f'_*⁺`: the natural
transformation out of the right derived functor `R f_*⁺ ⋙ D g^*⁺` of `f_* ⋙ Qh ⋙ D g^*⁺`
induced by `AlgebraicGeometry.Etale.baseChangeMapHomotopyPlus`.
(blueprint: `definition-derived-base-change-map`) -/
noncomputable def Etale.derivedBaseChangeMapPlus (sq : CommSq g' f' f g) :
    (f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus ⟶
      ((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc _ (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g)
    (HomotopyCategory.Plus.quasiIso _) _ (Etale.baseChangeMapHomotopyPlus A sq)

omit [HasSmallSiteSheafify A] in
/-- **The derived base change map is computed by the underived one on resolutions**: for a
bounded below complex `K` of sheaves on `X`, the composite of `D g^*⁺` of the unit
`f_* K ⟶ R f_*⁺ K` with the derived base change map is the levelwise underived base change
map followed by the unit `f'_* g'^* K ⟶ R f'_*⁺ (g'^* K)`, modulo the isomorphisms
`Functor.mapDerivedCategoryPlusFactorsh`. In particular, if `K` is a bounded below complex of
injectives, this computes the derived base change map on `K`.
(blueprint: `prose-04-06`) -/
@[reassoc]
lemma Etale.derivedBaseChangeMapPlus_fac_app (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ((g)^*[A]).mapDerivedCategoryPlus.map ((f)_*[A].rightDerivedFunctorPlusUnith.app K) ≫
        (Etale.derivedBaseChangeMapPlus A sq).app (DerivedCategory.Plus.Qh.obj K) =
      ((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app K) ≫
        (f')_*[A].rightDerivedFunctorPlusUnith.app (((g')^*[A]).mapHomotopyCategoryPlus.obj K) ≫
        (f')_*[A].rightDerivedFunctorPlus.map
          (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K) := by
  rw [← Etale.baseChangeMapHomotopyPlus_app, Etale.derivedBaseChangeMapPlus,
    ← Functor.rightDerived_fac_app _ (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g)
      (HomotopyCategory.Plus.quasiIso _) _ (Etale.baseChangeMapHomotopyPlus A sq) K]
  simp only [Etale.rightDerivedLowerStarPlusCompUpperStarUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, comp_id]

omit [HasSmallSiteSheafify A] in
/-- **Uniqueness of the derived base change map**: a natural transformation
`R f_*⁺ ⋙ D g^*⁺ ⟶ D g'^*⁺ ⋙ R f'_*⁺` satisfying the formula
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app` on every bounded below complex is
the derived base change map. (blueprint: `lemma-identity-pasting`)
(blueprint: `prose-04-06`) -/
lemma Etale.derivedBaseChangeMapPlus_ext (sq : CommSq g' f' f g)
    (δ : (f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus ⟶
      ((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus)
    (hδ : ∀ K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A),
      ((g)^*[A]).mapDerivedCategoryPlus.map ((f)_*[A].rightDerivedFunctorPlusUnith.app K) ≫
        δ.app (DerivedCategory.Plus.Qh.obj K) =
      ((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app K) ≫
        (f')_*[A].rightDerivedFunctorPlusUnith.app
          (((g')^*[A]).mapHomotopyCategoryPlus.obj K) ≫
        (f')_*[A].rightDerivedFunctorPlus.map
          (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K)) :
    δ = Etale.derivedBaseChangeMapPlus A sq := by
  refine Functor.rightDerived_ext _ (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g)
    (HomotopyCategory.Plus.quasiIso _) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Etale.rightDerivedLowerStarPlusCompUpperStarUnit, Functor.whiskerRight_app,
    Functor.associator_hom_app, comp_id, Functor.comp_obj]
  rw [hδ K, ← Etale.derivedBaseChangeMapPlus_fac_app]

omit [HasSmallSiteSheafify A] in
/-- **The derived base change map commutes with the shifts.** On complexes of injective
sheaves it is computed by the underived base change map and the units of the right derived
functors (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app`), all of which commute with
the shifts; every bounded below complex is quasi-isomorphic to a complex of injective sheaves.
In particular the derived base change map is a morphism of triangulated functors, so it
induces morphisms of triangles and of the associated long exact sequences of homology. -/
instance Etale.commShift_derivedBaseChangeMapPlus (sq : CommSq g' f' f g) :
    NatTrans.CommShift (Etale.derivedBaseChangeMapPlus A sq) ℤ := by
  let inj := (InjectiveObject.ι (Sheaf X.smallEtaleTopology A)).mapHomotopyCategoryPlus
  let α := Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g
  have hfac := Functor.rightDerived_fac _ α (HomotopyCategory.Plus.quasiIso _) _
    (Etale.baseChangeMapHomotopyPlus A sq)
  have hβ : NatTrans.CommShift (Etale.baseChangeMapHomotopyPlus A sq) ℤ := by
    dsimp only [Etale.baseChangeMapHomotopyPlus]
    infer_instance
  have hα : NatTrans.CommShift α ℤ := by
    have : α = (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (f)_*[A].rightDerivedFunctorPlusUnith
          ((g)^*[A]).mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom := by
      ext K
      simp [α]
    rw [this]
    infer_instance
  have : IsIso (Functor.whiskerLeft inj α) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K ↦ ?_)
    dsimp [α]
    infer_instance
  have h₁ : NatTrans.CommShift (Functor.whiskerLeft inj
      (Functor.whiskerLeft DerivedCategory.Plus.Qh (Etale.derivedBaseChangeMapPlus A sq))) ℤ := by
    have : Functor.whiskerLeft inj
        (Functor.whiskerLeft DerivedCategory.Plus.Qh (Etale.derivedBaseChangeMapPlus A sq)) =
        inv (Functor.whiskerLeft inj α) ≫ Functor.whiskerLeft inj
          (Etale.baseChangeMapHomotopyPlus A sq) := by
      rw [IsIso.eq_inv_comp, ← Functor.whiskerLeft_comp, Etale.derivedBaseChangeMapPlus, hfac]
    rw [this]
    have : NatTrans.CommShift (Functor.whiskerLeft inj α) ℤ := inferInstance
    have : NatTrans.CommShift (inv (Functor.whiskerLeft inj α)) ℤ :=
      NatTrans.CommShift.of_isIso _ _
    infer_instance
  have h₂ : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Plus.Qh (Etale.derivedBaseChangeMapPlus A sq)) ℤ := by
    refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
    let E := DerivedCategory.Plus.injectiveObjectEquivalence (Sheaf X.smallEtaleTopology A)
    obtain ⟨f, hf⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective K
      (inj.obj (E.inverse.obj (DerivedCategory.Plus.Qh.obj K)))
      inferInstance).2 (E.counitIso.inv.app (DerivedCategory.Plus.Qh.obj K))
    refine ⟨_, f, ?_⟩
    rw [Functor.comp_map, hf]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Plus.Qh (fun K ↦ ?_)
  exact ⟨_, (DerivedCategory.Plus.Qh.objObjPreimageIso K).inv, inferInstance⟩

end Derived

section Exact

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

omit [HasSmallSiteSheafify A] in
/-- **Derived base change for exact pushforwards**: if `f_*` and `f'_*` are exact and the
underived base change map is an isomorphism, then so is the derived base change map: no
resolutions are involved, the units `f_* ⟶ R f_*⁺`, `f'_* ⟶ R f'_*⁺` being isomorphisms. -/
lemma Etale.isIso_derivedBaseChangeMapPlus_of_isIso_baseChangeMap (sq : CommSq g' f' f g)
    [PreservesFiniteLimits (f)_*[A]] [PreservesFiniteColimits (f)_*[A]]
    [PreservesFiniteLimits (f')_*[A]] [PreservesFiniteColimits (f')_*[A]]
    [IsIso (Etale.baseChangeMap A sq)] :
    IsIso (Etale.derivedBaseChangeMapPlus A sq) := by
  have hα : IsIso (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g) := by
    dsimp only [Etale.rightDerivedLowerStarPlusCompUpperStarUnit]
    infer_instance
  have hβ : IsIso (Etale.baseChangeMapHomotopyPlus A sq) := by
    dsimp only [Etale.baseChangeMapHomotopyPlus]
    infer_instance
  have hfac := Functor.rightDerived_fac _ (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g)
    (HomotopyCategory.Plus.quasiIso _) _ (Etale.baseChangeMapHomotopyPlus A sq)
  have : IsIso (Functor.whiskerLeft DerivedCategory.Plus.Qh
      (Etale.derivedBaseChangeMapPlus A sq)) := by
    rw [Etale.derivedBaseChangeMapPlus]
    have : IsIso (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (Functor.rightDerivedDesc _
        (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g)
        (HomotopyCategory.Plus.quasiIso _) _ (Etale.baseChangeMapHomotopyPlus A sq))) := by
      rw [hfac]; exact hβ
    exact IsIso.of_isIso_comp_left (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f g) _
  have : ∀ Z, IsIso ((Etale.derivedBaseChangeMapPlus A sq).app Z) := fun Z => by
    obtain ⟨K, ⟨e⟩⟩ := (Localization.essSurj DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso _)).mem_essImage Z
    have h := (Etale.derivedBaseChangeMapPlus A sq).naturality e.hom
    rw [← IsIso.eq_inv_comp] at h
    have : IsIso ((Etale.derivedBaseChangeMapPlus A sq).app (DerivedCategory.Plus.Qh.obj K)) :=
      inferInstanceAs (IsIso ((Functor.whiskerLeft DerivedCategory.Plus.Qh
        (Etale.derivedBaseChangeMapPlus A sq)).app K))
    rw [h]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Exact

section Property

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The proper base change property** for the coefficients `A`: for every cartesian square
```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```
the derived base change map `g^* Rf_* ⟶ Rf'_* g'^*` on `D⁺` is an isomorphism.
(blueprint: `def:weil-pbc-property`) -/
class Etale.IsBaseChangeIso : Prop where
  isIso : ∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g), IsIso (Etale.derivedBaseChangeMapPlus A sq.toCommSq)

/-- **The sheaf-level base change property**: for every cartesian square the underived base
change map `g^* f_* ⟶ f'_* g'^*` is an isomorphism. -/
class Etale.IsBaseChangeIsoSheaf : Prop where
  isIso : ∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g), IsIso (Etale.baseChangeMap A sq.toCommSq)

attribute [instance] Etale.IsBaseChangeIso.isIso Etale.IsBaseChangeIsoSheaf.isIso

end Property

end AlgebraicGeometry
