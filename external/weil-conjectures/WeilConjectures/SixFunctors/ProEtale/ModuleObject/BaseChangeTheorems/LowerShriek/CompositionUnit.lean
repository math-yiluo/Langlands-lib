/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeMate

/-!

# Unit laws of the composition isomorphisms of the lower shriek

This file proves the identity equations of the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on bounded constructible `ℚ̄_ℓ`-sheaves, and the compatibility of the
identification `Rf_! ≅ Rf_*` of a proper `f` with composition (blueprint `prop-functor-package`,
clause (3)).

The proofs compute the composition isomorphisms through the triangles of compactifications
`Compactification.Triangle.unitLeft`, `Compactification.Triangle.unitRight` and the triangle of
trivial compactifications of proper morphisms
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle`), whose
composition isomorphisms are computed by the formal unit laws
`CategoryTheory.ExchangeFormalism.compIso_unitLeft_hom_app`,
`CategoryTheory.ExchangeFormalism.compIso_unitRight_hom_app` and
`CategoryTheory.ExchangeFormalism.compIso_ofProper_hom_app`.

## Main results

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_id_left'` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_id_right'`: the identity
  equations of the composition isomorphisms.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp'`: the
  identification `Rf_! ≅ Rf_*` of a proper `f` is compatible with composition.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace CategoryTheory.ExchangeFormalism

universe w v₁ v u'

variable {𝒞 : Type u'} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞} [𝒪.ContainsIdentities]
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

/-- For the triangle of trivial factorizations `X ⟶[𝟙] X ⟶[f] Y`, `Y ⟶[𝟙] Y ⟶[g] S`,
`X ⟶[𝟙] X ⟶[f ≫ g] S`, the identifications `(𝟙)_! ⋙ f_* ≅ f_*` intertwine the composition
isomorphism with the composition isomorphism `(f ≫ g)_* ≅ f_* ⋙ g_*` of the pushforwards. -/
lemma hcomp_shId_eq_compIso_ofProper {X Y S : 𝒞} (f : X ⟶ Y) (g : Y ⟶ S)
    (w : f ≫ 𝟙 Y = 𝟙 X ≫ f) [IsIso (F.baseChange f (𝟙 X) (𝟙 Y) f w)]
    [IsIso (F.exchange f (𝟙 X) (𝟙 Y) f w)] :
    NatTrans.hcomp (Functor.whiskerRight (F.shId X).hom (F.pf f) ≫ (Functor.leftUnitor _).hom)
        (Functor.whiskerRight (F.shId Y).hom (F.pf g) ≫ (Functor.leftUnitor _).hom) =
      (F.compIso (⟨X, Y, X, 𝟙 X, f, 𝟙 Y, g, 𝟙 X, f ≫ g, 𝟙 X, f, Category.id_comp _, rfl, w⟩ :
          ShriekTriangle 𝒪 X Y S)).hom ≫
        (Functor.whiskerRight (F.shId X).hom (F.pf (f ≫ g)) ≫ (Functor.leftUnitor _).hom) ≫
        (F.pfComp' f g (f ≫ g) rfl).hom := by
  ext M
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.id_obj, Functor.comp_obj, Category.assoc,
    F.compIso_ofProper_hom_app f g (f ≫ g) rfl w M]
  erw [Category.id_comp, Category.comp_id, Category.id_comp]
  rw [F.pfComp'_inv_naturality_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end CategoryTheory.ExchangeFormalism

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

section Copy

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The comparison of the chosen compactification of `φ` with the chosen compactification of `ψ`
transported along `φ = ψ` is the identity, up to `eqToHom`. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_copy_hom {φ ψ : X ⟶ Y}
    (e : φ = ψ) :
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (compactificationOverField φ)
        ((compactificationOverField ψ).copy (congrArg (fun φ : X ⟶ Y ↦ φ.left) e))).hom =
      eqToHom (congrArg (boundedConstructibleLowerShriek ℓ) e) := by
  subst e
  exact congrArg Iso.hom
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl ℓ _)

end Copy

section Unit

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The composition isomorphism of the triangle `Compactification.Triangle.unitLeft c` of
`(𝟙 X, f)` is induced by `R(𝟙 X)_* (𝟙 X)_! ≅ 𝟭`. -/
lemma compIso_triangleShriekTriangle_unitLeft_hom_app (f : X ⟶ Y) (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ
      (f := 𝟙 X) (g := f) (Compactification.Triangle.unitLeft c)
    haveI := isIso_exchange_triangleShriekTriangle ℓ
      (f := 𝟙 X) (g := f) (Compactification.Triangle.unitLeft c)
    ((𝔽).compIso (triangleShriekTriangle (f := 𝟙 X) (g := f)
        (Compactification.Triangle.unitLeft c))).hom.app K =
      (boundedConstructibleLowerShriekOfCompactification ℓ c).map
        ((boundedConstructibleLowerStar ℓ (𝟙 X)).map
            (((𝔽).shId (SepFinType.mk X)).hom.app K) ≫
          ((𝔽).pfId (SepFinType.mk X)).hom.app K) := by
  have w : 𝟙 (SepFinType.mk X) ≫ SepFinType.homMk c.overI = SepFinType.homMk c.overI ≫ 𝟙 _ := by
    simp
  have h₁ : IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk c.overI)
      (SepFinType.homMk c.overI) (𝟙 _) w) :=
    isIso_baseChange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
      (Compactification.Triangle.unitLeft c)
  have h₂ : IsIso ((𝔽).exchange (𝟙 (SepFinType.mk X)) (SepFinType.homMk c.overI)
      (SepFinType.homMk c.overI) (𝟙 _) w) :=
    isIso_exchange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
      (Compactification.Triangle.unitLeft c)
  have := isIso_baseChange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
    (Compactification.Triangle.unitLeft c)
  have := isIso_exchange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
    (Compactification.Triangle.unitLeft c)
  have e : ((𝔽).compIso (triangleShriekTriangle (f := 𝟙 X) (g := f)
      (Compactification.Triangle.unitLeft c))).hom =
      ((𝔽).compIso (⟨SepFinType.mk X, SepFinType.mk c.overObj, SepFinType.mk c.overObj, 𝟙 _, 𝟙 _,
        SepFinType.homMk c.overI, SepFinType.homMk c.overG, SepFinType.homMk c.overI,
        SepFinType.homMk c.overG, SepFinType.homMk c.overI, 𝟙 _, Category.id_comp _,
        Category.id_comp _, w⟩ : ExchangeFormalism.ShriekTriangle _ _ _ _)).hom := rfl
  exact (congr_app e K).trans ((𝔽).compIso_unitLeft_hom_app (SepFinType.homMk c.overI)
    (SepFinType.homMk c.overG) w K)

/-- The isomorphism `R(𝟙 X)_!^{𝟙} ≅ R(𝟙 X)_*` of the trivial compactification of `𝟙 X`, followed
by `R(𝟙 X)_* ≅ 𝟭`, is `R(𝟙 X)_* (𝟙 X)_! ≅ 𝟭` of the exchange formalism. -/
lemma boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_id_hom_app_comp
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ (𝟙 X)).hom.app K ≫
        (boundedConstructibleLowerStarId ℓ X).hom.app K =
      (boundedConstructibleLowerStar ℓ (𝟙 X)).map (((𝔽).shId (SepFinType.mk X)).hom.app K) ≫
        ((𝔽).pfId (SepFinType.mk X)).hom.app K := by
  rw [boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_hom_eq ℓ (g := 𝟙 X),
    boundedConstructibleLowerStarId_eq_pfId]
  simp

/-- The composition isomorphism `R(𝟙 ≫ f)_! ≅ R(𝟙)_! ⋙ Rf_!` through the triangle
`Compactification.Triangle.unitLeft` of the chosen compactification of `f`. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_id_left_hom_eq (f : X ⟶ Y) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
      (Compactification.Triangle.unitLeft (compactificationOverField f))
    haveI := isIso_exchange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
      (Compactification.Triangle.unitLeft (compactificationOverField f))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 X) f).hom =
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField (𝟙 X ≫ f))
          ((compactificationOverField f).copy
            (congrArg (fun φ : X ⟶ Y ↦ φ.left) (Category.id_comp f)))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (f := 𝟙 X) (g := f)
          (Compactification.Triangle.unitLeft (compactificationOverField f)))).inv ≫
        Functor.whiskerRight (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (.ofIsProper (𝟙 X : X ⟶ X).left) (compactificationOverField (𝟙 X))).hom
          (boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f)) := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
    (Compactification.Triangle.unitLeft (compactificationOverField f))
  have := isIso_exchange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
    (Compactification.Triangle.unitLeft (compactificationOverField f))
  have hT : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 X) f).hom =
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField (𝟙 X ≫ f))
          ((compactificationOverField f).copy
            (congrArg (fun φ : X ⟶ Y ↦ φ.left) (Category.id_comp f)))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (f := 𝟙 X) (g := f)
          (Compactification.Triangle.unitLeft (compactificationOverField f)))).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (.ofIsProper (𝟙 X : X ⟶ X).left) (compactificationOverField (𝟙 X))).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (compactificationOverField f) (compactificationOverField f)).hom :=
    boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ (𝟙 X) f
      (Compactification.Triangle.unitLeft (compactificationOverField f))
  rw [boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl, Iso.refl_hom] at hT
  erw [Functor.hcomp_id (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
    (.ofIsProper (𝟙 X : X ⟶ X).left) (compactificationOverField (𝟙 X))).hom
    (boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f))] at hT
  exact hT

/-- **Left identity equation of the composition isomorphisms of the lower shriek** (blueprint
`prop-functor-package`, clause (3)): `R(𝟙 ≫ f)_! ≅ R(𝟙)_! ⋙ Rf_! ≅ R(𝟙)_* ⋙ Rf_! ≅ Rf_!` is
the identity. -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_id_left' (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 X) f).hom.app K ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X)).hom.app K ≫
            (boundedConstructibleLowerStarId ℓ X).hom.app K) =
      eqToHom (by rw [Category.id_comp]; rfl) := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
    (Compactification.Triangle.unitLeft (compactificationOverField f))
  have := isIso_exchange_triangleShriekTriangle ℓ (f := 𝟙 X) (g := f)
    (Compactification.Triangle.unitLeft (compactificationOverField f))
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_id_left_hom_eq,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_copy_hom ℓ
      (Category.id_comp f),
    boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq]
  simp only [NatTrans.comp_app, eqToHom_app, Category.assoc, Iso.trans_hom]
  erw [Functor.whiskerRight_app (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
    (.ofIsProper (𝟙 X : X ⟶ X).left) (compactificationOverField (𝟙 X))).hom
    (boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f)) K]
  have h₁ : (boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f)).map
        ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (.ofIsProper (𝟙 X : X ⟶ X).left) (compactificationOverField (𝟙 X))).hom.app K) ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField (𝟙 X)) (.ofIsProper (𝟙 X : X ⟶ X).left)).hom.app K ≫
          (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ (𝟙 X)).hom.app K ≫
          (boundedConstructibleLowerStarId ℓ X).hom.app K) =
      (boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f)).map
        ((boundedConstructibleLowerStar ℓ (𝟙 X)).map (((𝔽).shId (SepFinType.mk X)).hom.app K) ≫
          ((𝔽).pfId (SepFinType.mk X)).hom.app K) := by
    rw [← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ
      (.ofIsProper (𝟙 X : X ⟶ X).left), Iso.symm_hom,
      boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_id_hom_app_comp]
    refine ((boundedConstructibleLowerShriek ℓ f).map_comp _ _).symm.trans ?_
    rw [Iso.hom_inv_id_app_assoc]
    rfl
  rw [h₁, ← compIso_triangleShriekTriangle_unitLeft_hom_app ℓ f (compactificationOverField f) K,
    Iso.inv_hom_id_app]
  simp

/-- The composition isomorphism of the triangle `Compactification.Triangle.unitRight c` of
`(f, 𝟙 Y)` is induced by `R(𝟙 Y)_* (𝟙 Y)_! ≅ 𝟭`. -/
lemma compIso_triangleShriekTriangle_unitRight_hom_app (f : X ⟶ Y) (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ
      (f := f) (g := 𝟙 Y) (Compactification.Triangle.unitRight c)
    haveI := isIso_exchange_triangleShriekTriangle ℓ
      (f := f) (g := 𝟙 Y) (Compactification.Triangle.unitRight c)
    ((𝔽).compIso (triangleShriekTriangle (f := f) (g := 𝟙 Y)
        (Compactification.Triangle.unitRight c))).hom.app K =
      (boundedConstructibleLowerStar ℓ (𝟙 Y)).map
          (((𝔽).shId (SepFinType.mk Y)).hom.app
            ((boundedConstructibleLowerShriekOfCompactification ℓ c).obj K)) ≫
        ((𝔽).pfId (SepFinType.mk Y)).hom.app
          ((boundedConstructibleLowerShriekOfCompactification ℓ c).obj K) := by
  have w : SepFinType.homMk c.overG ≫ 𝟙 (SepFinType.mk Y) =
      𝟙 (SepFinType.mk c.overObj) ≫ SepFinType.homMk c.overG := by
    simp
  have h₁ : IsIso ((𝔽).baseChange (SepFinType.homMk c.overG) (𝟙 _) (𝟙 _)
      (SepFinType.homMk c.overG) w) :=
    isIso_baseChange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
      (Compactification.Triangle.unitRight c)
  have h₂ : IsIso ((𝔽).exchange (SepFinType.homMk c.overG) (𝟙 _) (𝟙 _)
      (SepFinType.homMk c.overG) w) :=
    isIso_exchange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
      (Compactification.Triangle.unitRight c)
  have := isIso_baseChange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
    (Compactification.Triangle.unitRight c)
  have := isIso_exchange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
    (Compactification.Triangle.unitRight c)
  have e : ((𝔽).compIso (triangleShriekTriangle (f := f) (g := 𝟙 Y)
      (Compactification.Triangle.unitRight c))).hom =
      ((𝔽).compIso (⟨SepFinType.mk c.overObj, SepFinType.mk Y, SepFinType.mk c.overObj,
        SepFinType.homMk c.overI, SepFinType.homMk c.overG, 𝟙 _, 𝟙 _, SepFinType.homMk c.overI,
        SepFinType.homMk c.overG, 𝟙 _, SepFinType.homMk c.overG, Category.comp_id _,
        Category.comp_id _, w⟩ : ExchangeFormalism.ShriekTriangle _ _ _ _)).hom := rfl
  exact (congr_app e K).trans ((𝔽).compIso_unitRight_hom_app (SepFinType.homMk c.overI)
    (SepFinType.homMk c.overG) w K)

/-- The composition isomorphism of `Compactification.Triangle.unitRight` for the chosen
compactification of `f`. -/
lemma compIso_triangleShriekTriangle_unitRight_compactificationOverField_hom_app (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ
      (f := f) (g := 𝟙 Y) (Compactification.Triangle.unitRight (compactificationOverField f))
    haveI := isIso_exchange_triangleShriekTriangle ℓ
      (f := f) (g := 𝟙 Y) (Compactification.Triangle.unitRight (compactificationOverField f))
    ((𝔽).compIso (triangleShriekTriangle (f := f) (g := 𝟙 Y)
        (Compactification.Triangle.unitRight (compactificationOverField f)))).hom.app K =
      (boundedConstructibleLowerStar ℓ (𝟙 Y)).map
          (((𝔽).shId (SepFinType.mk Y)).hom.app ((boundedConstructibleLowerShriek ℓ f).obj K)) ≫
        ((𝔽).pfId (SepFinType.mk Y)).hom.app ((boundedConstructibleLowerShriek ℓ f).obj K) :=
  compIso_triangleShriekTriangle_unitRight_hom_app ℓ f (compactificationOverField f) K

/-- The composition isomorphism `R(f ≫ 𝟙)_! ≅ Rf_! ⋙ R(𝟙)_!` through the triangle
`Compactification.Triangle.unitRight` of the chosen compactification of `f`. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_id_right_hom_eq (f : X ⟶ Y) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
      (Compactification.Triangle.unitRight (compactificationOverField f))
    haveI := isIso_exchange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
      (Compactification.Triangle.unitRight (compactificationOverField f))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 Y)).hom =
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField (f ≫ 𝟙 Y))
          ((compactificationOverField f).copy
            (congrArg (fun φ : X ⟶ Y ↦ φ.left) (Category.comp_id f)))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (f := f) (g := 𝟙 Y)
          (Compactification.Triangle.unitRight (compactificationOverField f)))).inv ≫
        Functor.whiskerLeft
          (boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f))
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (.ofIsProper (𝟙 Y : Y ⟶ Y).left) (compactificationOverField (𝟙 Y))).hom := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
    (Compactification.Triangle.unitRight (compactificationOverField f))
  have := isIso_exchange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
    (Compactification.Triangle.unitRight (compactificationOverField f))
  have hT : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 Y)).hom =
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField (f ≫ 𝟙 Y))
          ((compactificationOverField f).copy
            (congrArg (fun φ : X ⟶ Y ↦ φ.left) (Category.comp_id f)))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (f := f) (g := 𝟙 Y)
          (Compactification.Triangle.unitRight (compactificationOverField f)))).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (compactificationOverField f) (compactificationOverField f)).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (.ofIsProper (𝟙 Y : Y ⟶ Y).left) (compactificationOverField (𝟙 Y))).hom :=
    boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ f (𝟙 Y)
      (Compactification.Triangle.unitRight (compactificationOverField f))
  rw [boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl, Iso.refl_hom] at hT
  erw [Functor.id_hcomp
    (boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (.ofIsProper (𝟙 Y : Y ⟶ Y).left) (compactificationOverField (𝟙 Y))).hom] at hT
  exact hT

/-- The comparisons of compactifications of `𝟙 Y` and `R(𝟙 Y)_!^{𝟙} ≅ R(𝟙 Y)_* ≅ 𝟭` after `Rf_!`
are the composition isomorphism of `Compactification.Triangle.unitRight`. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_id_right_aux (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
      (Compactification.Triangle.unitRight (compactificationOverField f))
    haveI := isIso_exchange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
      (Compactification.Triangle.unitRight (compactificationOverField f))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (.ofIsProper (𝟙 Y : Y ⟶ Y).left) (compactificationOverField (𝟙 Y))).hom.app
        ((boundedConstructibleLowerShriekOfCompactification ℓ
          (compactificationOverField f)).obj K) ≫
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (compactificationOverField (𝟙 Y)) (.ofIsProper (𝟙 Y : Y ⟶ Y).left)).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ (𝟙 Y)).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleLowerStarId ℓ Y).hom.app ((boundedConstructibleLowerShriek ℓ f).obj K) =
      ((𝔽).compIso (triangleShriekTriangle (f := f) (g := 𝟙 Y)
        (Compactification.Triangle.unitRight (compactificationOverField f)))).hom.app K := by
  rw [← boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ
    (.ofIsProper (𝟙 Y : Y ⟶ Y).left), Iso.symm_hom]
  erw [Iso.hom_inv_id_app_assoc]
  rw [boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_id_hom_app_comp,
    compIso_triangleShriekTriangle_unitRight_compactificationOverField_hom_app]

/-- **Right identity equation of the composition isomorphisms of the lower shriek** (blueprint
`prop-functor-package`, clause (3)): `R(f ≫ 𝟙)_! ≅ Rf_! ⋙ R(𝟙)_! ≅ Rf_! ⋙ R(𝟙)_* ≅ Rf_!` is
the identity. -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_id_right' (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 Y)).hom.app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 Y)).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
        (boundedConstructibleLowerStarId ℓ Y).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) =
      eqToHom (by rw [Category.comp_id]; rfl) := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
    (Compactification.Triangle.unitRight (compactificationOverField f))
  have := isIso_exchange_triangleShriekTriangle ℓ (f := f) (g := 𝟙 Y)
    (Compactification.Triangle.unitRight (compactificationOverField f))
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_id_right_hom_eq,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_copy_hom ℓ
      (Category.comp_id f),
    boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq]
  simp only [NatTrans.comp_app, eqToHom_app, Category.assoc, Iso.trans_hom]
  erw [Functor.whiskerLeft_app
    (boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (.ofIsProper (𝟙 Y : Y ⟶ Y).left) (compactificationOverField (𝟙 Y))).hom K]
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_id_right_aux, Iso.inv_hom_id_app]
  simp

end Unit

section Proper

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The triangle of trivial compactifications `X ⟶[𝟙] X ⟶[f] Y`, `Y ⟶[𝟙] Y ⟶[g] Z`,
`X ⟶[𝟙] X ⟶[f ≫ g] Z` of proper morphisms `f` and `g`, with `q = 𝟙` and `p = f`. -/
noncomputable abbrev ofIsProperTriangle (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f.left]
    [IsProper g.left] [IsProper (f ≫ g).left] :
    AlgebraicGeometry.Compactification.Triangle f.left g.left where
  cf := .ofIsProper f.left
  cg := .ofIsProper g.left
  cfg := .ofIsProper (f ≫ g).left
  q := 𝟙 X.left
  isOpenImmersion_q := inferInstanceAs (IsOpenImmersion (𝟙 X.left))
  p := f.left
  i_q := Category.id_comp _
  p_g := rfl
  isPullback := IsPullback.of_id_snd

/-- The triangle of factorizations of the triangle of compactifications `ofIsProperTriangle` is
the triangle of trivial factorizations of the exchange formalism. -/
lemma compIso_triangleShriekTriangle_ofIsProperTriangle (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] [IsProper (f ≫ g).left] :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (ofIsProperTriangle f g)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (ofIsProperTriangle f g)
    haveI := (𝔽).isIso_baseChange_id_vert (SepFinType.homMk f)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    haveI := (𝔽).isIso_exchange_id_vert (SepFinType.homMk f)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((𝔽).compIso (triangleShriekTriangle (ofIsProperTriangle f g))).hom =
      ((𝔽).compIso (⟨SepFinType.mk X, SepFinType.mk Y, SepFinType.mk X, 𝟙 _,
        SepFinType.homMk f, 𝟙 _, SepFinType.homMk g, 𝟙 _,
        SepFinType.homMk f ≫ SepFinType.homMk g, 𝟙 _, SepFinType.homMk f, Category.id_comp _,
        rfl, (Category.comp_id _).trans (Category.id_comp _).symm⟩ :
          ExchangeFormalism.ShriekTriangle _ _ _ _)).hom := by
  obtain ⟨Xl, ⟨⟨⟩⟩, Xh⟩ := X
  obtain ⟨fl, ⟨⟨⟨⟩⟩⟩, fw⟩ := f
  dsimp only at fl
  obtain rfl : Xh = fl ≫ Y.hom := by simpa using fw.symm
  obtain ⟨Yl, ⟨⟨⟩⟩, Yh⟩ := Y
  obtain ⟨gl, ⟨⟨⟨⟩⟩⟩, gw⟩ := g
  dsimp only at gl
  obtain rfl : Yh = gl ≫ Z.hom := by simpa using gw.symm
  rfl

/-- The composition isomorphism of the triangle `ofIsProperTriangle` is, through the
identifications `R(-)_!^{𝟙} ≅ R(-)_*` of the trivial compactifications, the composition
isomorphism `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`. -/
lemma compIso_triangleShriekTriangle_ofIsProperTriangle_inv_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] [IsProper (f ≫ g).left] :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (ofIsProperTriangle f g)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (ofIsProperTriangle f g)
    ((𝔽).compIso (triangleShriekTriangle (ofIsProperTriangle f g))).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ f).hom
          (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ g).hom =
      (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ (f ≫ g)).hom ≫
        (boundedConstructibleLowerStarComp ℓ f g).inv := by
  have w : SepFinType.homMk f ≫ 𝟙 (SepFinType.mk Y) = 𝟙 (SepFinType.mk X) ≫ SepFinType.homMk f :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  have := isIso_baseChange_triangleShriekTriangle ℓ (ofIsProperTriangle f g)
  have := isIso_exchange_triangleShriekTriangle ℓ (ofIsProperTriangle f g)
  have := (𝔽).isIso_baseChange_id_vert (SepFinType.homMk f) w
  have := (𝔽).isIso_exchange_id_vert (SepFinType.homMk f) w
  rw [Iso.inv_comp_eq, compIso_triangleShriekTriangle_ofIsProperTriangle ℓ f g,
    boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_hom_eq ℓ (g := f),
    boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_hom_eq ℓ (g := g),
    boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_hom_eq ℓ (g := f ≫ g),
    boundedConstructibleLowerStarComp_eq_pfComp' ℓ f g, Iso.symm_inv]
  exact (𝔽).hcomp_shId_eq_compIso_ofProper (SepFinType.homMk f) (SepFinType.homMk g) w

omit [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
/-- The comparison of the trivial compactification of a proper `f` with the chosen one, followed
by `Rf_! ≅ Rf_*`, is the identification `Rf_!^{𝟙} ≅ Rf_*`. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_ofIsProper_hom_comp
    (f : X ⟶ Y) [IsProper f.left] :
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (.ofIsProper f.left)
        (compactificationOverField f)).hom ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom =
      (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ f).hom := by
  rw [boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq, Iso.trans_hom, ← Category.assoc,
    ← Iso.trans_hom, boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl]
  exact Category.id_comp _

/-- **The identification `Rf_! ≅ Rf_*` is compatible with composition**, as an equation of
natural transformations. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_hom_comp_hcomp_isoLowerStar (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsProper f.left] [IsProper g.left] [IsProper (f ≫ g).left] :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).hom =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g)).hom ≫
        (boundedConstructibleLowerStarComp ℓ f g).inv := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (ofIsProperTriangle f g)
  have := isIso_exchange_triangleShriekTriangle ℓ (ofIsProperTriangle f g)
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ f g
    (ofIsProperTriangle f g)]
  simp only [Category.assoc]
  erw [← NatTrans.exchange
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (.ofIsProper f.left)
      (compactificationOverField f)).hom
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (.ofIsProper g.left)
      (compactificationOverField g)).hom
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).hom]
  rw [boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_ofIsProper_hom_comp,
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_ofIsProper_hom_comp,
    compIso_triangleShriekTriangle_ofIsProperTriangle_inv_comp,
    boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq ℓ (f ≫ g), Iso.trans_hom,
    Category.assoc]

/-- **The identification `Rf_! ≅ Rf_*` is compatible with composition** (blueprint
`prop-functor-package`, clause (3)): for proper `f` and `g`,
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_! ≅ Rf_* ⋙ Rg_*` is `R(f ≫ g)_! ≅ R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`. -/
theorem boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp' (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] [IsProper (f ≫ g).left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
        (boundedConstructibleLowerStar ℓ g).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K) =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g)).hom.app K ≫
        (boundedConstructibleLowerStarComp ℓ f g).inv.app K := by
  simpa only [NatTrans.comp_app, NatTrans.hcomp_app] using
    congr_app (boundedConstructibleLowerShriekComp_padicAlgCl_hom_comp_hcomp_isoLowerStar ℓ f g) K

end Proper

end AlgebraicGeometry.ProEtale.CondensedRing
