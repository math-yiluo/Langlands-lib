/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverIntegralIdentification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat

/-!
# Sections of `p^* Rⁱg_* ℚ̄_ℓ,T` as abelian groups, with their `ℚ̄_ℓ`-structure

Let `g : T ⟶ Y` be a morphism of schemes, `p : S ⟶ Y` weakly étale and
`F = Rⁱg_* ℚ̄_ℓ,T` the `i`-th cohomology sheaf of the derived pushforward of the constant `ℓ`-adic
sheaf (`AlgebraicGeometry.ProEtale.adicRightDerivedLowerStarUnit`). This file identifies the
abelian sheaf underlying `p^* F` with `p^* Rⁱg_*` of the abelian sheaf underlying `ℚ̄_ℓ,T`
(`AlgebraicGeometry.ProEtale.adicUpperStarRightDerivedLowerStarUnitAbIso`), and shows that this
identification carries the multiplication by a scalar `c ∈ ℚ̄_ℓ` to `p^* Rⁱg_*` of the
multiplication by `c` on `ℚ̄_ℓ,T`
(`AlgebraicGeometry.ProEtale.adicUpperStarRightDerivedLowerStarUnitAbIso_hom_smul`).

The scalar multiplications form a natural endomorphism of the identity functor of sheaves of
`ℚ̄_ℓ`-modules (`AlgebraicGeometry.ProEtale.weilSmulNatTrans`), which is intertwined by `g_*`, by
its right derived functors (`CategoryTheory.Functor.rightDerived_map_app_eq`) and by the
pullback along a weakly étale morphism, which is a restriction.
-/

@[expose] public section

universe u

open CategoryTheory Abelian

/-- A functor isomorphic to a functor intertwining two natural endomorphisms of the identity
functors intertwines them as well. -/
lemma CategoryTheory.Functor.map_app_eq_of_iso {C D : Type*} [Category* C] [Category* D]
    (β : 𝟭 C ⟶ 𝟭 C) (β' : 𝟭 D ⟶ 𝟭 D) {F G : C ⥤ D} (e : F ≅ G) (X : C)
    (h : G.map (β.app X) = β'.app (G.obj X)) : F.map (β.app X) = β'.app (F.obj X) := by
  rw [← cancel_mono (e.hom.app X)]
  have h1 := e.hom.naturality (β.app X)
  have h2 := β'.naturality (e.hom.app X)
  dsimp at h1 h2 ⊢
  rw [h1, h, h2]

namespace AlgebraicGeometry.ProEtale

section Scalar

variable {l : ℕ} [Fact l.Prime] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

variable (l) in
/-- Multiplication by a scalar `c ∈ ℚ̄_ℓ` on sheaves of `ℚ̄_ℓ`-modules on `X_proét`. -/
noncomputable abbrev weilSmulNatTrans (X : Scheme.{u}) (c : ULift.{u + 1} (PadicAlgCl l)) :
    𝟭 (Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) ⟶ 𝟭 _ :=
  Sheaf.smulNatTrans _ c

variable (c : ULift.{u + 1} (PadicAlgCl l))

lemma lowerStar_map_weilSmulNatTrans_app
    (M : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    (g)_*[WeilCoefficients.{u} l].map ((weilSmulNatTrans l Z c).app M) =
      (weilSmulNatTrans l Y c).app ((g)_*[WeilCoefficients.{u} l].obj M) :=
  rfl

/-- The right derived functors of `g_*` commute with the multiplication by a scalar. -/
lemma rightDerived_lowerStar_map_weilSmulNatTrans_app (i : ℕ)
    (M : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    ((g)_*[WeilCoefficients.{u} l].rightDerived i).map ((weilSmulNatTrans l Z c).app M) =
      (weilSmulNatTrans l Y c).app (((g)_*[WeilCoefficients.{u} l].rightDerived i).obj M) :=
  Functor.rightDerived_map_app_eq _ _ _ (lowerStar_map_weilSmulNatTrans_app g c) i M

/-- The pullback along a weakly étale morphism commutes with the multiplication by a scalar. -/
lemma upperStar_map_weilSmulNatTrans_app (h : WeaklyEtale g)
    (M : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (g)^*[WeilCoefficients.{u} l].map ((weilSmulNatTrans l Y c).app M) =
      (weilSmulNatTrans l Z c).app ((g)^*[WeilCoefficients.{u} l].obj M) :=
  Functor.map_app_eq_of_iso _ _ (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g h)
    M rfl

variable (l) in
/-- Taking underlying abelian sheaves commutes with the classical right derived functors of the
pushforward of sheaves of `ℚ̄_ℓ`-modules. -/
noncomputable def rightDerivedLowerStarWeilCoefficientsForgetAbIso (i : ℕ) :
    (g)_*[WeilCoefficients.{u} l].rightDerived i ⋙ weilCoefficientsForgetAb l Y ≅
      weilCoefficientsForgetAb l Z ⋙ (g)_*[Ab.{u + 1}].rightDerived i :=
  Functor.isoWhiskerRight ((g)_*[WeilCoefficients.{u} l]
      |>.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso i).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      ((weilCoefficientsForgetAb l Y).mapDerivedCategoryHomologyFunctorIso i)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (rightDerivedLowerStarCompWeilCoefficientsForgetAbIso g) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((weilCoefficientsForgetAb l Z).mapDerivedCategorySingleFunctor 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (weilCoefficientsForgetAb l Z)
      ((g)_*[Ab.{u + 1}].singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso i)

end Scalar

section UpperStar

variable {l : ℕ} [Fact l.Prime] {T Y S : Scheme.{u}} (g : T ⟶ Y) (p : S ⟶ Y) (i : ℕ)

variable (l) in
/-- The `i`-th cohomology sheaf `Rⁱg_* ℚ̄_ℓ,T` of the derived pushforward of the constant `ℓ`-adic
sheaf. -/
noncomputable abbrev adicRightDerivedLowerStarUnit : AdicSheaf l Y :=
  (DerivedCategory.homologyFunctor _ i).obj
    ((g)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj
      (AdicSheaf.unit l T)))

variable (l) in
/-- The sheaf of `ℚ̄_ℓ`-modules underlying `Rⁱg_* ℚ̄_ℓ,T` is the classical right derived functor of
the pushforward of sheaves of `ℚ̄_ℓ`-modules, applied to `ℚ̄_ℓ,T`. -/
noncomputable def adicRightDerivedLowerStarUnitForgetIso :
    (adicRightDerivedLowerStarUnit l g i).X ≅
      ((g)_*[WeilCoefficients.{u} l].rightDerived i).obj (adicConstantSheaf l T) :=
  ((AdicSheaf.forget Y).mapDerivedCategoryHomologyFunctorIso i).app _ ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      ((mapDerivedCategoryForgetCompRightDerivedLowerStarIso l g).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      (((g)_*[WeilCoefficients.{u} l]).rightDerivedFunctor.mapIso
        (((AdicSheaf.forget T).mapDerivedCategorySingleFunctor 0).app _)) ≪≫
    ((g)_*[WeilCoefficients.{u} l]).homologyRightDerivedFunctorObjSingleFunctorIso _ i

variable (l) [WeaklyEtale p]

/-- The abelian sheaf underlying `p^* Rⁱg_* ℚ̄_ℓ,T`, for `p` weakly étale, is `p^* Rⁱg_*` of the
abelian sheaf underlying `ℚ̄_ℓ,T`. -/
noncomputable def adicUpperStarRightDerivedLowerStarUnitAbIso :
    (weilCoefficientsForgetAb l S).obj ((p)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g i)).X ≅
      (p)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived i).obj
        ((weilCoefficientsForgetAb l T).obj (adicConstantSheaf l T))) :=
  (weilCoefficientsForgetAb l S).mapIso ((p)^*[WeilCoefficients.{u} l].mapIso
      (adicRightDerivedLowerStarUnitForgetIso l g i)) ≪≫
    (upperStarCompSheafComposeForget₂Iso p (ULift.{u + 1} (PadicAlgCl l))).app _ ≪≫
    (p)^*[Ab.{u + 1}].mapIso ((rightDerivedLowerStarWeilCoefficientsForgetAbIso l g i).app _)

/-- **The identification `adicUpperStarRightDerivedLowerStarUnitAbIso` is `ℚ̄_ℓ`-linear**: it
carries the multiplication by `c ∈ ℚ̄_ℓ` to `p^* Rⁱg_*` of the multiplication by `c` on
`ℚ̄_ℓ,T`. -/
lemma adicUpperStarRightDerivedLowerStarUnitAbIso_hom_smul (c : ULift.{u + 1} (PadicAlgCl l)) :
    (weilCoefficientsForgetAb l S).map ((weilSmulNatTrans l S c).app _) ≫
        (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom =
      (adicUpperStarRightDerivedLowerStarUnitAbIso l g p i).hom ≫
        (p)^*[Ab.{u + 1}].map (((g)_*[Ab.{u + 1}].rightDerived i).map
          ((weilCoefficientsForgetAb l T).map
            ((weilSmulNatTrans l T c).app (adicConstantSheaf l T)))) := by
  have h1 := (weilSmulNatTrans l S c).naturality
    ((p)^*[WeilCoefficients.{u} l].map (adicRightDerivedLowerStarUnitForgetIso l g i).hom)
  have h2 := upperStar_map_weilSmulNatTrans_app p c inferInstance
    (((g)_*[WeilCoefficients.{u} l].rightDerived i).obj (adicConstantSheaf l T))
  have h3 := (upperStarCompSheafComposeForget₂Iso p (ULift.{u + 1} (PadicAlgCl l))).hom.naturality
    ((weilSmulNatTrans l Y c).app
      (((g)_*[WeilCoefficients.{u} l].rightDerived i).obj (adicConstantSheaf l T)))
  have h4 := rightDerived_lowerStar_map_weilSmulNatTrans_app g c i (adicConstantSheaf l T)
  have h5 := (rightDerivedLowerStarWeilCoefficientsForgetAbIso l g i).hom.naturality
    ((weilSmulNatTrans l T c).app (adicConstantSheaf l T))
  dsimp at h1 h3 h5
  simp only [adicUpperStarRightDerivedLowerStarUnitAbIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  erw [← h1]
  rw [Functor.map_comp_assoc, ← h2, reassoc_of% h3, ← Functor.map_comp, ← Functor.map_comp,
    ← h4]
  erw [h5]

end UpperStar

end AlgebraicGeometry.ProEtale
