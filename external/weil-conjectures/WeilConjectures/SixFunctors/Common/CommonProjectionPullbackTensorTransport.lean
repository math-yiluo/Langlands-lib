/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
/-! # Transporting a tensor comparison square through functor equalities -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory
namespace WeilConjectures

private theorem natIso_component_heq
    {A B : Type*} [Category* A] [Category* B]
    {F G F' G' : A ⥤ B} (eF : F = F') (eG : G = G')
    (a : F ≅ G) (b : F' ≅ G') (h : HEq a b) (K : A) :
    HEq (a.hom.app K) (b.hom.app K) := by
  subst F' G'
  cases eq_of_heq h
  rfl

/-- A tensor/pullback component square is preserved under the recorded functor equalities.
Source: thm-sf-pf-field.proof.md, Compatibility, normalization of the supplied operations.
(blueprint: lem-sf-common-projection-tensor-component-normalization).
Proof: substitute the six functor equalities. Equality of the pullback comparison
components identifies the natural isomorphisms. The uncurrying identities identify
the two tensorator components. Substitute the two comparison components and combine
the two tensor-factor maps by functoriality. -/
theorem commonProjectionTensorComponent_of_normalization
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (I : A ⥤ A') (J : B ⥤ B')
    {F F₀ : A ⥤ B} {G G₀ : A' ⥤ B'}
    {TA : A ⥤ A ⥤ A} {TB : B ⥤ B ⥤ B}
    {TA' : A' ⥤ A' ⥤ A'} {TB' : B' ⥤ B' ⥤ B'}
    (RA : A × A ⥤ A) (RB : B × B ⥤ B)
    (RA' : A' × A' ⥤ A') (RB' : B' × B' ⥤ B')
    (eF : F = F₀) (eG : G = G₀)
    (eTA : TA = Functor.currying.inverse.obj RA)
    (eTB : TB = Functor.currying.inverse.obj RB)
    (eTA' : TA' = Functor.currying.inverse.obj RA')
    (eTB' : TB' = Functor.currying.inverse.obj RB')
    (φ : (Functor.postcompose₂.obj F).obj TA ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj TB)
    (ψ : (Functor.postcompose₂.obj G).obj TA' ⟶
      (((Functor.whiskeringLeft₂ _).obj G).obj G).obj TB')
    (μ : ∀ K L, F₀.obj (RA.obj (K, L)) ⟶ RB.obj (F₀.obj K, F₀.obj L))
    (ν : ∀ K L, G₀.obj (RA'.obj (K, L)) ⟶ RB'.obj (G₀.obj K, G₀.obj L))
    (a : F ⋙ J ≅ I ⋙ G) (a₀ : F₀ ⋙ J ≅ I ⋙ G₀)
    (tA : Functor.uncurry.obj TA ⋙ I ≅ I.prod I ⋙ Functor.uncurry.obj TA')
    (tB : Functor.uncurry.obj TB ⋙ J ≅ J.prod J ⋙ Functor.uncurry.obj TB')
    (tA₀ : RA ⋙ I ≅ I.prod I ⋙ RA') (tB₀ : RB ⋙ J ≅ J.prod J ⋙ RB')
    (mA : (Functor.postcompose₂.obj I).obj TA ≅
      (((Functor.whiskeringLeft₂ _).obj I).obj I).obj TA')
    (mB : (Functor.postcompose₂.obj J).obj TB ≅
      (((Functor.whiskeringLeft₂ _).obj J).obj J).obj TB')
    (hmA : ∀ K L, (mA.hom.app K).app L = tA.hom.app (K, L))
    (hmB : ∀ K L, (mB.hom.app K).app L = tB.hom.app (K, L))
    (ha : ∀ K, HEq (a.hom.app K) (a₀.hom.app K))
    (htA : HEq tA tA₀) (htB : HEq tB tB₀)
    (hφ : ∀ K L, HEq ((φ.app K).app L) (μ K L))
    (hψ : ∀ K L, HEq ((ψ.app K).app L) (ν K L))
    (M N : A)
    (h : J.map (μ M N) ≫ tB₀.hom.app (F₀.obj M, F₀.obj N) =
      a₀.hom.app (RA.obj (M, N)) ≫ G₀.map (tA₀.hom.app (M, N)) ≫
        ν (I.obj M) (I.obj N) ≫
        RB'.map (Prod.mkHom (a₀.inv.app M) (a₀.inv.app N))) :
    J.map ((φ.app M).app N) ≫
        (mB.hom.app (F.obj M)).app
          (F.obj N) =
      a.hom.app ((TA.obj M).obj N) ≫
        G.map ((mA.hom.app M).app N) ≫
        ((ψ.app (I.obj M)).app (I.obj N)) ≫
        (TB'.map (a.inv.app M)).app (G.obj (I.obj N)) ≫
        (TB'.obj (J.obj (F.obj M))).map (a.inv.app N) := by
  subst F G TA TB TA' TB'
  have ea : a = a₀ := by
    apply Iso.ext
    ext K
    exact eq_of_heq (ha K)
  cases ea
  have htA_app (K L : A) : tA.hom.app (K, L) = tA₀.hom.app (K, L) := by
    exact eq_of_heq (natIso_component_heq
      (congrArg (fun R ↦ R ⋙ I) (Functor.uncurry_obj_curry_obj RA))
      (congrArg (fun R ↦ I.prod I ⋙ R) (Functor.uncurry_obj_curry_obj RA'))
      tA tA₀ htA (K, L))
  have htB_app (K L : B) : tB.hom.app (K, L) = tB₀.hom.app (K, L) := by
    exact eq_of_heq (natIso_component_heq
      (congrArg (fun R ↦ R ⋙ J) (Functor.uncurry_obj_curry_obj RB))
      (congrArg (fun R ↦ J.prod J ⋙ R) (Functor.uncurry_obj_curry_obj RB'))
      tB tB₀ htB (K, L))
  rw [hmA, hmB, eq_of_heq (hφ M N), eq_of_heq (hψ (I.obj M) (I.obj N)), htA_app, htB_app]
  simpa only [Functor.currying, Functor.curry_obj_obj_obj, Functor.comp_obj,
    Functor.curry_obj_map_app, Functor.curry_obj_obj_map,
    ← Functor.map_comp, CategoryTheory.prod_comp, Category.comp_id, Category.id_comp,
    Category.assoc] using h

end WeilConjectures
