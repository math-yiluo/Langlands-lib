/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportDerived

/-!
# The base-change morphism and residue field module sheaves

Write `G_X = residueFieldModuleSheaf X ℓ E`. For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

we show that, if the isomorphisms `ProEtale.residueFieldDerivedUpperStarIso` are compatible with
the composition of derived pullbacks along `f' ≫ g` and `g' ≫ f`
(`ProEtale.ResidueFieldDerivedUpperStarIsoCompCoherenceAt`), then `D(G_{Y'})` of the base-change
morphism `BC_sq` of module objects over `𝔽_E` at `M` and the derived base change map
`ProEtale.derivedBaseChangeMap` of pro-étale sheaves of `𝔽_E`-modules at `D(G_X) M` are
isomorphic arrows (`ProEtale.nonempty_arrowIso_map_exchangeRight_residueField`). The proof is the
cube law of mates (`CategoryTheory.Adjunction.nonempty_arrowIso_map_exchangeRight_app`), the
comparison of the derived pushforwards being invertible by
`ProEtale.isIso_residueFieldDerivedPushHom`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The isomorphisms `residueFieldDerivedUpperStarIso : Lh^* ⋙ D(G) ≅ D(G) ⋙ Lh^*` are
compatible with the composition isomorphisms `L(p ≫ q)^* ≅ Lq^* ⋙ Lp^*` along `p` and `q`. -/
def ResidueFieldDerivedUpperStarIsoCompCoherenceAt {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) : Prop :=
  ∀ M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (residueFieldRingObj Z ℓ E)),
    (residueFieldDerivedUpperStarIso ℓ E (p ≫ q)).hom.app M ≫
        (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E))
          p q).hom.app ((residueFieldModuleSheaf Z ℓ E).mapDerivedCategory.obj M) =
      (residueFieldModuleSheaf X ℓ E).mapDerivedCategory.map
          ((CondensedRing.leftDerivedUpperStarComp
            (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) p q).hom.app M) ≫
        (residueFieldDerivedUpperStarIso ℓ E p).hom.app
          (L((q)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧).obj M) ≫
        L((p)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]).map
          ((residueFieldDerivedUpperStarIso ℓ E q).hom.app M)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The isomorphisms `residueFieldDerivedUpperStarIso` commute with the transports along an
equality `u = v` of morphisms of schemes. -/
lemma residueFieldDerivedUpperStarIso_hom_app_leftDerivedUpperStarCongr {X Y : Scheme.{u}}
    {u v : X ⟶ Y} (e : u = v)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (residueFieldRingObj Y ℓ E))) :
    (residueFieldDerivedUpperStarIso ℓ E u).hom.app M ≫
        (leftDerivedUpperStarCongr (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) e).hom.app
          ((residueFieldModuleSheaf Y ℓ E).mapDerivedCategory.obj M) =
      (residueFieldModuleSheaf X ℓ E).mapDerivedCategory.map
          (eqToHom (by rw [e] :
            L((u)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧).obj M =
              L((v)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧).obj M)) ≫
        (residueFieldDerivedUpperStarIso ℓ E v).hom.app M := by
  subst e
  simp

private lemma inv_inv_comp_eq_comp_inv_inv {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (i₁ : O₂ ≅ O₁) (i₂ : O₃ ≅ O₂) (x : O₃ ⟶ O₄) (y : O₁ ⟶ O₅) (j₁ : O₆ ≅ O₅) (j₂ : O₄ ≅ O₆)
    (h : x ≫ j₂.hom ≫ j₁.hom = i₂.hom ≫ i₁.hom ≫ y) :
    i₁.inv ≫ i₂.inv ≫ x = y ≫ j₁.inv ≫ j₂.inv := by
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq, ← reassoc_of% h]
  simp

private lemma cube_aux {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ Q₁ Q₂ Q₃ Q₄ : C}
    (t₁ : O₁ ⟶ O₂) (t₂ : O₂ ⟶ O₃) (t₃ : O₃ ⟶ O₄) (u₁ : O₄ ⟶ O₅) (u₂ : O₅ ⟶ O₆) (v₁ : O₁ ⟶ Q₁)
    (v₂ : Q₁ ⟶ Q₂) (w₁ : Q₂ ⟶ Q₃) (w₂ : Q₃ ⟶ Q₄) (w₃ : Q₄ ⟶ O₆) (P₁ : O₂ ⟶ Q₃) (P₂ : O₃ ⟶ Q₄)
    (s : O₂ ⟶ O₁) (s' : Q₃ ⟶ Q₂) (hs : t₁ ≫ s = 𝟙 O₁) (hs' : s' ≫ w₁ = 𝟙 Q₃)
    (H₁ : P₁ ≫ s' = s ≫ v₁ ≫ v₂) (H₂ : P₂ ≫ w₃ = t₃ ≫ u₁ ≫ u₂) (H₃ : P₁ ≫ w₂ = t₂ ≫ P₂) :
    t₁ ≫ t₂ ≫ t₃ ≫ u₁ ≫ u₂ = v₁ ≫ v₂ ≫ w₁ ≫ w₂ ≫ w₃ := by
  have h : t₁ ≫ P₁ = v₁ ≫ v₂ ≫ w₁ := by
    rw [← Category.comp_id P₁, ← hs', reassoc_of% H₁, reassoc_of% hs]
  rw [← H₂, reassoc_of% H₃.symm, reassoc_of% h]

variable {ℓ E} {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The cube condition of `CategoryTheory.Adjunction.nonempty_arrowIso_map_exchangeRight_app` for
the derived pullbacks of module objects over `𝔽_E` and of sheaves of `𝔽_E`-modules along a
commutative square, assuming the compatibility of `residueFieldDerivedUpperStarIso` with the
composition of derived pullbacks along `f' ≫ g` and `g' ≫ f`. -/
lemma residueFieldDerivedUpperStarIso_cube (sq : CommSq g' f' f g)
    (H₁ : ResidueFieldDerivedUpperStarIsoCompCoherenceAt ℓ E f' g)
    (H₂ : ResidueFieldDerivedUpperStarIsoCompCoherenceAt ℓ E g' f)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (residueFieldRingObj Y ℓ E))) :
    L((f')^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]).map
        ((residueFieldDerivedUpperStarIso ℓ E g).inv.app M) ≫
        (residueFieldDerivedUpperStarIso ℓ E f').inv.app
          (L((g)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧).obj M) ≫
        (residueFieldModuleSheaf X' ℓ E).mapDerivedCategory.map
          ((pullbackSquareComparison
            (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) sq).hom.app M) =
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) sq).hom.app
          ((residueFieldModuleSheaf Y ℓ E).mapDerivedCategory.obj M) ≫
        L((g')^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]).map
          ((residueFieldDerivedUpperStarIso ℓ E f).inv.app M) ≫
        (residueFieldDerivedUpperStarIso ℓ E g').inv.app
          (L((f)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧).obj M) := by
  -- The unifications with `inv_inv_comp_eq_comp_inv_inv` and `cube_aux` only need to unfold
  -- reducible constants. At default transparency the elaborator unfolds the composition of the
  -- derived categories (a localization) when comparing the (pretty-printing identical) sides,
  -- which takes minutes.
  simp only [← Iso.app_inv, ← Functor.mapIso_inv]
  with_reducible refine inv_inv_comp_eq_comp_inv_inv _ _ _ _ _ _ ?_
  have H₁ := H₁ M
  have H₂ := H₂ M
  have H₃ := residueFieldDerivedUpperStarIso_hom_app_leftDerivedUpperStarCongr ℓ E sq.w.symm M
  simp only [Iso.app_hom, Functor.mapIso_hom, pullbackSquareComparison_hom_app, Functor.map_comp,
    Category.assoc, leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  with_reducible
    exact cube_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp [← Functor.map_comp]) (by simp) H₁ H₂ H₃

end AlgebraicGeometry.ProEtale
