/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalHom
public import WeilConjectures.PoincareDuality.Biduality.Constructible
public import WeilConjectures.TraceFormula.Product

/-!

# External products and the Künneth–Verdier map

Let `X, Y` be separated `k`-schemes of finite type, with projections `p_X : X ⨯ Y ⟶ X` and
`p_Y : X ⨯ Y ⟶ Y` of their product over the base point. The *external product* of
`M ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and `N ∈ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` is `M ⊠ N = Lp_X^* M ⊗ Lp_Y^* N`
(`ProEtale.CondensedRing.externalProduct`, blueprint `prose-11-08`).

The *Künneth–Verdier map* (blueprint `lemma-external-duality-trace-morphism`, (iv))
```
κ_{M,N} : M ⊠ D_Y N ⟶ RHom(Lp_Y^* N, Rp_X^! M)
```
(`ProEtale.CondensedRing.kunnethVerdierMap`) is the transpose of
```
Lp_Y^* N ⊗ (Lp_X^* M ⊗ Lp_Y^* D_Y N) ≅ Lp_X^* M ⊗ (Lp_Y^* N ⊗ Lp_Y^* D_Y N)
  ⟶ Lp_X^* M ⊗ Lp_Y^* (N ⊗ D_Y N) --ev--> Lp_X^* M ⊗ Lp_Y^* ω_Y --α--> Rp_X^! M,
```
where `α = α_{𝟙, a_Y}` is the *exceptional Künneth map* (blueprint
`lemma-external-duality-trace-morphism`, (ii); `ProEtale.CondensedRing.exceptionalKunnethMap`): the
exceptional adjoint of
```
Rp_X! (Lp_X^* M ⊗ Lp_Y^* ω_Y) ≅ Rp_X! (Lp_Y^* ω_Y ⊗ Lp_X^* M) ≅ Rp_X! (Lp_Y^* ω_Y) ⊗ M
  ≅ La_X^* Ra_Y! ω_Y ⊗ M --ε--> La_X^* ℚ̄_ℓ ⊗ M ≅ M,
```
built from the derived projection formula for `p_X`, compact-support base change in the
cartesian square of the product, and the counit of `Ra_Y! ⊣ Ra_Y^!`; this is the composite
`Ku_!` of `lemma-external-duality-trace-morphism` (i) for the pair `(𝟙_X, a_Y)` followed by the
counits. Its invertibility, the Künneth–Verdier theorem (blueprint
`lemma-external-duality-trace-morphism--1`), is `ProEtale.CondensedRing.isIso_kunnethVerdierMap`, in
`WeilConjectures.TraceFormula.KunnethVerdierTheorem`. The map `κ_{M,N}`
factors as `RHom(1, α) ∘ β` through the external Hom map `β` of blueprint
`lemma-external-duality-trace-morphism` (iii) (`ProEtale.CondensedRing.kunnethVerdierMap_eq`).

All constructions are classical: ordinary categories and natural transformations built by
composition, whiskering and mates from the data of the six functors (blueprint
`rem-trf-classical-framework`).

## Main definitions

- `ProEtale.CondensedRing.externalProduct`: the external product `M ⊠ N`.
- `ProEtale.CondensedRing.exceptionalKunnethMap`: `α_{𝟙, a_Y} : M ⊠ ω_Y ⟶ Rp_X^! M`.
- `ProEtale.CondensedRing.kunnethVerdierMap`: `κ_{M,N}`.

## Main statements

- `ProEtale.CondensedRing.kunnethVerdierMap_eq`: `κ_{M,N} = RHom(1, α) ∘ β`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *external product* `M ⊠ N = Lp_X^* M ⊗ Lp_Y^* N` on `X ⨯ Y` (blueprint
`prose-11-08`), with the projections `p_X = prod.fst` and `p_Y = prod.snd`; the
order of the factors is part of the notation. -/
noncomputable def externalProduct (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Dᵇc((X ⨯ Y).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M ⊗
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N

variable (X Y) in
/-- Compact-support base change for the product square, inverted:
`Rp_X! ⋙ ... : Lp_Y^* ⋙ Rp_X! ≅ Ra_Y! ⋙ La_X^*`. -/
noncomputable def prodBaseChangeIso :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y) ⋙
        boundedConstructibleLowerShriek ℓ
          (prod.fst : X ⨯ Y ⟶ X) ≅
      boundedConstructibleLowerShriek ℓ (toPoint Y) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (isPullback_prod_toPoint X Y)
  (asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (isPullback_prod_toPoint X Y))).symm

/-- The morphism `Rp_X! (Lp_X^* M ⊗ Lp_Y^* ω_Y) ⟶ M` whose exceptional adjoint is the exceptional
Künneth map: the tensor symmetry, the inverse of the projection formula for `p_X`, the inverse
of compact-support base change in the product square, the counit of `Ra_Y! ⊣ Ra_Y^!` and the
unit isomorphism of the monoidal functor `La_X^*`. -/
noncomputable def exceptionalKunnethAdjoint (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj
        (externalProduct ℓ M (dualizingComplex' ℓ Y)) ⟶ M :=
  (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map (β_ _ _).hom ≫
    inv (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Y ⟶ X)).app
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
        (dualizingComplex' ℓ Y))).app M) ≫
    ((prodBaseChangeIso ℓ X Y).hom.app (dualizingComplex' ℓ Y) ▷ M) ≫
    ((boundedConstructibleUpperStar _ ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _)) ▷ M) ≫
    ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv ▷ M) ≫
    (λ_ M).hom

/-- The *exceptional Künneth map* `α_{𝟙, a_Y} : M ⊠ ω_Y ⟶ Rp_X^! M` (blueprint
`lemma-external-duality-trace-morphism`, (ii), for `f₁ = 𝟙_X`, `f₂ = a_Y`, `L₁ = M`, `L₂ = ℚ̄_ℓ`):
the exceptional adjoint of `exceptionalKunnethAdjoint`. -/
noncomputable def exceptionalKunnethMap (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ M (dualizingComplex' ℓ Y) ⟶
      (boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M :=
  (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : X ⨯ Y ⟶ X)).homEquiv _ _
    (exceptionalKunnethAdjoint ℓ M)

/-- The pairing `Lp_Y^* N ⊗ (M ⊠ D_Y N) ⟶ Rp_X^! M` whose transpose is the Künneth–Verdier map:
the symmetry moving `Lp_Y^* N` next to `Lp_Y^* D_Y N`, the monoidal structure of `Lp_Y^*`, the
evaluation `N ⊗ D_Y N ⟶ ω_Y` and the exceptional Künneth map. -/
noncomputable def kunnethVerdierPairing (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N ⊗
        externalProduct ℓ M (verdierDual ℓ N) ⟶
      (boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M :=
  (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
    (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)) _ _) ≫
    (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map
      ((ihom.ev N).app (dualizingComplex' ℓ Y))) ≫
    exceptionalKunnethMap ℓ M

/-- The *Künneth–Verdier map* `κ_{M,N} : M ⊠ D_Y N ⟶ RHom(Lp_Y^* N, Rp_X^! M)` (blueprint
`lemma-external-duality-trace-morphism`, (iv)): the transpose of `kunnethVerdierPairing`, that is
the external Hom map `β` of the two evaluations followed by the exceptional Künneth map
`α_{𝟙, a_Y}`. -/
noncomputable def kunnethVerdierMap (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ M (verdierDual ℓ N) ⟶
      (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N)).obj
        ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M) :=
  curry (kunnethVerdierPairing ℓ M N)

/-- **The Künneth–Verdier map is `RHom(1, α) ∘ β`** (blueprint
`lemma-external-duality-trace-morphism` (iv)): through the unit identifications `M ≅ RHom(ℚ̄_ℓ, M)`
and `ℚ̄_ℓ ⊠ N ≅ Lp_Y^* N`, `κ_{M,N}` is the external Hom map `β` of blueprint
`lemma-external-duality-trace-morphism` (iii) for the pairs `(ℚ̄_ℓ, M)` and `(N, ω_Y)` followed by
the exceptional Künneth map `α`. -/
lemma kunnethVerdierMap_eq (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    kunnethVerdierMap ℓ M N =
      ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map
          (MonoidalClosed.unitNatIso.hom.app M) ▷ _ ≫
        externalHomMap (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X))
          (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)) (𝟙_ _) M N
          (dualizingComplex' ℓ Y) ≫
        (pre (unitExternalMap (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X))
          (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)) N)).app _) ≫
      (ihom _).map (exceptionalKunnethMap ℓ M) :=
  curry_eq_externalHomMap_comp _ _ M N _ (exceptionalKunnethMap ℓ M)

/-- The computation behind `exceptionalKunnethAdjoint_naturality`, for abstract functors and
morphisms. -/
private lemma exceptionalKunnethAdjoint_naturality_aux {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    [MonoidalCategory 𝒞] [MonoidalCategory 𝒟] [BraidedCategory 𝒟] (F : 𝒟 ⥤ 𝒞) (P : 𝒞 ⥤ 𝒟)
    (W : 𝒟) {M M' : 𝒞} (φ : M ⟶ M') (pf : ∀ M : 𝒞, F.obj (W ⊗ P.obj M) ⟶ F.obj W ⊗ M)
    (hpf : F.map (W ◁ P.map φ) ≫ pf M' = pf M ≫ (F.obj W ◁ φ)) {T₁ T₂ : 𝒞}
    (b : F.obj W ⟶ T₁) (c : T₁ ⟶ T₂) (e : T₂ ⟶ 𝟙_ 𝒞) :
    F.map (P.map φ ▷ W) ≫ (F.map (β_ (P.obj M') W).hom ≫ pf M' ≫ (b ▷ M') ≫ (c ▷ M') ≫
        (e ▷ M') ≫ (λ_ M').hom) =
      (F.map (β_ (P.obj M) W).hom ≫ pf M ≫ (b ▷ M) ≫ (c ▷ M) ≫ (e ▷ M) ≫ (λ_ M).hom) ≫ φ := by
  rw [← F.map_comp_assoc, BraidedCategory.braiding_naturality_left, F.map_comp_assoc,
    reassoc_of% hpf, whisker_exchange_assoc, whisker_exchange_assoc, whisker_exchange_assoc,
    leftUnitor_naturality]
  simp only [Category.assoc]

/-- The adjoint of the exceptional Künneth map is natural in `M`: for `φ : M ⟶ M'`,
```
Rp_X! (M ⊠ ω_Y) ──Rp_X! (φ ⊠ 1)──▶ Rp_X! (M' ⊠ ω_Y)
       │                                   │
       ▼                                   ▼
       M ─────────────── φ ──────────────▶ M'
```
commutes. -/
@[reassoc]
lemma exceptionalKunnethAdjoint_naturality {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : M ⟶ M') :
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map φ ▷ _) ≫
      exceptionalKunnethAdjoint ℓ M' = exceptionalKunnethAdjoint ℓ M ≫ φ := by
  have hPF := boundedConstructibleExceptionalProjectionMorphism_natural_right ℓ
    (prod.fst : X ⨯ Y ⟶ X)
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj (dualizingComplex' ℓ Y)) φ
  have hinv : (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map
      (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map φ) ≫
        inv (boundedConstructibleExceptionalProjectionMorphism ℓ (prod.fst : X ⨯ Y ⟶ X)
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (dualizingComplex' ℓ Y)) M') =
      inv (boundedConstructibleExceptionalProjectionMorphism ℓ (prod.fst : X ⨯ Y ⟶ X)
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (dualizingComplex' ℓ Y)) M) ≫ (_ ◁ φ) := by
    rw [IsIso.comp_inv_eq, Category.assoc, hPF, IsIso.inv_hom_id_assoc]
  have hinv' : (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map
      (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map φ) ≫
        inv (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Y ⟶ X)).app
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (dualizingComplex' ℓ Y))).app M') =
      inv (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Y ⟶ X)).app
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (dualizingComplex' ℓ Y))).app M) ≫ (_ ◁ φ) := hinv
  unfold exceptionalKunnethAdjoint
  exact exceptionalKunnethAdjoint_naturality_aux
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X))
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X))
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj (dualizingComplex' ℓ Y)) φ
    (fun M ↦ inv (((boundedConstructibleExceptionalProjection ℓ (prod.fst : X ⨯ Y ⟶ X)).app
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
        (dualizingComplex' ℓ Y))).app M)) hinv'
    ((prodBaseChangeIso ℓ X Y).hom.app (dualizingComplex' ℓ Y))
    ((boundedConstructibleUpperStar _ ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _)))
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv

/-- Transposes along an adjunction of morphisms related by naturality squares are related by
naturality squares. -/
private lemma homEquiv_naturality_aux {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {F : 𝒟 ⥤ 𝒞}
    {G : 𝒞 ⥤ 𝒟} (adj : F ⊣ G) {A A' : 𝒟} {B B' : 𝒞} (f : A ⟶ A') (g : B ⟶ B')
    {a : F.obj A ⟶ B} {a' : F.obj A' ⟶ B'} (h : F.map f ≫ a' = a ≫ g) :
    f ≫ adj.homEquiv _ _ a' = adj.homEquiv _ _ a ≫ G.map g := by
  rw [← Adjunction.homEquiv_naturality_left, h, Adjunction.homEquiv_naturality_right]

/-- Curried morphisms of pairings related by naturality squares are related by naturality
squares. -/
private lemma curry_naturality_aux {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞]
    [MonoidalClosed 𝒞] (A : 𝒞) {B B' T T' : 𝒞} (f : B ⟶ B') (g : T ⟶ T')
    {p : A ⊗ B ⟶ T} {p' : A ⊗ B' ⟶ T'} (h : A ◁ f ≫ p' = p ≫ g) :
    f ≫ curry p' = curry p ≫ (ihom A).map g := by
  rw [← curry_natural_left, h, curry_natural_right]

/-- The naturality of the Künneth–Verdier pairing in its first argument, for abstract objects. -/
private lemma kunnethVerdierPairing_aux {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞]
    [BraidedCategory 𝒞] (A B : 𝒞) {C₁ C₀ PM PM' T T' : 𝒞} (x : PM ⟶ PM') (m₁ : A ⊗ B ⟶ C₁)
    (m₂ : C₁ ⟶ C₀) {a : PM ⊗ C₀ ⟶ T} {a' : PM' ⊗ C₀ ⟶ T'} (g : T ⟶ T')
    (h : x ▷ C₀ ≫ a' = a ≫ g) :
    A ◁ (x ▷ B) ≫ ((α_ A PM' B).inv ≫ (β_ A PM').hom ▷ B ≫ (α_ PM' A B).hom ≫ PM' ◁ m₁ ≫
        PM' ◁ m₂ ≫ a') =
      ((α_ A PM B).inv ≫ (β_ A PM).hom ▷ B ≫ (α_ PM A B).hom ≫ PM ◁ m₁ ≫ PM ◁ m₂ ≫ a) ≫ g := by
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc, ← whisker_exchange_assoc, h]
  simp only [Category.assoc]

/-- The exceptional Künneth map `α_{𝟙, a_Y} : M ⊠ ω_Y ⟶ Rp_X^! M` is natural in `M`. -/
@[reassoc]
lemma exceptionalKunnethMap_naturality {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : M ⟶ M') :
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map φ ▷ _ ≫
        exceptionalKunnethMap ℓ M' =
      exceptionalKunnethMap ℓ M ≫
        (boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map φ := by
  exact homEquiv_naturality_aux _ _ _ (exceptionalKunnethAdjoint_naturality ℓ φ)

/-- The Künneth–Verdier pairing is natural in `M`. -/
@[reassoc]
lemma kunnethVerdierPairing_naturality {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : M ⟶ M') (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    _ ◁ ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map φ ▷ _) ≫
        kunnethVerdierPairing ℓ M' N =
      kunnethVerdierPairing ℓ M N ≫
        (boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map φ :=
  kunnethVerdierPairing_aux _ _ _ _ _ _ (exceptionalKunnethMap_naturality ℓ φ)

/-- The Künneth–Verdier map `κ_{M,N}` is natural in `M`. -/
@[reassoc]
lemma kunnethVerdierMap_naturality_left {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : M ⟶ M') (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map φ ▷ _ ≫
        kunnethVerdierMap ℓ M' N =
      kunnethVerdierMap ℓ M N ≫
        (ihom _).map ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map φ) := by
  exact curry_naturality_aux _ _ _ (kunnethVerdierPairing_naturality ℓ φ N)

/-- The objects `M` for which the Künneth–Verdier map `κ_{M,N}` is an isomorphism are closed under
isomorphisms (the first closure property of the dévissage in `M` of
`lemma-external-duality-trace-morphism--1`). -/
lemma isIso_kunnethVerdierMap_of_iso {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (e : M ≅ M') (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso (kunnethVerdierMap ℓ M' N)] : IsIso (kunnethVerdierMap ℓ M N) := by
  have h := kunnethVerdierMap_naturality_left ℓ e.hom N
  rw [(IsIso.eq_comp_inv _).mpr h.symm]
  infer_instance

/-- The double-dual morphism is natural, for any braiding. -/
private lemma bidualityMap_naturality {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞]
    [MonoidalClosed 𝒞] {_ : BraidedCategory 𝒞} (ω : 𝒞) {M M' : 𝒞} (f : M ⟶ M') :
    f ≫ Verdier.bidualityMap ω M' = Verdier.bidualityMap ω M ≫ (pre ((pre f).app ω)).app ω :=
  toIhomIhom_naturality ω f

/-- **Verdier biduality for the dualizing complex** (blueprint `theorem-verdier-biduality--1`): for
bounded constructible `M` on `Y`, the double-dual morphism `M ⟶ D_Y D_Y M`, the transpose of the
evaluation `D_Y M ⊗ M ⟶ M ⊗ D_Y M ⟶ ω_Y`, is an isomorphism. It is the constructible biduality
theorem (`isIso_verdierBiduality`, blueprint `theorem-verdier-biduality`). -/
noncomputable def verdierBidualityIso (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ≅ verdierDual ℓ (verdierDual ℓ M) :=
  haveI := isIso_verdierBiduality ℓ M
  asIso (verdierBiduality ℓ M)

lemma verdierBidualityIso_hom (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (verdierBidualityIso ℓ M).hom = verdierBiduality ℓ M :=
  rfl

/-- The biduality isomorphism is natural (blueprint `theorem-verdier-biduality--1`). -/
@[reassoc]
lemma verdierBidualityIso_hom_naturality {M M' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : M ⟶ M') :
    f ≫ (verdierBidualityIso ℓ M').hom =
      (verdierBidualityIso ℓ M).hom ≫
        (pre ((pre f).app (dualizingComplex' ℓ Y))).app (dualizingComplex' ℓ Y) :=
  bidualityMap_naturality _ f

end AlgebraicGeometry.ProEtale.CondensedRing
