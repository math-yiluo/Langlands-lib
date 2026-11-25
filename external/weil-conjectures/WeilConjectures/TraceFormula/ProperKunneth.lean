/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperProjectionFormula
public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.TraceFormula.RelativeFrobeniusComparison

/-!

# The Künneth formula for proper direct images

Let `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂` be morphisms of separated `k`-schemes of finite type, with
product `q = f₁ × f₂ : X₁ ⨯ X₂ ⟶ Y₁ ⨯ Y₂`. The *Künneth map*
```
Π : Rf₁* B₁ ⊠ Rf₂* B₂ ⟶ Rq_* (B₁ ⊠ B₂)
```
(`ProEtale.CondensedRing.prodLowerStarExternalProduct`, blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 5) is the adjoint for `Lq^* ⊣ Rq_*` of the
monoidal structure of `Lq^*` followed by the counits of `Lfᵢ^* ⊣ Rfᵢ*`, transported along the
projections (`ProEtale.CondensedRing.prodUpperStarCounit`). This file proves that `Π` is an
isomorphism for proper `f₁`, `f₂` (`ProEtale.CondensedRing.isIso_prodLowerStarExternalProduct`,
blueprint `lemma-kunneth-formula-compact-supports--1`, in the form `Rf_! ≅ Rf_*` for proper
morphisms used in `lemma-external-duality-trace-morphism` (i)).

## Proof

Write `q = r ≫ s` with `r = f₁ × 1 : X₁ ⨯ X₂ ⟶ Y₁ ⨯ X₂` and `s = 1 × f₂ : Y₁ ⨯ X₂ ⟶ Y₁ ⨯ Y₂`,
base changes of `f₁` and `f₂`. By `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom`, `Π` is
an isomorphism as soon as

* the base change morphisms of the cartesian squares of `r` and `s` are isomorphisms: this is
  proper base change (`isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`), the
  transposes of the transported counits being the base change morphisms
  (`ProEtale.CondensedRing.homEquiv_prodUpperStarCounit`);
* the projection morphism of `r` and the left projection morphism of `s` are isomorphisms: this
  is the projection formula for the proper morphisms `r` and `s`
  (`isIso_projectionMorphism_boundedConstructible_padicAlgCl`), together with the compatibility of
  the derived pullback with the Koszul braidings for the left one
  (`boundedConstructibleUpperStar_map_braiding_hom_δ`).

The transported counits are compatible with the composition isomorphisms of the pullbacks
(`ProEtale.CondensedRing.upperStarComp_inv_app_comp_prodUpperStarCounit_left`,
`ProEtale.CondensedRing.upperStarComp_inv_app_comp_prodUpperStarCounit_right`).

## Main definitions

- `ProEtale.CondensedRing.prodUpperStarCounit`: the counit of `Lf^* ⊣ Rf_*` transported along a
  commutative square.
- `ProEtale.CondensedRing.prodLowerStarExternalProduct`: the Künneth map `Π`.

## Main statements

- `ProEtale.CondensedRing.isIso_prodLowerStarExternalProduct`: `Π` is an isomorphism for proper
  `f₁` and `f₂`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- Merging two `eqToHom`s after two morphisms; stated for abstract objects so that it can be
applied without unfolding the objects. -/
private lemma eqToHom_comp_eqToHom_comp_aux {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (x : O₁ ⟶ O₂) (y : O₂ ⟶ O₃) (e₁ : O₃ = O₄) (e₂ : O₄ = O₅) (e₃ : O₃ = O₅) (t : O₅ ⟶ O₆) :
    x ≫ y ≫ eqToHom e₁ ≫ eqToHom e₂ ≫ t = x ≫ y ≫ eqToHom e₃ ≫ t := by
  simp

/-- The computation behind `upperStarComp_inv_app_comp_prodUpperStarCounit_left`, stated for
abstract objects and morphisms so that it can be applied without unfolding them. -/
private lemma map_comp_eqToHom_comp_aux {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {A₁ A₂ A₃ A₄ A₅ : 𝒞} {B₁ B₂ B₃ B₄ B₅ B₆ : 𝒟} (a' : A₁ ⟶ A₂) (e₃ : A₂ = A₃) (c' : A₃ ⟶ A₄)
    (d' : A₄ ⟶ A₅) (y : F.obj A₂ ⟶ B₁) (e₁ : B₁ = B₂) (e₂ : B₂ = B₃) (c : B₃ ⟶ B₄)
    (d : B₄ ⟶ B₅) (n : F.obj A₅ ⟶ B₅) (n' : F.obj A₄ ⟶ B₄) (y' : F.obj A₃ ⟶ B₆)
    (e₄ : B₆ = B₃) (e₅ : B₁ = B₆) (hnat : F.map d' ≫ n = n' ≫ d)
    (hC : F.map c' ≫ n' = y' ≫ eqToHom e₄ ≫ c) (hE : F.map (eqToHom e₃) ≫ y' = y ≫ eqToHom e₅) :
    F.map a' ≫ y ≫ eqToHom e₁ ≫ eqToHom e₂ ≫ c ≫ d =
      F.map (a' ≫ eqToHom e₃ ≫ c' ≫ d') ≫ n := by
  simp only [Functor.map_comp, Category.assoc, hnat, reassoc_of% hC, reassoc_of% hE,
    eqToHom_trans_assoc]

/-! ### Transported counits -/

section Counit

variable {P P' X Y R : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType R.hom] [QuasiCompact R.hom] [IsSeparated R.hom]

/-- The counit of `Lf^* ⊣ Rf_*` transported along a commutative square `q ≫ p' = p ≫ f`:
`Lq^* Lp'^* Rf_* B ⟶ Lp^* B`. -/
noncomputable def prodUpperStarCounit {q : P ⟶ P'} {p : P ⟶ X} {p' : P' ⟶ Y} {f : X ⟶ Y}
    (w : q ≫ p' = p ≫ f) (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p').obj
          ((boundedConstructibleLowerStar ℓ f).obj B)) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj B :=
  (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ q p').inv.app _ ≫
    eqToHom (by rw [w]) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p f).hom.app _ ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app B)

/-- The transpose of the transported counit of a commutative square is the base change morphism
of the square. -/
lemma homEquiv_prodUpperStarCounit {q : P ⟶ P'} {p : P ⟶ X} {p' : P' ⟶ Y} {f : X ⟶ Y}
    (w : q ≫ p' = p ≫ f) (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ q).homEquiv
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p').obj
          ((boundedConstructibleLowerStar ℓ f).obj B))
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj B)
        (prodUpperStarCounit ℓ w B) =
      (boundedConstructibleBaseChange ℓ (CommSq.mk w.symm)).app B := by
  rw [boundedConstructibleBaseChange_eq_exchangeRight,
    Adjunction.exchangeRight_app (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ q)
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (CommSq.mk w.symm)) B,
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ q).homEquiv_unit,
    boundedConstructiblePullbackSquareComparison_hom_app, prodUpperStarCounit]
  simp only [Functor.map_comp, Category.assoc]

/-- For a cartesian square `q ≫ p' = p ≫ f` with `f` proper, the transpose of the transported
counit is an isomorphism: proper base change. -/
lemma isIso_homEquiv_prodUpperStarCounit {q : P ⟶ P'} {p : P ⟶ X} {p' : P' ⟶ Y} {f : X ⟶ Y}
    [IsProper f.left] (sq : IsPullback p q f p')
    (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ q).homEquiv _ _
        (prodUpperStarCounit ℓ sq.w.symm B)) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq
  rw [homEquiv_prodUpperStarCounit]
  infer_instance

/-- Changing the second morphism of a composition isomorphism of the pullbacks along an equality
of morphisms. -/
@[reassoc]
lemma map_eqToHom_comp_upperStarComp_inv_app (r : P ⟶ R) {a b : R ⟶ Y} (h : a = b)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ r).map (eqToHom (by rw [h])) ≫
        (boundedConstructibleUpperStarComp _ ℓ r b).inv.app K =
      (boundedConstructibleUpperStarComp _ ℓ r a).inv.app K ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The composition isomorphism `L(r ≫ ρ)^* ≅ Lρ^* ⋙ Lr^*` read through
`L(ρ ≫ f)^* ≅ Lf^* ⋙ Lρ^*`. -/
@[reassoc]
lemma map_upperStarComp_hom_app_comp_upperStarComp_inv_app {X' : Over (Spec (.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    (r : P ⟶ R) (ρ : R ⟶ X) (f : X ⟶ X') (K : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ r).map
        ((boundedConstructibleUpperStarComp _ ℓ ρ f).hom.app K) ≫
      (boundedConstructibleUpperStarComp _ ℓ r ρ).inv.app
        ((boundedConstructibleUpperStar _ ℓ f).obj K) =
    (boundedConstructibleUpperStarComp _ ℓ r (ρ ≫ f)).inv.app K ≫
      eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleUpperStarComp _ ℓ (r ≫ ρ) f).hom.app K := by
  have hA := boundedConstructibleUpperStarComp_assoc_app (Profinite.padicAlgClRingObj ℓ) ℓ r ρ f K
  rw [← cancel_epi ((boundedConstructibleUpperStarComp _ ℓ r (ρ ≫ f)).hom.app K),
    Iso.hom_inv_id_app_assoc, ← cancel_mono ((boundedConstructibleUpperStarComp _ ℓ r ρ).hom.app
      ((boundedConstructibleUpperStar _ ℓ f).obj K)), Category.assoc, Category.assoc,
    Category.assoc, Iso.inv_hom_id_app, hA, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]

/-- Pasting a transported counit with the trivial square of a composite `r ≫ s` on the right of
the target: for `s ≫ g = g'`, the transported counit of `(r ≫ s) ≫ g = p ≫ f` is that of
`r ≫ g' = p ≫ f` after the composition isomorphisms. -/
lemma upperStarComp_inv_app_comp_prodUpperStarCounit_right {P'' : Over (Spec (.of k))}
    [LocallyOfFiniteType P''.hom] [QuasiCompact P''.hom] [IsSeparated P''.hom]
    {r : P ⟶ R} {s : R ⟶ P''} {g : P'' ⟶ Y} {p : P ⟶ X} {f : X ⟶ Y}
    (w : (r ≫ s) ≫ g = p ≫ f) (w' : r ≫ s ≫ g = p ≫ f)
    (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp _ ℓ r s).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleLowerStar ℓ f).obj B)) ≫
      prodUpperStarCounit ℓ w B =
    (boundedConstructibleUpperStar _ ℓ r).map
        ((boundedConstructibleUpperStarComp _ ℓ s g).inv.app _) ≫
      prodUpperStarCounit ℓ w' B := by
  unfold prodUpperStarCounit
  rewrite [boundedConstructibleUpperStarComp_inv_app_comp_inv_app_assoc]
  exact eqToHom_comp_eqToHom_comp_aux _ _ _ _ _ _

/-- Pasting a transported counit with the trivial square of a composite `r ≫ s` on the left of
the source: the transported counit of `(r ≫ s) ≫ g = (r ≫ ρ) ≫ f` is `Lr^*` of that of
`s ≫ g = ρ ≫ f` after the composition isomorphisms. -/
lemma upperStarComp_inv_app_comp_prodUpperStarCounit_left {P'' : Over (Spec (.of k))}
    [LocallyOfFiniteType P''.hom] [QuasiCompact P''.hom] [IsSeparated P''.hom]
    {r : P ⟶ R} {s : R ⟶ P''} {g : P'' ⟶ Y} {ρ : R ⟶ X} {f : X ⟶ Y}
    (w : (r ≫ s) ≫ g = (r ≫ ρ) ≫ f) (w' : s ≫ g = ρ ≫ f)
    (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp _ ℓ r s).inv.app
        ((boundedConstructibleUpperStar _ ℓ g).obj ((boundedConstructibleLowerStar ℓ f).obj B)) ≫
      prodUpperStarCounit ℓ w B =
    (boundedConstructibleUpperStar _ ℓ r).map (prodUpperStarCounit ℓ w' B) ≫
      (boundedConstructibleUpperStarComp _ ℓ r ρ).inv.app B := by
  unfold prodUpperStarCounit
  rewrite [boundedConstructibleUpperStarComp_inv_app_comp_inv_app_assoc]
  exact map_comp_eqToHom_comp_aux (boundedConstructibleUpperStar _ ℓ r) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((boundedConstructibleUpperStarComp _ ℓ r ρ).inv.naturality
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app B))
    (map_upperStarComp_hom_app_comp_upperStarComp_inv_app ℓ r ρ f _)
    (map_eqToHom_comp_upperStarComp_inv_app ℓ r w' _)

end Counit

/-! ### The Künneth map -/

section Kunneth

variable {P Q R X₁ X₂ Y₁ Y₂ : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
  [LocallyOfFiniteType R.hom] [QuasiCompact R.hom] [IsSeparated R.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]

/-- **The Künneth map of a factorization `q = r ≫ s` is an isomorphism**: let
`q ≫ πᵢ = pᵢ ≫ fᵢ` be commutative squares with `f₁`, `f₂` proper, such that `q = r ≫ s` with `r`
and `s` proper, `p₁ ≫ f₁ = r ≫ (s ≫ π₁)` cartesian and `p₂ = r ≫ ρ₂` with `ρ₂ ≫ f₂ = s ≫ π₂`
cartesian. Then the transpose of
```
Lq^* (Lπ₁^* Rf₁* B₁ ⊗ Lπ₂^* Rf₂* B₂) ⟶ Lq^* Lπ₁^* Rf₁* B₁ ⊗ Lq^* Lπ₂^* Rf₂* B₂
  ⟶ Lp₁^* B₁ ⊗ Lp₂^* B₂
```
is an isomorphism. -/
theorem isIso_homEquiv_δ_tensorHom_prodUpperStarCounit {q : P ⟶ Q} {p₁ : P ⟶ X₁}
    {p₂ : P ⟶ X₂} {π₁ : Q ⟶ Y₁} {π₂ : Q ⟶ Y₂} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} (r : P ⟶ R)
    (s : R ⟶ Q) (ρ₂ : R ⟶ X₂) (hq : r ≫ s = q) (hp₂ : r ≫ ρ₂ = p₂) (w₁ : q ≫ π₁ = p₁ ≫ f₁)
    (w₂ : q ≫ π₂ = p₂ ≫ f₂) (sq₁ : IsPullback p₁ r f₁ (s ≫ π₁)) (sq₂ : IsPullback ρ₂ s f₂ π₂)
    [IsProper f₁.left] [IsProper f₂.left] [IsProper r.left] [IsProper s.left]
    (B₁ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B₂ : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ q).homEquiv _ _
      (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ q) _ _ ≫
        (prodUpperStarCounit ℓ w₁ B₁ ⊗ₘ prodUpperStarCounit ℓ w₂ B₂))) := by
  subst hq hp₂
  have hc₁ := upperStarComp_inv_app_comp_prodUpperStarCounit_right ℓ w₁ sq₁.w.symm B₁
  have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ r).homEquiv _ _
      ((boundedConstructibleUpperStarComp _ ℓ r s).inv.app _ ≫ prodUpperStarCounit ℓ w₁ B₁)) := by
    rw [hc₁, Adjunction.homEquiv_naturality_left]
    have := isIso_homEquiv_prodUpperStarCounit ℓ sq₁ B₁
    infer_instance
  have := isIso_homEquiv_prodUpperStarCounit ℓ sq₂ B₂
  have := (boundedConstructibleUpperStarLowerStarAdjunction ℓ s).isIso_leftProjectionMorphism
    (fun K M ↦ (boundedConstructibleUpperStar_map_braiding_hom_δ ℓ s K M).symm)
    ((boundedConstructibleUpperStar _ ℓ π₁).obj ((boundedConstructibleLowerStar ℓ f₁).obj B₁))
    ((boundedConstructibleUpperStar _ ℓ ρ₂).obj B₂)
  exact Adjunction.isIso_homEquiv_δ_tensorHom
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ r)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ s)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (r ≫ s))
    (boundedConstructibleUpperStarComp _ ℓ r s)
    (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ r s) _ _
    (prodUpperStarCounit ℓ sq₂.w.symm B₂) ((boundedConstructibleUpperStarComp _ ℓ r ρ₂).inv.app B₂)
    (upperStarComp_inv_app_comp_prodUpperStarCounit_left ℓ w₂ sq₂.w.symm B₂)

variable (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

/-- The *Künneth map* `Π : Rf₁* B₁ ⊠ Rf₂* B₂ ⟶ R(f₁ × f₂)_* (B₁ ⊠ B₂)` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 5): the adjoint for `Lq^* ⊣ Rq_*`,
`q = f₁ × f₂`, of
```
Lq^* (Lp₁^* Rf₁* B₁ ⊗ Lp₂^* Rf₂* B₂) ≅ Lq^* Lp₁^* Rf₁* B₁ ⊗ Lq^* Lp₂^* Rf₂* B₂
  ⟶ Lp₁^* B₁ ⊗ Lp₂^* B₂,
```
the monoidal structure of `Lq^*` followed by the counits. For proper `f_i` it is the inverse of
the `!`-Künneth isomorphism `Ku_!` of `lemma-external-duality-trace-morphism` (i) under
`Rq_* ≅ Rq_!`. -/
noncomputable def prodLowerStarExternalProduct
    (B₁ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B₂ : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ ((boundedConstructibleLowerStar ℓ f₁).obj B₁)
        ((boundedConstructibleLowerStar ℓ f₂).obj B₂) ⟶
      (boundedConstructibleLowerStar ℓ (prod.map f₁ f₂)).obj (externalProduct ℓ B₁ B₂) :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map f₁ f₂)).homEquiv _ _
    ((Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (prod.map f₁ f₂)) _ _).inv ≫
      (prodUpperStarCounit ℓ (prod.map_fst f₁ f₂) B₁ ⊗ₘ
        prodUpperStarCounit ℓ (prod.map_snd f₁ f₂) B₂))

/-- **The relative product theorem for proper morphisms** (blueprint
`lemma-kunneth-formula-compact-supports--1`, compatibility with `Rf_! ≅ Rf_*` for proper `f`, as
used in `lemma-external-duality-trace-morphism` (i)): for proper `f₁`, `f₂` the Künneth map
`Rf₁* B₁ ⊠ Rf₂* B₂ ⟶ R(f₁ × f₂)_* (B₁ ⊠ B₂)` is an isomorphism. It is the Künneth map of the
factorization `f₁ × f₂ = (f₁ × 1) ≫ (1 × f₂)` into base changes of `f₁` and `f₂`
(`isIso_homEquiv_δ_tensorHom_prodUpperStarCounit`). -/
instance isIso_prodLowerStarExternalProduct [IsProper f₁.left] [IsProper f₂.left]
    (B₁ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B₂ : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (prodLowerStarExternalProduct ℓ f₁ f₂ B₁ B₂) := by
  have : IsProper (prod.map f₁ (𝟙 X₂)).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id f₁ X₂).map (Over.forget _))
      (inferInstanceAs (IsProper f₁.left))
  have : IsProper (prod.map (𝟙 Y₁) f₂).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_snd_with_id f₂ Y₁).map (Over.forget _))
      (inferInstanceAs (IsProper f₂.left))
  have h : prod.map (𝟙 Y₁) f₂ ≫ prod.fst = prod.fst := by simp
  have sq₁ : IsPullback (prod.fst : X₁ ⨯ X₂ ⟶ X₁) (prod.map f₁ (𝟙 X₂)) f₁
      (prod.map (𝟙 Y₁) f₂ ≫ prod.fst) := by
    rw [h]
    exact IsPullback.of_prod_fst_with_id f₁ X₂
  rw [prodLowerStarExternalProduct, Functor.Monoidal.μIso_inv]
  exact isIso_homEquiv_δ_tensorHom_prodUpperStarCounit ℓ (prod.map f₁ (𝟙 X₂))
    (prod.map (𝟙 Y₁) f₂) prod.snd (by simp) (by simp) _ _ sq₁
    (IsPullback.of_prod_snd_with_id f₂ Y₁) B₁ B₂

end Kunneth

end AlgebraicGeometry.ProEtale.CondensedRing
