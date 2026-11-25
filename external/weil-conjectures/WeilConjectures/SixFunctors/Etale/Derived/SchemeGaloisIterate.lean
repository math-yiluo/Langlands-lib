/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SchemeGaloisComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.WeilDatum

/-!
# Iterates of the comparison of the scheme and the Galois Frobenius pullbacks

Let `g, g' : X ⟶ X` be endomorphisms of a scheme and `κ : Lg^* ≅ Lg'^*` an isomorphism of
derived pullbacks on the étale site. Writing `g_m = g^m` (`AlgebraicGeometry.ProEtale.iterateHom`),
`κ` iterates to isomorphisms `κ_m : Lg_m^* ≅ Lg'_m^*`, with `κ_0 = 𝟙` and
```
κ_{m+1} : L(g ≫ g_m)^* ≅ Lg^* Lg_m^* --Lg^* κ_m--> Lg^* Lg'_m^* --κ--> Lg'^* Lg'_m^*
  ≅ L(g' ≫ g'_m)^*
```
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateHomIso`). They are compatible with
iteration in the sense that `κ_{m+n}` is `Lg_n^* κ_m` followed by `κ_n` at `Lg'_m^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateHomIso_add_hom_app`); for `n = 1` and `m = 1`
these are the two recursions `κ_{m+1} = κ_1 ∘ Lg^* κ_m` and `κ_{m+1} = κ_m ∘ Lg_m^* κ_1` of
blueprint `lemma-scheme-frobenius-geometric-frobenius`.

The iterates of a Weil datum `φ : Lg'^* K ⟶ K` on the étale site
(`AlgebraicGeometry.Etale.weilDatumIterate`, the étale analogue of
`AlgebraicGeometry.ProEtale.weilDatumIterate`, blueprint
`definition-frobenius-correspondences-their-operators`) satisfy `(φ ∘ κ)_m = φ_m ∘ κ_m`
(`AlgebraicGeometry.Etale.weilDatumIterate_comp`).

For the scheme Frobenius `Φ_X` and the geometric Galois Frobenius `Fr_X` of a geometric fibre, `κ`
is `AlgebraicGeometry.Etale.leftDerivedUpperStarGeometricFiberFrobeniusIso`; its iterates are
`AlgebraicGeometry.Etale.leftDerivedUpperStarGeometricFiberFrobeniusIterateIso`, and for
`ψ = φ ∘ κ_1` we get `ψ_m = φ_m ∘ κ_m`
(`AlgebraicGeometry.Etale.weilDatumIterate_comp_geometricFiberFrobenius`,
`AlgebraicGeometry.Etale.weilDatumIterate_schemeFrobeniusForm_hom`).

## Main definitions

- `AlgebraicGeometry.Etale.weilDatumIterate`: the iterates `φ_m` of a Weil datum.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateHomIso`: the iterates `κ_m`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarGeometricFiberFrobeniusIterateIso`:
  `κ_m : L(Φ_X^m)^* ≅ L(Fr_X^m)^*`.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateHomIso_add_hom_app`: compatibility of the
  `κ_m` with iteration.
- `AlgebraicGeometry.Etale.weilDatumIterate_comp`: `(φ ∘ κ)_m = φ_m ∘ κ_m`.
- `AlgebraicGeometry.Etale.weilDatumIterate_schemeFrobeniusForm_hom`: `ψ_m = φ_m κ_m`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

open ProEtale (iterateHom iterateHom_succ iterateHom_add)

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

section Iterate

variable {X : Scheme.{u}} {g g' : X ⟶ X}

/-- Blueprint `definition-frobenius-correspondences-their-operators` (iterates, étale site): the
iterate `φ_m : Lg_m^* K ⟶ K` of a Weil datum `φ : Lg^* K ⟶ K` on the étale site, for the iterate
`g_m = g^m` (`AlgebraicGeometry.ProEtale.iterateHom`): `φ_0` is the identification
`L(𝟙 X)^* K ≅ K` and `φ_{m+1}` is the composite
```
L(g_{m+1})^* K = L(g ≫ g_m)^* K ≅ Lg^* Lg_m^* K --Lg^* φ_m--> Lg^* K --φ--> K.
```
This is the étale analogue of `AlgebraicGeometry.ProEtale.weilDatumIterate`. -/
noncomputable def weilDatumIterate {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (φ : L((g)^*[A]).obj K ⟶ K) : (m : ℕ) → L((iterateHom g m)^*[A]).obj K ⟶ K
  | 0 => (leftDerivedUpperStarId A X).hom.app K
  | m + 1 =>
    (leftDerivedUpperStarComp A g (iterateHom g m) _ (iterateHom_succ g m)).hom.app K ≫
      L((g)^*[A]).map (weilDatumIterate φ m) ≫ φ

variable {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}

lemma weilDatumIterate_zero (φ : L((g)^*[A]).obj K ⟶ K) :
    weilDatumIterate φ 0 = (leftDerivedUpperStarId A X).hom.app K :=
  rfl

lemma weilDatumIterate_succ (φ : L((g)^*[A]).obj K ⟶ K) (m : ℕ) :
    weilDatumIterate φ (m + 1) =
      (leftDerivedUpperStarComp A g (iterateHom g m) _ (iterateHom_succ g m)).hom.app K ≫
        L((g)^*[A]).map (weilDatumIterate φ m) ≫ φ :=
  rfl

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius` (the iterates `κ_m`): an isomorphism
`κ : Lg^* ≅ Lg'^*` of derived pullbacks along endomorphisms `g, g'` of `X` iterates to
isomorphisms `κ_m : Lg_m^* ≅ Lg'_m^*` for the iterates `g_m = g^m`, `g'_m = g'^m`: `κ_0` is the
identity and
```
κ_{m+1} : L(g ≫ g_m)^* ≅ Lg^* Lg_m^* --Lg^* κ_m--> Lg^* Lg'_m^* --κ--> Lg'^* Lg'_m^*
  ≅ L(g' ≫ g'_m)^*.
```
-/
noncomputable def leftDerivedUpperStarIterateHomIso (κ : L((g)^*[A]) ≅ L((g')^*[A])) :
    (m : ℕ) → (L((iterateHom g m)^*[A]) ≅ L((iterateHom g' m)^*[A]))
  | 0 => Iso.refl _
  | m + 1 =>
    leftDerivedUpperStarComp A g (iterateHom g m) _ (iterateHom_succ g m) ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarIterateHomIso κ m) L((g)^*[A]) ≪≫
      Functor.isoWhiskerLeft L((iterateHom g' m)^*[A]) κ ≪≫
      (leftDerivedUpperStarComp A g' (iterateHom g' m) _ (iterateHom_succ g' m)).symm

variable (κ : L((g)^*[A]) ≅ L((g')^*[A]))

@[simp]
lemma leftDerivedUpperStarIterateHomIso_zero :
    leftDerivedUpperStarIterateHomIso κ 0 = Iso.refl _ :=
  rfl

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius` (compatibility of `κ_m` with
iteration, recursive form): `κ_{m+1}` is `Lg^* κ_m` followed by `κ` at `Lg'_m^* K`. -/
lemma leftDerivedUpperStarIterateHomIso_succ_hom_app (m : ℕ) (M : _root_.DerivedCategory
    (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarIterateHomIso κ (m + 1)).hom.app M =
      (leftDerivedUpperStarComp A g (iterateHom g m) _ (iterateHom_succ g m)).hom.app M ≫
        L((g)^*[A]).map ((leftDerivedUpperStarIterateHomIso κ m).hom.app M) ≫
          κ.hom.app (L((iterateHom g' m)^*[A]).obj M) ≫
            (leftDerivedUpperStarComp A g' (iterateHom g' m) _ (iterateHom_succ g' m)).inv.app
              M := by
  simp [leftDerivedUpperStarIterateHomIso]

/-- The first iterate of `κ` is `κ`, up to the identifications `g^1 = g ≫ 𝟙` and
`L(𝟙 X)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarIterateHomIso_one_hom_app (M : _root_.DerivedCategory
    (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarIterateHomIso κ 1).hom.app M =
      (leftDerivedUpperStarComp A g (𝟙 X) _ (by simp)).hom.app M ≫
        L((g)^*[A]).map ((leftDerivedUpperStarId A X).hom.app M) ≫ κ.hom.app M ≫
          L((g')^*[A]).map ((leftDerivedUpperStarId A X).inv.app M) ≫
            (leftDerivedUpperStarComp A g' (𝟙 X) _ (by simp)).inv.app M := by
  have hn := κ.hom.naturality ((leftDerivedUpperStarId A X).hom.app M)
  simp only [Functor.id_obj] at hn
  rw [leftDerivedUpperStarIterateHomIso_succ_hom_app, reassoc_of% hn, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [leftDerivedUpperStarIterateHomIso_zero, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  rfl

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius` (compatibility of `κ_m` with
iteration): under `g_{m+n} = g_n ≫ g_m`, the isomorphism `κ_{m+n}` is `Lg_n^* κ_m` followed by
`κ_n` at `Lg'_m^* M`:
```
L(g_{m+n})^* M ≅ Lg_n^* Lg_m^* M --Lg_n^* κ_m--> Lg_n^* Lg'_m^* M --κ_n--> Lg'_n^* Lg'_m^* M
  ≅ L(g'_{m+n})^* M.
```
For `m = 1` this is the recursion `κ_{n+1} = κ_{n, Lg'^* M} ∘ Lg_n^* κ_1` of the blueprint, and
for `n = 1` it is the defining recursion
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateHomIso_succ_hom_app`. -/
theorem leftDerivedUpperStarIterateHomIso_add_hom_app (m n : ℕ)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarIterateHomIso κ (m + n)).hom.app M =
      (leftDerivedUpperStarComp A (iterateHom g n) (iterateHom g m) _
          (iterateHom_add g m n)).hom.app M ≫
        L((iterateHom g n)^*[A]).map ((leftDerivedUpperStarIterateHomIso κ m).hom.app M) ≫
          (leftDerivedUpperStarIterateHomIso κ n).hom.app (L((iterateHom g' m)^*[A]).obj M) ≫
            (leftDerivedUpperStarComp A (iterateHom g' n) (iterateHom g' m) _
              (iterateHom_add g' m n)).inv.app M := by
  induction n with
  | zero =>
    have e : ∀ (p : X ⟶ X), (leftDerivedUpperStarComp A (𝟙 X) p p
        (Category.id_comp p).symm).inv.app M =
          (leftDerivedUpperStarId A X).hom.app (L((p)^*[A]).obj M) := fun p ↦ by
      rw [← cancel_epi ((leftDerivedUpperStarComp A (𝟙 X) p p
        (Category.id_comp p).symm).hom.app M), Iso.hom_inv_id_app,
        leftDerivedUpperStarComp_id_left_hom_app]
    have e' : (leftDerivedUpperStarComp A (𝟙 X) (iterateHom g m) (iterateHom g m)
        (Category.id_comp _).symm).hom.app M =
          (leftDerivedUpperStarId A X).inv.app (L((iterateHom g m)^*[A]).obj M) := by
      rw [← cancel_mono ((leftDerivedUpperStarId A X).hom.app _), Iso.inv_hom_id_app,
        leftDerivedUpperStarComp_id_left_hom_app]
      rfl
    change _ = (leftDerivedUpperStarComp A (𝟙 X) (iterateHom g m) (iterateHom g m)
        (Category.id_comp _).symm).hom.app M ≫ _ ≫ 𝟙 _ ≫
          (leftDerivedUpperStarComp A (𝟙 X) (iterateHom g' m) (iterateHom g' m)
            (Category.id_comp _).symm).inv.app M
    rw [e, e', Category.id_comp, NatTrans.naturality]
    simp
  | succ n ih =>
    refine (leftDerivedUpperStarIterateHomIso_succ_hom_app κ (m + n) M).trans ?_
    rw [ih, leftDerivedUpperStarIterateHomIso_succ_hom_app κ n]
    have a := leftDerivedUpperStarComp_assoc'_app A g (iterateHom g n) (iterateHom g m)
      (iterateHom g (n + 1)) (iterateHom g (m + n)) (iterateHom g (m + n + 1))
      (iterateHom_succ g n) (iterateHom_add g m n) (iterateHom_add g m (n + 1)) M
    have a' := map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app A g'
      (iterateHom g' n) (iterateHom g' m) (iterateHom g' (n + 1)) (iterateHom g' (m + n))
      (iterateHom g' (m + n + 1)) (iterateHom_succ g' n) (iterateHom_add g' m n)
      (iterateHom_add g' m (n + 1)) M
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% a, κ.hom.naturality_assoc
        ((leftDerivedUpperStarComp A (iterateHom g' n) (iterateHom g' m) _
          (iterateHom_add g' m n)).inv.app M), a',
      (leftDerivedUpperStarComp A g (iterateHom g n) _ (iterateHom_succ g n)).hom.naturality_assoc
        ((leftDerivedUpperStarIterateHomIso κ m).hom.app M)]
    rfl

end Iterate

section Datum

variable {X : Scheme.{u}} {g g' : X ⟶ X} (κ : L((g)^*[A]) ≅ L((g')^*[A]))
  {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius` (`ψ_m = φ_m κ_m`): for an isomorphism
`κ : Lg^* ≅ Lg'^*` and a Weil datum `φ : Lg'^* K ⟶ K`, the iterates of the Weil datum
`ψ = φ ∘ κ_K : Lg^* K ⟶ K` are `ψ_m = φ_m ∘ κ_{m,K}`, `κ_m` being the iterates of `κ`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateHomIso`). -/
theorem weilDatumIterate_comp (φ : L((g')^*[A]).obj K ⟶ K) (m : ℕ) :
    weilDatumIterate (κ.hom.app K ≫ φ) m =
      (leftDerivedUpperStarIterateHomIso κ m).hom.app K ≫ weilDatumIterate φ m := by
  induction m with
  | zero => simp [weilDatumIterate_zero]
  | succ m ih =>
    rw [weilDatumIterate_succ, weilDatumIterate_succ, ih,
      leftDerivedUpperStarIterateHomIso_succ_hom_app]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [κ.hom.naturality_assoc]

end Datum

section GeometricFiberFrobenius

variable (A) {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius` (the isomorphisms `κ_m`): the
isomorphisms `κ_m : L(Φ_X^m)^* ≅ L(Fr_X^m)^*` between the derived pullbacks along the iterates
of the scheme Frobenius `Φ_X` and of the geometric Galois Frobenius `Fr_X` of the geometric
fibre `X` of `f`, iterating
`κ_1 = AlgebraicGeometry.Etale.leftDerivedUpperStarGeometricFiberFrobeniusIso`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateHomIso`). They are natural, and compatible
with iteration by `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateHomIso_add_hom_app`. -/
noncomputable def leftDerivedUpperStarGeometricFiberFrobeniusIterateIso (m : ℕ) :
    L((iterateHom f.geometricFiberFrobenius m)^*[A]) ≅
      L((iterateHom f.geometricGaloisFrobenius.asIso.hom m)^*[A]) :=
  leftDerivedUpperStarIterateHomIso (leftDerivedUpperStarGeometricFiberFrobeniusIso A f) m

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius` (`ψ_m = φ_m κ_m`, for an arbitrary
morphism `φ`): for a morphism `φ : LFr_X^* K ⟶ K`, the iterates of
`ψ = φ ∘ κ_{1,K} : LΦ_X^* K ⟶ K` are `ψ_m = φ_m ∘ κ_{m,K}`. -/
theorem weilDatumIterate_comp_geometricFiberFrobenius
    {K : _root_.DerivedCategory (Sheaf f.geometricFiber.smallEtaleTopology A)}
    (φ : L((f.geometricGaloisFrobenius.asIso.hom)^*[A]).obj K ⟶ K) (m : ℕ) :
    weilDatumIterate ((leftDerivedUpperStarGeometricFiberFrobeniusIso A f).hom.app K ≫ φ) m =
      (leftDerivedUpperStarGeometricFiberFrobeniusIterateIso A f m).hom.app K ≫
        weilDatumIterate φ m :=
  weilDatumIterate_comp _ φ m

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius` (`ψ_m = φ_m κ_m`): for a Weil
structure `φ : LFr_X^* K ≅ K`, the iterates of its scheme-Frobenius form `ψ = φ ∘ κ_{1,K}`
(`AlgebraicGeometry.Etale.schemeFrobeniusForm`) are `ψ_m = φ_m ∘ κ_{m,K}`. -/
theorem weilDatumIterate_schemeFrobeniusForm_hom
    {K : _root_.DerivedCategory (Sheaf f.geometricFiber.smallEtaleTopology A)}
    (φ : L((f.geometricGaloisFrobenius.asIso.hom)^*[A]).obj K ≅ K) (m : ℕ) :
    weilDatumIterate (schemeFrobeniusForm A φ).hom m =
      (leftDerivedUpperStarGeometricFiberFrobeniusIterateIso A f m).hom.app K ≫
        weilDatumIterate φ.hom m :=
  weilDatumIterate_comp_geometricFiberFrobenius A f φ.hom m

end GeometricFiberFrobenius

end Etale

end AlgebraicGeometry
