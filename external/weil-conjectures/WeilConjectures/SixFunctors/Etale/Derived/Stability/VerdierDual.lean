/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteEtaleAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!
# The Tor amplitude of the Verdier dual

This file proves the auxiliary statements used for the Tor bound of the Verdier dual
(`lemma-verdier-duality-preserves-constructibility--1`):

- `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerStar`: the internal hom into
  a direct image, `RHom(K, Rf_* M) ≅ Rf_* RHom(Lf^* K, M)`;
- `AlgebraicGeometry.Etale.torAmplitudeIn_obj₂_of_distTriang`: Tor amplitude in a given interval
  is closed under extensions;
- `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_obj₂_of_distTriang`: the same for the
  internal hom out of a fixed complex, which is triangulated in its second variable;
- `AlgebraicGeometry.Etale.torAmplitudeIn_of_leftDerivedUpperStar_of_surjective`: Tor amplitude
  descends along a surjective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The internal hom into a direct image -/

/-- **The internal hom into a direct image**: for `f : Z ⟶ X` and `K` on `X`,
`RHom_X(K, Rf_* M) ≅ Rf_* RHom_Z(Lf^* K, M)`. Both sides are right adjoint to functors of
`T ∈ D(X_ét)`: the left one to `T ↦ Lf^*(K ⊗ᴸ T)`, the right one to `T ↦ Lf^* K ⊗ᴸ Lf^* T`, and
these agree since `Lf^*` is monoidal. -/
theorem nonempty_iso_derivedHom_rightDerivedLowerStar {Z X : Scheme.{u}} (f : Z ⟶ X)
    (K : DerivedCategoryModule Λ X) (M : DerivedCategoryModule Λ Z) :
    Nonempty (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj M) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj
        (((RHom(Z)[ModuleCat.{u + 1} Λ]).obj (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          M)) := by
  let adj₁ := (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  let adj₂ := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).comp
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))
  let e : (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
        (-⊗ᴸ-(Z)[ModuleCat.{u + 1} Λ]).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
    NatIso.ofComponents (fun T ↦ leftDerivedUpperStarTensorIso _ f K T) fun φ ↦
      ((leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} Λ) f).hom.app K).naturality φ
  exact ⟨((adj₁.ofNatIsoLeft e).rightAdjointUniq adj₂).app M⟩

/-! ### Extensions and descent, for a general coefficient category -/

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **Tor amplitude is closed under extensions**: in a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` whose outer terms have Tor amplitude in `[a, b]`, so does `X₂`, the
derived tensor product with a sheaf being triangulated. -/
lemma torAmplitudeIn_obj₂_of_distTriang' {X : Scheme.{u}}
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) {a b : ℤ} (h₁ : torAmplitudeIn A X a b T.obj₁)
    (h₃ : torAmplitudeIn A X a b T.obj₃) : torAmplitudeIn A X a b T.obj₂ := fun F ↦ by
  let G := (-⊗ᴸ-(X)[A]).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  let := _root_.DerivedCategory.commShiftTensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
  have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
  obtain ⟨g₁, l₁⟩ := h₁ F
  obtain ⟨g₃, l₃⟩ := h₃ F
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ (G.map_distinguished _ hT) _ g₁ g₃,
    _root_.DerivedCategory.TStructure.t.isLE₂ _ (G.map_distinguished _ hT) _ l₁ l₃⟩

/-- **Tor amplitude descends along a morphism reflecting vanishing**: if `p : U' ⟶ U` is such
that
vanishing of homology sheaves can be tested after pullback along `p` (e.g. `p` surjective),
and `Lp^* N` has Tor amplitude in `[a, b]`, then so does `N`, since
`p^*(N ⊗ᴸ G) ≅ Lp^* N ⊗ᴸ p^* G`. -/
lemma torAmplitudeIn_of_leftDerivedUpperStar' {U' U : Scheme.{u}} (p : U' ⟶ U)
    [(p)^*[A].PreservesFlat] (hp : ∀ (M : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A))
      (q : ℤ), IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj (D((p)^*[A]).obj M)) →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj M))
    {N : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)} {a b : ℤ}
    (h : torAmplitudeIn A U' a b ((L((p)^*[A])).obj N)) :
    torAmplitudeIn A U a b N := fun G ↦ by
  let M := ((-⊗ᴸ-(U)[A]).obj N).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj G)
  let e : D((p)^*[A]).obj M ≅ ((-⊗ᴸ-(U')[A]).obj ((L((p)^*[A])).obj N)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj ((p)^*[A].obj G)) :=
    ((leftDerivedUpperStarIsoMapDerivedCategory A p).app _).symm ≪≫
      leftDerivedUpperStarTensorIso A p _ _ ≪≫
      ((-⊗ᴸ-(U')[A]).obj ((L((p)^*[A])).obj N)).mapIso
        ((singleFunctorCompLeftDerivedUpperStarIso A p).app G)
  obtain ⟨h₁, h₂⟩ := h ((p)^*[A].obj G)
  have h₁' : _root_.DerivedCategory.TStructure.t.IsGE (((-⊗ᴸ-(U')[A]).obj
      ((L((p)^*[A])).obj N)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((p)^*[A].obj G))) a := h₁
  have h₂' : _root_.DerivedCategory.TStructure.t.IsLE (((-⊗ᴸ-(U')[A]).obj
      ((L((p)^*[A])).obj N)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((p)^*[A].obj G))) b := h₂
  have hM₁ := _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have hM₂ := _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  exact ⟨(_root_.DerivedCategory.isGE_iff M a).2 fun q hq ↦ hp M q
      ((_root_.DerivedCategory.isGE_iff _ a).1 hM₁ q hq),
    (_root_.DerivedCategory.isLE_iff M b).2 fun q hq ↦ hp M q
      ((_root_.DerivedCategory.isLE_iff _ b).1 hM₂ q hq)⟩

end General

/-! ### Extensions and descent, for coefficients in a ring -/

/-- **Tor amplitude is closed under extensions**, for sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.torAmplitudeIn_obj₂_of_distTriang'`). -/
lemma torAmplitudeIn_obj₂_of_distTriang {X : Scheme.{u}}
    (T : Triangle (DerivedCategoryModule Λ X)) (hT : T ∈ distTriang _) {a b : ℤ}
    (h₁ : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b T.obj₁)
    (h₃ : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b T.obj₃) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b T.obj₂ :=
  torAmplitudeIn_obj₂_of_distTriang' (ModuleCat.{u + 1} Λ) T hT h₁ h₃

/-- The internal hom `RHom(K, -)` out of a fixed complex `K` sends distinguished triangles to
distinguished triangles, being right adjoint to the triangulated `K ⊗ᴸ -`; hence if `RHom(K, -)`
of the outer terms of a distinguished triangle has Tor amplitude in `[a, b]`, so does
`RHom(K, -)` of the middle term. -/
lemma torAmplitudeIn_derivedHom_obj₂_of_distTriang {X : Scheme.{u}}
    (K : DerivedCategoryModule Λ X) (T : Triangle (DerivedCategoryModule Λ X))
    (hT : T ∈ distTriang _) {a b : ℤ}
    (h₁ : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj T.obj₁))
    (h₃ : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj T.obj₃)) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj T.obj₂) := by
  have : ((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).IsTriangulated :=
    (derivedTensorHomAdjunction _ K).isTriangulated_rightAdjoint
  exact torAmplitudeIn_obj₂_of_distTriang Λ _
    (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).map_distinguished _ hT) h₁ h₃

section Descent

open ZeroObject

/-- A sheaf of `Λ`-modules on the small étale site whose pullback along a surjective morphism
vanishes is zero: pullbacks along a jointly surjective family reflect isomorphisms. -/
lemma isZero_of_isZero_upperStar_of_surjective {U' U : Scheme.{u}} (p : U' ⟶ U)
    (hp : Function.Surjective p.base) {F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h : IsZero ((p)^*[ModuleCat.{u + 1} Λ].obj F)) : IsZero F := by
  have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (ι := PUnit.{u + 1}) (fun _ ↦ p) (fun x ↦ by
      obtain ⟨y, rfl⟩ := hp x
      exact ⟨⟨⟩, y, rfl⟩) (0 : F ⟶ 0) (fun _ ↦
        isIso_of_source_target_iso_zero _ h.isoZero
          (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

/-- A complex whose pullback along a surjective morphism has vanishing `q`-th homology sheaf
has vanishing `q`-th homology sheaf. -/
lemma isZero_homology_of_surjective {U' U : Scheme.{u}} (p : U' ⟶ U)
    (hp : Function.Surjective p.base) (M : DerivedCategoryModule Λ U) (q : ℤ)
    (hq : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (D((p)^*[ModuleCat.{u + 1} Λ]).obj M))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj M) :=
  isZero_of_isZero_upperStar_of_surjective Λ p hp (hq.of_iso
    ((((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app M))

end Descent

/-- **Tor amplitude descends along a surjective morphism**, for sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.torAmplitudeIn_of_leftDerivedUpperStar'`). -/
lemma torAmplitudeIn_of_leftDerivedUpperStar_of_surjective {U' U : Scheme.{u}} (p : U' ⟶ U)
    (hp : Function.Surjective p.base) {N : DerivedCategoryModule Λ U} {a b : ℤ}
    (h : torAmplitudeIn (ModuleCat.{u + 1} Λ) U' a b ((L((p)^*[ModuleCat.{u + 1} Λ])).obj N)) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b N :=
  torAmplitudeIn_of_leftDerivedUpperStar' (ModuleCat.{u + 1} Λ) p
    (isZero_homology_of_surjective Λ p hp) h

end Etale

end AlgebraicGeometry
