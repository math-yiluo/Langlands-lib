/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
public import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# The internal-hom comparison of a derived pullback

For a morphism of schemes `g : Y ⟶ X` and a monoidal Grothendieck abelian coefficient category
`A`, the derived pullback `Lg^* : D(X_ét, A) ⥤ D(Y_ét, A)` is a monoidal functor
(`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`), so it has a canonical comparison map

`ρ_{K, M} : Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)`

(`AlgebraicGeometry.Etale.derivedHomUpperStarComparison`), the transpose of
`Lg^* K ⊗ᴸ Lg^* RHom(K, M) ≅ Lg^*(K ⊗ᴸ RHom(K, M)) ⟶ Lg^* M`. It is the comparison map of the
third assertion of blueprint `lemma-restriction-geometric-generic-fibre`, and it is compatible with
evaluation by construction (`AlgebraicGeometry.Etale.derivedHomUpperStarComparison_ev`): this is
what identifies `g^* δ_K` with `δ_{g^* K}` in `lemma-double-dual-geometric-generic-fibre--1`.

This file records the general properties of `ρ` used to prove that it is an isomorphism over a
geometric generic point
(`WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric`):

- it is an isomorphism when `K` has a left dual
  (`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_of_exactPairing`);
- it is an isomorphism at `(K, Rg_* N)` when `Rg_*` is fully faithful, e.g. for open and closed
  immersions (`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_rightDerivedLowerStar`);
- it is compatible with composition
  (`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_iff_comp`), the composition
  isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` being monoidal
  (`AlgebraicGeometry.Etale.isMonoidal_leftDerivedUpperStarComp_hom`).

It also records the isomorphisms `RHom(K, Rf_* N) ≅ Rf_* RHom(Lf^* K, N)`
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerStarIso`) and, for `D` a left dual of `P`,
`RHom(P, N) ≅ D ⊗ᴸ N` (`AlgebraicGeometry.Etale.derivedHomIsoDerivedTensorOfExactPairing`).

## Implementation notes

Everything is stated for a general coefficient category `A`; see the implementation notes of
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure` for why statements about the
monoidal structure should not be elaborated at `A = ModuleCat Λ` directly.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

/-- Blueprint `lemma-restriction-geometric-generic-fibre`, the internal-hom comparison: for
`g : Y ⟶ X`, the canonical map `Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)`, the comparison map
`CategoryTheory.Functor.LaxMonoidal.ihomComparison` of the monoidal functor `Lg^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`). It is the transpose of
`Lg^* K ⊗ᴸ Lg^* RHom(K, M) ≅ Lg^*(K ⊗ᴸ RHom(K, M)) ⟶ Lg^* M`, the pullback of the evaluation
(`AlgebraicGeometry.Etale.derivedHomUpperStarComparison_ev`). -/
noncomputable def derivedHomUpperStarComparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (L((g)^*[A])).obj ((RHom(X)[A].obj (op K)).obj M) ⟶
      (RHom(Y)[A].obj (op ((L((g)^*[A])).obj K))).obj ((L((g)^*[A])).obj M) :=
  letI := leftDerivedUpperStarMonoidal A g
  (Functor.LaxMonoidal.ihomComparison L((g)^*[A]) K).app M

/-- Blueprint `lemma-restriction-geometric-generic-fibre`: the internal-hom comparison preserves
evaluation. The square
```
  Lg^*K ⊗ᴸ Lg^* RHom(K, M) ──1 ⊗ ρ──▶ Lg^*K ⊗ᴸ RHom(Lg^*K, Lg^*M)
            │ μ                                   │ ev
            ▼                                     ▼
  Lg^*(K ⊗ᴸ RHom(K, M)) ───────Lg^* ev──────▶ Lg^* M
```
commutes, `μ` being the tensor comparison of the monoidal functor `Lg^*`. -/
lemma derivedHomUpperStarComparison_ev {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A g
    (L((g)^*[A])).obj K ◁ derivedHomUpperStarComparison A g K M ≫
        (ihom.ev ((L((g)^*[A])).obj K)).app ((L((g)^*[A])).obj M) =
      Functor.LaxMonoidal.μ (L((g)^*[A])) K _ ≫ (L((g)^*[A])).map ((ihom.ev K).app M) :=
  letI := leftDerivedUpperStarMonoidal A g
  Functor.LaxMonoidal.ihomComparison_ev _ K M

/-- The internal-hom comparison is natural in the second variable. -/
@[reassoc]
lemma derivedHomUpperStarComparison_naturality {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : M ⟶ M') :
    (L((g)^*[A])).map ((RHom(X)[A].obj (op K)).map f) ≫ derivedHomUpperStarComparison A g K M' =
      derivedHomUpperStarComparison A g K M ≫
        (RHom(Y)[A].obj (op ((L((g)^*[A])).obj K))).map ((L((g)^*[A])).map f) :=
  letI := leftDerivedUpperStarMonoidal A g
  (Functor.LaxMonoidal.ihomComparison L((g)^*[A]) K).naturality f

/-- The internal-hom comparison is an isomorphism at `(K, M)` if and only if it is one at any
`(K, M')` with `M ≅ M'`. -/
lemma isIso_derivedHomUpperStarComparison_iff_of_iso_right {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : M ≅ M') :
    IsIso (derivedHomUpperStarComparison A g K M) ↔
      IsIso (derivedHomUpperStarComparison A g K M') :=
  letI := leftDerivedUpperStarMonoidal A g
  Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso_right _ K e

/-- The internal-hom comparison is an isomorphism at `(K, M)` if and only if it is one at any
`(K', M)` with `K ≅ K'`. -/
lemma isIso_derivedHomUpperStarComparison_iff_of_iso_left {X Y : Scheme.{u}} (g : Y ⟶ X)
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : K ≅ K')
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (derivedHomUpperStarComparison A g K M) ↔
      IsIso (derivedHomUpperStarComparison A g K' M) :=
  letI := leftDerivedUpperStarMonoidal A g
  Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso_left _ e M

/-- **The site-perfect case.** If `P` has a left dual `D`, the internal-hom comparison
`Lg^* RHom(P, M) ⟶ RHom(Lg^* P, Lg^* M)` is an isomorphism for every `M`
(`CategoryTheory.Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing`). -/
lemma isIso_derivedHomUpperStarComparison_of_exactPairing {X Y : Scheme.{u}} (g : Y ⟶ X)
    (D P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) [ExactPairing D P]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (derivedHomUpperStarComparison A g P M) :=
  letI := leftDerivedUpperStarMonoidal A g
  Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing _ D P M

/-- If `Rf_*` is fully faithful (the counit of `Lf^* ⊣ Rf_*` is invertible), the internal-hom
comparison `Lf^* RHom(K, Rf_* N) ⟶ RHom(Lf^* K, Lf^* Rf_* N)` is an isomorphism
(`CategoryTheory.Functor.Monoidal.isIso_ihomComparison_app_rightAdjoint`). This applies to open
and to closed immersions. -/
lemma isIso_derivedHomUpperStarComparison_rightDerivedLowerStar {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIso (derivedUpperStarLowerStarAdjunction A f).counit]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (derivedHomUpperStarComparison A f K ((R((f)_*[A])).obj N)) :=
  letI := leftDerivedUpperStarMonoidal A f
  Functor.Monoidal.isIso_ihomComparison_app_rightAdjoint
    (derivedUpperStarLowerStarAdjunction A f) K N

/-- The isomorphism `RHom(K, Rf_* N) ≅ Rf_* RHom(Lf^* K, N)`
(`CategoryTheory.Functor.Monoidal.isIso_ihomRightAdjointComparison`). -/
noncomputable def derivedHomRightDerivedLowerStarIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (RHom(X)[A].obj (op K)).obj ((R((f)_*[A])).obj N) ≅
      (R((f)_*[A])).obj ((RHom(Y)[A].obj (op ((L((f)^*[A])).obj K))).obj N) :=
  letI := leftDerivedUpperStarMonoidal A f
  have := Functor.Monoidal.isIso_ihomRightAdjointComparison
    (derivedUpperStarLowerStarAdjunction A f) K N
  asIso (Functor.Monoidal.ihomRightAdjointComparison (derivedUpperStarLowerStarAdjunction A f) K N)

/-- If `D` is a left dual of `P`, then `RHom(P, N) ≅ D ⊗ᴸ N`
(`CategoryTheory.MonoidalClosed.ihomObjIsoTensor`). -/
noncomputable def derivedHomIsoDerivedTensorOfExactPairing {X : Scheme.{u}}
    (D P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) [ExactPairing D P]
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (RHom(X)[A].obj (op P)).obj N ≅ ((-⊗ᴸ-(X)[A]).obj D).obj N :=
  ihomObjIsoTensor D P N

section Composition

variable {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
  [NatTrans.IsMonoidal (Etale.upperStarComp A g₁ g₂ g₁₂ hg).hom]

/-- The composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) is a monoidal natural isomorphism, for the
monoidal structures `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`,
`AlgebraicGeometry.Etale.leftDerivedUpperStarComp_hom_app_unit`). -/
lemma isMonoidal_leftDerivedUpperStarComp_hom :
    letI := leftDerivedUpperStarMonoidal A g₁
    letI := leftDerivedUpperStarMonoidal A g₂
    letI := leftDerivedUpperStarMonoidal A g₁₂
    NatTrans.IsMonoidal (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom := by
  let := leftDerivedUpperStarMonoidal A g₁
  let := leftDerivedUpperStarMonoidal A g₂
  let := leftDerivedUpperStarMonoidal A g₁₂
  constructor
  · have hu := leftDerivedUpperStarComp_hom_app_unit A g₁ g₂ g₁₂ hg
    have e₁ : (letI := leftDerivedUpperStarOplaxMonoidal A g₁;
        Functor.OplaxMonoidal.η (L((g₁)^*[A]))) = Functor.OplaxMonoidal.η (L((g₁)^*[A])) := rfl
    have e₂ : (letI := leftDerivedUpperStarOplaxMonoidal A g₂;
        Functor.OplaxMonoidal.η (L((g₂)^*[A]))) = Functor.OplaxMonoidal.η (L((g₂)^*[A])) := rfl
    have e₁₂ : (letI := leftDerivedUpperStarOplaxMonoidal A g₁₂;
        Functor.OplaxMonoidal.η (L((g₁₂)^*[A]))) = Functor.OplaxMonoidal.η (L((g₁₂)^*[A])) := rfl
    rw [e₁, e₂, e₁₂] at hu
    rw [← cancel_mono ((L((g₁)^*[A])).map (Functor.OplaxMonoidal.η (L((g₂)^*[A]))) ≫
      Functor.OplaxMonoidal.η (L((g₁)^*[A]))), Category.assoc, hu, Functor.Monoidal.ε_η,
      Functor.LaxMonoidal.comp_ε, Category.assoc, ← Functor.map_comp_assoc,
      Functor.Monoidal.ε_η, CategoryTheory.Functor.map_id, Category.id_comp,
      Functor.Monoidal.ε_η]
  · intro K M
    have h := leftDerivedUpperStarTensorComparison_comp_assoc A g₁ g₂ g₁₂ hg K M
      (Functor.LaxMonoidal.μ (L((g₂)^*[A]) ⋙ L((g₁)^*[A])) K M)
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (L((g₁₂)^*[A])) K M), Functor.Monoidal.δ_μ_assoc]
    erw [h]
    have e₁ : ∀ X Y, ((leftDerivedUpperStarTensorComparison A g₁).app X).app Y =
        Functor.OplaxMonoidal.δ (L((g₁)^*[A])) X Y := fun _ _ ↦ rfl
    have e₂ : ∀ X Y, ((leftDerivedUpperStarTensorComparison A g₂).app X).app Y =
        Functor.OplaxMonoidal.δ (L((g₂)^*[A])) X Y := fun _ _ ↦ rfl
    rw [e₁, e₂, Functor.LaxMonoidal.comp_μ, Functor.Monoidal.δ_μ_assoc, ← Functor.map_comp,
      Functor.Monoidal.δ_μ]
    simp

include hg in
/-- **The internal-hom comparison and composition.** For `g₁₂ = g₁ ≫ g₂`, the comparison of
`L(g₁₂)^*` at `(K, M)` is an isomorphism if and only if the composite
`Lg₁^* Lg₂^* RHom(K, M) ⟶ Lg₁^* RHom(Lg₂^* K, Lg₂^* M) ⟶ RHom(Lg₁^* Lg₂^* K, Lg₁^* Lg₂^* M)`
of the comparisons of `Lg₂^*` and of `Lg₁^*` is one. -/
lemma isIso_derivedHomUpperStarComparison_iff_comp
    (K M : _root_.DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    IsIso (derivedHomUpperStarComparison A g₁₂ K M) ↔
      IsIso ((L((g₁)^*[A])).map (derivedHomUpperStarComparison A g₂ K M) ≫
        derivedHomUpperStarComparison A g₁ ((L((g₂)^*[A])).obj K) ((L((g₂)^*[A])).obj M)) := by
  let := leftDerivedUpperStarMonoidal A g₁
  let := leftDerivedUpperStarMonoidal A g₂
  let := leftDerivedUpperStarMonoidal A g₁₂
  have := isMonoidal_leftDerivedUpperStarComp_hom A g₁ g₂ g₁₂ hg
  have h₁ := Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg) K M
  rw [Functor.LaxMonoidal.ihomComparison_comp_app] at h₁
  exact h₁

end Composition

end Etale

end AlgebraicGeometry
