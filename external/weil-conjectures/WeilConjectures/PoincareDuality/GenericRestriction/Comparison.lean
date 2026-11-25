/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
public import WeilConjectures.PoincareDuality.ProperProjectionComp
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom

/-!
# The internal-hom comparison of a derived pullback: formal properties

Let `Λ` be a commutative condensed ring. For a morphism of schemes `g : Z' ⟶ Z`, the derived
pullback `Lg^*` on the derived categories of module objects over `Λ` is monoidal, so it has a
comparison map
`ρ_g(K, M) : Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`). This file collects the formal properties of
`ρ` used to prove that it is an isomorphism for a change of the base field and for the pullback to
a geometric generic fibre (blueprint `lemma-restriction-geometric-generic-fibre` (2)):

* `ρ` is compatible with composition: the composition isomorphism
  `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` is monoidal
  (`ProEtale.CondensedRing.isMonoidal_leftDerivedUpperStarComp_hom`), so `ρ_{f ≫ g}` is invertible
  as soon as `ρ_g` and `ρ_f` are
  (`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_comp`);
* `ρ` is invertible at `(K, Rf_* N)` for a morphism `f` with fully faithful `Rf_*` (an open or a
  closed immersion), as soon as `Rf_*` commutes with the base change along `g` at `N` and at
  `RHom(Lf^* K, N)` and `ρ` of the base change of `g` is invertible at `(Lf^* K, N)`
  (`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_rightDerivedLowerStar_of_isPullback`);
* **dévissage in the second variable**: for an open immersion `j` with closed complement `i`,
  `ρ_g` is invertible at `(K, M)` as soon as it is at `(K, Rj_* Lj^* M)` and at the objects
  `(K, Ri_* X)`, `X` bounded constructible, and `Rj_*` commutes with the base change along `g` at
  `Lj^* M`
  (`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_isIso_open_closed`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor.LaxMonoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The comparison `ρ_g(K, M) : Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)` of the monoidal functor
`Lg^*` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), on the derived categories of module
objects over `Λ`. It is the transpose of
`Lg^* K ⊗ᴸ Lg^* RHom(K, M) ≅ Lg^*(K ⊗ᴸ RHom(K, M)) ⟶ Lg^* M`,
hence compatible with evaluation. -/
noncomputable def ihomUpperStarComparison {W X : Scheme.{u}} (g : W ⟶ X)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (L((g)^*⟦Λ⟧)).obj ((ihom K).obj M) ⟶
      (ihom ((L((g)^*⟦Λ⟧)).obj K)).obj ((L((g)^*⟦Λ⟧)).obj M) :=
  (ihomComparison L((g)^*⟦Λ⟧) K).app M

lemma ihomUpperStarComparison_eq {W X : Scheme.{u}} (g : W ⟶ X)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ihomUpperStarComparison Λ g K M = (ihomComparison L((g)^*⟦Λ⟧) K).app M :=
  rfl

/-- The comparison `ρ_g(K, M)` is natural in `M`. -/
@[reassoc]
lemma ihomUpperStarComparison_naturality {W X : Scheme.{u}} (g : W ⟶ X)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {M M' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (φ : M ⟶ M') :
    (L((g)^*⟦Λ⟧)).map ((ihom K).map φ) ≫ ihomUpperStarComparison Λ g K M' =
      ihomUpperStarComparison Λ g K M ≫ (ihom ((L((g)^*⟦Λ⟧)).obj K)).map ((L((g)^*⟦Λ⟧)).map φ) :=
  (ihomComparison L((g)^*⟦Λ⟧) K).naturality φ

/-- The comparison `ρ_g(K, M)` is an isomorphism if and only if `ρ_g(K, M')` is, for `M ≅ M'`. -/
lemma isIso_ihomUpperStarComparison_iff_of_iso_right {W X : Scheme.{u}} (g : W ⟶ X)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {M M' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (e : M ≅ M') :
    IsIso (ihomUpperStarComparison Λ g K M) ↔ IsIso (ihomUpperStarComparison Λ g K M') :=
  NatTrans.isIso_app_iff_of_iso _ e

/-- The comparison of a weakly étale morphism (for instance an open immersion, or the inclusion of
the generic point of an integral scheme) is an isomorphism
(`ProEtale.CondensedRing.isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale`). -/
instance isIso_ihomUpperStarComparison_of_weaklyEtale {W X : Scheme.{u}} (g : W ⟶ X)
    [WeaklyEtale g]
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (ihomUpperStarComparison Λ g K M) := by
  have := isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale Λ g K
  rw [ihomUpperStarComparison_eq]
  infer_instance

/-- The comparison of `Lf^*` at `(K, Rf_* N)` is an isomorphism when the counit of `Lf^* ⊣ Rf_*`
is invertible (`Rf_*` fully faithful, e.g. for an open or a closed immersion):
`CategoryTheory.Functor.Monoidal.isIso_ihomComparison_app_rightAdjoint`. -/
lemma isIso_ihomUpperStarComparison_rightDerivedLowerStar {V Z : Scheme.{u}} (f : V ⟶ Z)
    [IsIso (derivedUpperStarLowerStarAdjunction Λ f).counit]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))) :
    IsIso (ihomUpperStarComparison Λ f K ((R((f)_*⟦Λ⟧)).obj N)) :=
  Functor.Monoidal.isIso_ihomComparison_app_rightAdjoint
    (derivedUpperStarLowerStarAdjunction Λ f) K N

/-- If `K` has a left dual, the comparison `ρ_g(K, M)` is an isomorphism for every `M`
(`CategoryTheory.Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing`). -/
lemma isIso_ihomUpperStarComparison_of_exactPairing {W X : Scheme.{u}} (g : W ⟶ X)
    (D K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) [ExactPairing D K]
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (ihomUpperStarComparison Λ g K M) :=
  Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing L((g)^*⟦Λ⟧) D K M

section Composition

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of the derived pullbacks is a monoidal
natural transformation (`ProEtale.CondensedRing.leftDerivedUpperStarComp_δ`,
`ProEtale.CondensedRing.leftDerivedUpperStarComp_hom_app_unit`). -/
instance isMonoidal_leftDerivedUpperStarComp_hom :
    NatTrans.IsMonoidal (leftDerivedUpperStarComp Λ f g).hom :=
  NatTrans.IsMonoidal.of_isIso_of_δ _ fun X Y ↦ (leftDerivedUpperStarComp_δ Λ f g X Y).symm

/-- **The internal-hom comparison and composition.** The comparison of `L(f ≫ g)^*` at `(K, M)` is
an isomorphism if and only if the composite of `Lf^*` of the comparison of `Lg^*` and of the
comparison of `Lf^*` at `(Lg^* K, Lg^* M)` is one. Up to the composition isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, the comparison `ρ_{f ≫ g}(K, M)` is the composite
```
L(f ≫ g)^* RHom(K, M) ≅ Lf^* Lg^* RHom(K, M)
  ⟶ Lf^* RHom(Lg^* K, Lg^* M)                  (Lf^* ρ_g(K, M))
  ⟶ RHom(Lf^* Lg^* K, Lf^* Lg^* M)             (ρ_f(Lg^* K, Lg^* M))
  ≅ RHom(L(f ≫ g)^* K, L(f ≫ g)^* M).
``` -/
lemma isIso_ihomUpperStarComparison_comp_iff
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    IsIso (ihomUpperStarComparison Λ (f ≫ g) K M) ↔
      IsIso ((L((f)^*⟦Λ⟧)).map (ihomUpperStarComparison Λ g K M) ≫
        ihomUpperStarComparison Λ f ((L((g)^*⟦Λ⟧)).obj K) ((L((g)^*⟦Λ⟧)).obj M)) := by
  have h := Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso
    (leftDerivedUpperStarComp Λ f g) K M
  rw [Functor.LaxMonoidal.ihomComparison_comp_app] at h
  exact h

/-- `ProEtale.CondensedRing.isIso_ihomUpperStarComparison_comp_iff` for a morphism
`h` equal to `f ≫ g`. -/
lemma isIso_ihomUpperStarComparison_comp_iff_of_eq {h : X ⟶ Z} (hfg : f ≫ g = h)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    IsIso (ihomUpperStarComparison Λ h K M) ↔
      IsIso ((L((f)^*⟦Λ⟧)).map (ihomUpperStarComparison Λ g K M) ≫
        ihomUpperStarComparison Λ f ((L((g)^*⟦Λ⟧)).obj K) ((L((g)^*⟦Λ⟧)).obj M)) := by
  subst hfg
  exact isIso_ihomUpperStarComparison_comp_iff Λ f g K M

/-- If the comparisons of `Lg^*` at `(K, M)` and of `Lf^*` at `(Lg^* K, Lg^* M)` are isomorphisms,
so is the comparison of `L(f ≫ g)^*` at `(K, M)`. -/
lemma isIso_ihomUpperStarComparison_comp
    {K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))}
    (hg : IsIso (ihomUpperStarComparison Λ g K M))
    (hf : IsIso (ihomUpperStarComparison Λ f ((L((g)^*⟦Λ⟧)).obj K) ((L((g)^*⟦Λ⟧)).obj M))) :
    IsIso (ihomUpperStarComparison Λ (f ≫ g) K M) := by
  rw [isIso_ihomUpperStarComparison_comp_iff]
  infer_instance

/-- If the comparisons of `L(f ≫ g)^*` and of `Lg^*` at `(K, M)` are isomorphisms, so is the
comparison of `Lf^*` at `(Lg^* K, Lg^* M)`. -/
lemma isIso_ihomUpperStarComparison_of_comp
    {K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))}
    (hfg : IsIso (ihomUpperStarComparison Λ (f ≫ g) K M))
    (hg : IsIso (ihomUpperStarComparison Λ g K M)) :
    IsIso (ihomUpperStarComparison Λ f ((L((g)^*⟦Λ⟧)).obj K) ((L((g)^*⟦Λ⟧)).obj M)) := by
  rw [isIso_ihomUpperStarComparison_comp_iff] at hfg
  exact IsIso.of_isIso_comp_left ((L((f)^*⟦Λ⟧)).map (ihomUpperStarComparison Λ g K M)) _

end Composition

section DirectImage

variable {Z Z' V V' : Scheme.{u}} {gZ : Z' ⟶ Z} {f : V ⟶ Z} {f' : V' ⟶ Z'} {gV : V' ⟶ V}
  (sq : IsPullback gV f' f gZ)

/-- **The comparison on direct images.** Let `f : V ⟶ Z` be a morphism with fully faithful `Rf_*`
(an open or a closed immersion), `f' : V' ⟶ Z'` its base change along `gZ : Z' ⟶ Z`, again with
fully faithful `Rf'_*`. If `Rf_*` commutes with the base change at `N` and at `RHom(Lf^* K, N)`,
and the comparison of the base change `gV : V' ⟶ V` is an isomorphism at `(Lf^* K, N)`, then the
comparison of `gZ` is an isomorphism at `(K, Rf_* N)`: both sides are direct images along `f'`,
and after `Lf'^*` the comparison is that of `gV` (composition with the comparisons of `f`, `f'`,
which are isomorphisms on direct images). -/
lemma isIso_ihomUpperStarComparison_rightDerivedLowerStar_of_isPullback
    [IsIso (derivedUpperStarLowerStarAdjunction Λ f).counit]
    [IsIso (derivedUpperStarLowerStarAdjunction Λ f').counit]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V)))
    (hN : IsIso ((baseChangeMap Λ sq.toCommSq).app N))
    (hH : IsIso ((baseChangeMap Λ sq.toCommSq).app ((ihom ((L((f)^*⟦Λ⟧)).obj K)).obj N)))
    (hρ : IsIso (ihomUpperStarComparison Λ gV ((L((f)^*⟦Λ⟧)).obj K) N)) :
    IsIso (ihomUpperStarComparison Λ gZ K ((R((f)_*⟦Λ⟧)).obj N)) := by
  let eA := (L((gZ)^*⟦Λ⟧)).mapIso (ihomRightDerivedLowerStarIso Λ f K N) ≪≫
    asIso ((baseChangeMap Λ sq.toCommSq).app ((ihom ((L((f)^*⟦Λ⟧)).obj K)).obj N))
  let eB := (ihom ((L((gZ)^*⟦Λ⟧)).obj K)).mapIso (asIso ((baseChangeMap Λ sq.toCommSq).app N)) ≪≫
    ihomRightDerivedLowerStarIso Λ f' _ _
  have hρf' : IsIso (ihomUpperStarComparison Λ f' ((L((gZ)^*⟦Λ⟧)).obj K)
      ((L((gZ)^*⟦Λ⟧)).obj ((R((f)_*⟦Λ⟧)).obj N))) :=
    (isIso_ihomUpperStarComparison_iff_of_iso_right Λ f' ((L((gZ)^*⟦Λ⟧)).obj K)
      (asIso ((baseChangeMap Λ sq.toCommSq).app N))).2
      (isIso_ihomUpperStarComparison_rightDerivedLowerStar Λ f' _ _)
  have h₁ := isIso_ihomUpperStarComparison_rightDerivedLowerStar Λ f K N
  have h₂ := (isIso_ihomUpperStarComparison_iff_of_iso_right Λ gV ((L((f)^*⟦Λ⟧)).obj K)
    (asIso ((derivedUpperStarLowerStarAdjunction Λ f).counit.app N))).2 hρ
  have hρh := (isIso_ihomUpperStarComparison_comp_iff_of_eq Λ gV f sq.w K
    ((R((f)_*⟦Λ⟧)).obj N)).2 (IsIso.comp_isIso' (Functor.map_isIso _ _) h₂)
  rw [isIso_ihomUpperStarComparison_comp_iff] at hρh
  have h₃ := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hρf' hρh
  exact (derivedUpperStarLowerStarAdjunction Λ f').isIso_of_isIso_map_of_iso_rightAdjoint_obj
    eA eB _

end DirectImage

section Devissage

variable {Z Z' U U' W : Scheme.{u}} {gZ : Z' ⟶ Z} {i : W ⟶ Z} [IsClosedImmersion i]
  {j : U ⟶ Z} [IsOpenImmersion j] {j' : U' ⟶ Z'} [IsOpenImmersion j'] {gU : U' ⟶ U}

omit [IsOpenImmersion j'] in
/-- **Dévissage in the second variable.** Let `j : U ⟶ Z` be a quasi-compact open immersion with
closed complement `i : W ⟶ Z` and `j'` its base change along `gZ : Z' ⟶ Z`, such that `Rj_*`
commutes with the base change at `Lj^* M`. If the comparison of `gZ` is an isomorphism at
`(K, Rj_* Lj^* M)` and at every `(K, Ri_* X)` with `X` bounded constructible, then it is one at
`(K, M)`, for bounded constructible `M` with `Rj_* Lj^* M` bounded constructible. Complete the
unit `M ⟶ Rj_* Lj^* M` to a distinguished triangle `M ⟶ Rj_* Lj^* M ⟶ C ⟶ M[1]`: `C` is killed
by `Lj^*`, so `C ≅ Ri_* Li^* C` (the restrictions to `U` and `W` jointly detect isomorphisms, `j`
being quasi-compact), and the five lemma without connecting morphisms
(`CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃_of_subsingleton`) applies to the images of the
rotated triangle `C[-1] ⟶ M ⟶ Rj_* Lj^* M ⟶ C` under both sides of the comparison: there are no
maps from `Lg^* RHom(K, C)` to `RHom(Lg^* K, Rj'_* -)` since `Lj'^*` kills the former.
Writing `A(-) = Lg^* RHom(K, -)` and `B(-) = RHom(Lg^* K, Lg^* -)`, the diagram is
```
A(C[-1]) ⟶ A(M) ⟶ A(Rj_* Lj^* M) ⟶ A(C)
   │≅        │        │≅              │
   ↓         ↓ ρ      ↓               ↓
B(C[-1]) ⟶ B(M) ⟶ B(Rj_* Lj^* M) ⟶ B(C)
```
with `B(Rj_* Lj^* M) ≅ RHom(Lg^* K, Rj'_* Lg_U^* Lj^* M)`. -/
lemma isIso_ihomUpperStarComparison_of_isIso_open_closed [QuasiCompact j]
    [(boundedConstructible (condensedRingObj Λ Z)).IsTriangulated]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (sqU : IsPullback gU j' j gZ)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hM : boundedConstructible (condensedRingObj Λ Z) M)
    (hjM : boundedConstructible (condensedRingObj Λ Z) ((R((j)_*⟦Λ⟧)).obj ((L((j)^*⟦Λ⟧)).obj M)))
    (hbc : IsIso ((baseChangeMap Λ sqU.toCommSq).app ((L((j)^*⟦Λ⟧)).obj M)))
    (hU : IsIso (ihomUpperStarComparison Λ gZ K ((R((j)_*⟦Λ⟧)).obj ((L((j)^*⟦Λ⟧)).obj M))))
    (hW : ∀ X : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj Λ W)), boundedConstructible (condensedRingObj Λ W) X →
      IsIso (ihomUpperStarComparison Λ gZ K ((R((i)_*⟦Λ⟧)).obj X))) :
    IsIso (ihomUpperStarComparison Λ gZ K M) := by
  -- Reuse the derived monoidal structures throughout the internal-hom comparisons.
  let (X : Scheme.{u}) : MonoidalCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := inferInstance
  let (X : Scheme.{u}) : MonoidalClosed (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := inferInstance
  -- Elaborate the K-flat tensor instances once, uniformly in the pullback morphism.
  let pullback {X Y : Scheme.{u}} (f : X ⟶ Y) := L((f)^*⟦Λ⟧)
  let gStar := pullback gZ
  let jStar := pullback j
  let jStar' := pullback j'
  let gUStar := pullback gU
  let jPush := R((j)_*⟦Λ⟧)
  -- the triangle `M ⟶ Rj_* Lj^* M ⟶ C ⟶ M[1]`
  obtain ⟨C, v', w, hT⟩ := distinguished_cocone_triangle
    ((derivedUpperStarLowerStarAdjunction Λ j).unit.app M)
  have hC : boundedConstructible (condensedRingObj Λ Z) C :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT hM hjM
  -- `C` is supported on `W`
  have hjC : IsZero (jStar.obj C) := by
    have h₁ : IsIso (jStar.map
        ((derivedUpperStarLowerStarAdjunction Λ j).unit.app M)) :=
      IsIso.of_isIso_fac_right (hh := IsIso.id _)
        ((derivedUpperStarLowerStarAdjunction Λ j).left_triangle_components M)
    exact (Triangle.isZero₃_iff_isIso₁ _ (jStar.map_distinguished _ hT)).2 h₁
  have hjC' : IsZero (jStar.obj (C⟦(-1 : ℤ)⟧)) :=
    ((shiftFunctor _ (-1 : ℤ)).map_isZero hjC).of_iso
      ((jStar.commShiftIso (-1 : ℤ)).app C)
  have hu := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ j i hij hjC'
  have hC' : boundedConstructible (condensedRingObj Λ Z) (C⟦(-1 : ℤ)⟧) :=
    (boundedConstructible _).le_shift (-1 : ℤ) C hC
  have hφ₁ : IsIso (ihomUpperStarComparison Λ gZ K (C⟦(-1 : ℤ)⟧)) :=
    (isIso_ihomUpperStarComparison_iff_of_iso_right Λ gZ K
      (asIso ((derivedUpperStarLowerStarAdjunction Λ i).unit.app (C⟦(-1 : ℤ)⟧)))).2
      (hW _ (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ i _ hC'))
  -- the images of the rotated triangle `C[-1] ⟶ M ⟶ Rj_* Lj^* M ⟶ C`
  have hT' := inv_rot_of_distTriang _ hT
  let adj : (curriedTensor _).obj K ⊣ ihom K := ihom.adjunction K
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have : (ihom K).IsTriangulated := adj.isTriangulated_rightAdjoint
  let adj' : (curriedTensor _).obj (gStar.obj K) ⊣ ihom (gStar.obj K) :=
    ihom.adjunction _
  let := adj'.rightAdjointCommShift ℤ
  have := adj'.commShift_of_leftAdjoint ℤ
  have : (ihom (gStar.obj K)).IsTriangulated := adj'.isTriangulated_rightAdjoint
  have hT₁ := gStar.map_distinguished _ ((ihom K).map_distinguished _ hT')
  have hT₂ := (ihom (gStar.obj K)).map_distinguished _
    (gStar.map_distinguished _ hT')
  refine @Pretriangulated.isIso₂_of_isIso₁₃_of_subsingleton _ _ _ _ _ _ _ _ _ hT₁ hT₂ _ _
    (ihomUpperStarComparison Λ gZ K (jPush.obj (jStar.obj M)))
    (ihomUpperStarComparison_naturality Λ gZ K _)
    (ihomUpperStarComparison_naturality Λ gZ K _) ?_ hφ₁ hU
  -- the third term is `Rj'_*` of an object, and `Lj'^*` kills the first one
  let ebc := @asIso _ _ _ _ _ hbc
  let eB := (ihom (gStar.obj K)).mapIso ebc ≪≫ ihomRightDerivedLowerStarIso Λ j' _ _
  have hz₀ : IsZero (jStar.obj ((ihom K).obj (C⟦(-1 : ℤ)⟧))) :=
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint Λ j i
      hij.symm.disjoint _).of_iso (jStar.mapIso ((ihom K).mapIso
        (asIso ((derivedUpperStarLowerStarAdjunction Λ i).unit.app (C⟦(-1 : ℤ)⟧))) ≪≫
          ihomRightDerivedLowerStarIso Λ i K _))
  have hz : IsZero (jStar'.obj (gStar.obj ((ihom K).obj (C⟦(-1 : ℤ)⟧)))) :=
    (gUStar.map_isZero hz₀).of_iso
      ((pullbackSquareComparison Λ sqU.toCommSq).app _)
  exact (derivedUpperStarLowerStarAdjunction Λ j').subsingleton_hom_of_isZero_leftAdjoint eB
    (((shiftFunctor _ (1 : ℤ)).map_isZero hz).of_iso
      ((jStar'.commShiftIso (1 : ℤ)).app _))

end Devissage

end AlgebraicGeometry.ProEtale.CondensedRing
