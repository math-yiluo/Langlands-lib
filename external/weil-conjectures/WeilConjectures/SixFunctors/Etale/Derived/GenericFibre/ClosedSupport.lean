/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# Closed exceptional inverse images commute with generic base change

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`, and let `g : X' ⟶ X` be a
morphism with base changes `i' : Z' ⟶ X'`, `j' : U' ⟶ X'`, `g_Z : Z' ⟶ Z`, `g_U : U' ⟶ U`. The
canonical base change map of the exceptional inverse image

`β_M : g_Z^* Ri^! M ⟶ Ri'^! g^* M`

(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`, the mate of the inverse of the
compact-support base change isomorphism `Ex_!`) is an isomorphism as soon as the derived base
change map `Ex_* : g^* Rj_* j^* M ⟶ Rj'_* g_U^* j^* M` is one
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso`). Over the
generic point of an integral base this applies to every bounded constructible `M`, by
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic`: this is
the second comparison `g_Z^* Ri^! M ≅ Ri_{η̄}^! g_X^* M` of blueprint
`lemma-restriction-geometric-generic-fibre`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_generic`).

## Proof

As in the blueprint, pull back the supported localization triangle
`i_! Ri^! M ⟶ M ⟶ Rj_* j^* M ⟶` (`AlgebraicGeometry.Etale.supportedLocalizationTriangle`) along
`g`. Its first term is `g^* i_! Ri^! M ≅ i'_! g_Z^* Ri^! M` by compact-support base change, and
its third term `g^* Rj_* j^* M ≅ Rj'_* g_U^* j^* M` receives no maps from objects `i'_! Q[n]`
(`AlgebraicGeometry.Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`).
Since `i'_!` is fully faithful
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`), the transpose
of the first map, which is `β_M` by the mate calculus, is an isomorphism; this is the formal
statement `CategoryTheory.Pretriangulated.isIso_of_adjunction_triangle`. Only the
closed-support triangle is used, not boundary duality.

## Main statements

- `CategoryTheory.Pretriangulated.isIso_of_adjunction_triangle`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_generic`
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Let `L ⊣ R` be an adjunction with `L` fully faithful and target a pretriangulated category,
let `T` be a distinguished triangle whose first object is `L P` (via `e`) and whose third object
receives no nonzero maps from the objects `L Q` and `L Q⟦1⟧`. Then the transpose
`β : P ⟶ R T.obj₂` of `e.hom ≫ T.mor₁ : L P ⟶ T.obj₂` is an isomorphism: by the long exact
`Hom(L Q, -)`-sequence of `T`, composition with `T.mor₁` is bijective on maps out of `L Q`. -/
lemma isIso_of_adjunction_triangle {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Full] [L.Faithful]
    (T : Triangle D) (hT : T ∈ distTriang D) {P : C} (e : L.obj P ≅ T.obj₁)
    (h₀ : ∀ Q, Subsingleton (L.obj Q ⟶ T.obj₃))
    (h₁ : ∀ Q, Subsingleton (L.obj Q ⟶ T.obj₃⟦(-1 : ℤ)⟧))
    (β : P ⟶ R.obj T.obj₂) (hβ : L.map β ≫ adj.counit.app T.obj₂ = e.hom ≫ T.mor₁) :
    IsIso β := by
  refine isIso_of_yoneda_map_bijective β fun Q ↦ ?_
  have key : ∀ x : Q ⟶ P, (adj.homEquiv _ _).symm (x ≫ β) = L.map x ≫ e.hom ≫ T.mor₁ := by
    intro x
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, hβ]
  have hinj : Function.Injective (fun y : L.obj Q ⟶ T.obj₁ ↦ y ≫ T.mor₁) := by
    intro y₁ y₂ h
    rw [← sub_eq_zero]
    have h' : (y₁ - y₂) ≫ (Triangle.invRotate T).mor₂ = 0 := by
      simp only [Triangle.invRotate_mor₂, Preadditive.sub_comp]
      exact sub_eq_zero.2 h
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) _ h'
    have : z = 0 := (h₁ Q).elim _ _
    rw [hz, this, zero_comp]
  refine ⟨fun x₁ x₂ h ↦ ?_, fun y ↦ ?_⟩
  · have h' := congrArg (adj.homEquiv _ _).symm h
    simp only [key] at h'
    have h'' := hinj (a₁ := L.map x₁ ≫ e.hom) (a₂ := L.map x₂ ≫ e.hom) (by simpa using h')
    exact L.map_injective (by simpa using h'')
  · obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₂ T hT ((adj.homEquiv _ _).symm y)
      ((h₀ Q).elim _ _)
    obtain ⟨x, hx⟩ := L.map_surjective (z ≫ e.inv)
    refine ⟨x, (adj.homEquiv _ _).symm.injective ?_⟩
    simp only [key, hx, Category.assoc, Iso.inv_hom_id_assoc, hz]

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The base change map of a closed exceptional inverse image is invertible where the open
direct image commutes with base change. Let `i : Z ⟶ X` be a closed immersion with open
complement `j : U ⟶ X`, let `g : X' ⟶ X` be a morphism, and let `i'`, `j'` be the base changes
of `i`, `j` along `g` (with disjoint images). If the derived base change map
`Ex_* : g^* Rj_* j^* M ⟶ Rj'_* g_U^* j^* M` is an isomorphism, then so is the base change map
`β_M : g_Z^* Ri^! M ⟶ Ri'^! g^* M` of
`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`.

This is the closed-support step of blueprint `lemma-restriction-geometric-generic-fibre`: pull back
the supported localization triangle `i_! Ri^! M ⟶ M ⟶ Rj_* j^* M ⟶` along `g` and use that
`i'_!` is fully faithful (`CategoryTheory.Pretriangulated.isIso_of_adjunction_triangle`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso {X X' Z Z' U U' : Scheme.{u}}
    {g : X' ⟶ X} {i : Z ⟶ X} {i' : Z' ⟶ X'} {gZ : Z' ⟶ Z} [IsClosedImmersion i]
    [IsClosedImmersion i'] (sq : IsPullback gZ i' i g) {j : U ⟶ X} {j' : U' ⟶ X'} {gU : U' ⟶ U}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sqU : IsPullback gU j' j g)
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Disjoint (Set.range i'.base) (Set.range j'.base))
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqU.toCommSq).app
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M))) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app M) := by
  let adj := rightDerivedUpperShriekAdjunction Λ i'
  have : ∀ Q, IsIso (adj.unit.app Q) := fun Q ↦
    isIso_rightDerivedUpperShriekAdjunction_unit_app _ i' Q
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  have := adj.fullyFaithfulLOfIsIsoUnit.full
  have := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  obtain ⟨w, hw⟩ := (existsUnique_distTriang_supportedLocalization _ i j hij M).exists
  let T := (L((g)^*[ModuleCat.{u + 1} Λ])).mapTriangle.obj
    (supportedLocalizationTriangle _ i j M w)
  have hT : T ∈ distTriang _ := (L((g)^*[ModuleCat.{u + 1} Λ])).map_distinguished _ hw
  let e₃ : T.obj₃ ≅ (R((j')_*[ModuleCat.{u + 1} Λ])).obj
      ((L((gU)^*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M)) :=
    asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqU.toCommSq).app _)
  have hs : ∀ (Q : _root_.DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (n : ℤ), Subsingleton (((R(i')_![ModuleCat.{u + 1} Λ]).obj Q)⟦n⟧ ⟶ T.obj₃) := by
    intro Q n
    have := subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar _ i' j' hij'
      Q ((L((gU)^*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M)) n
    exact (Iso.homCongr (Iso.refl _) e₃).subsingleton
  refine isIso_of_adjunction_triangle adj T hT
    (asIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app _)).symm (fun Q ↦ ?_) (fun Q ↦ ?_)
    _ ?_
  · have := hs Q 0
    exact @Equiv.subsingleton _ _
      (Iso.homCongr ((shiftFunctorZero _ ℤ).app _).symm (Iso.refl _)) this
  · have := hs Q 1
    exact @Equiv.subsingleton _ _
      ((shiftEquiv _ (1 : ℤ)).toAdjunction.homEquiv _ _).symm this
  · have h := mateEquiv_counit (rightDerivedUpperShriekAdjunction _ i) adj
      (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)) M
    rw [NatIso.isIso_inv_app] at h
    exact h

/-- Blueprint `lemma-restriction-geometric-generic-fibre`, second comparison: closed exceptional
inverse images commute with generic base change.

Let `S` be integral and of finite type over a field `k`, let `Λ` be a finite ring whose exponent
is invertible on `S`, and let `t : T ⟶ S` be a morphism from a noetherian scheme lying over the
generic point of `S` (e.g. a geometric generic point `η̄`). Let `X` be of finite type over `S`
with base change `g : X_T ⟶ X`, let `i : Z ⟶ X` be a closed immersion with open complement
`j : U ⟶ X`, and let `i'`, `j'` be their base changes along `g`. Then for every bounded
constructible `M` on `X` the canonical base change map
`g_Z^* Ri^! M ⟶ Ri'^! g^* M` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`)
is an isomorphism: `j^* M` is bounded constructible, so the open direct image comparison
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic` applies,
and `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso`
concludes. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_of_generic {k : Type u} [Field k]
    {S : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] {T : Scheme.{u}} [IsNoetherian T] (t : T ⟶ S)
    (ht : ∀ x, t.base x = genericPoint S) {X X' Z Z' U U' : Scheme.{u}} (fX : X ⟶ S)
    [LocallyOfFiniteType fX] [QuasiCompact fX] {g : X' ⟶ X} {fT : X' ⟶ T}
    (hX : IsPullback g fT fX t) {i : Z ⟶ X} {i' : Z' ⟶ X'} {gZ : Z' ⟶ Z} [IsClosedImmersion i]
    [IsClosedImmersion i'] (sq : IsPullback gZ i' i g) {j : U ⟶ X} {j' : U' ⟶ X'} {gU : U' ⟶ U}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sqU : IsPullback gU j' j g)
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Disjoint (Set.range i'.base) (Set.range j'.base))
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app M) :=
  isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso Λ sq sqU hij hij' M
    (isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic Λ aS t ht fX j hX sqU
      (boundedConstructible_leftDerivedUpperStar _ j hM))

end Etale

end AlgebraicGeometry
