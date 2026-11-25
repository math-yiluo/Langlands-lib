/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-!
# The direct-image finiteness input and the open-complement condition

This file records two finiteness conditions on étale direct images, and proves that they hold
for schemes of finite type over a field.

* The *direct-image finiteness input over `k`*
  (`AlgebraicGeometry.Etale.DirectImageFinitenessInput`,
  blueprint `theorem-results-from-etale-theory`): higher direct images of constructible sheaves
  along morphisms of finite-type `k`-schemes are constructible, and a finite-type scheme of
  dimension `≤ d` over a separably closed field has torsion cohomological dimension `≤ 2d`. It holds
  over every separably closed field (`AlgebraicGeometry.Etale.directImageFinitenessInput`, blueprint
  `theorem-results-from-etale-theory`).
* The *open-complement condition with constant `c`* for a morphism `j : V ⟶ T`
  (`AlgebraicGeometry.Etale.OpenComplementCondition`, blueprint
  `theorem-f-shriek-finite-coefficients--1`): `R^q j_*` vanishes above `c` and preserves
  constructibility. For a quasi-compact open immersion into a scheme of finite type and of dimension
  `≤ d` over a field it holds with `c = 2d`
  (`AlgebraicGeometry.Etale.openComplementCondition_two_mul`, blueprint
  `theorem-f-shriek-finite-coefficients--1`).

The open-complement condition is what the closed-support statements need from the open
complement of a closed immersion; for curves the sharper constant `c = 1` is
`AlgebraicGeometry.Etale.openComplementCondition_one` in
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CurveOpenDirectImage`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `theorem-results-from-etale-theory`: The classical direct-image finiteness input.

Let `k` be a field and `Λ` a coefficient ring. The *direct-image finiteness input over `k`* holds
if

1. (*finiteness of the direct image*) for every morphism `u : S ⟶ T` between finite-type
   `k`-schemes (such a morphism is of finite type), every constructible sheaf `F` of `Λ`-modules
   on `S_ét` and every `q ≥ 0`, the higher direct image `R^q u_* F` is constructible on `T_ét`;
2. (*cohomological dimension*) for every separably closed field `K` on which the exponent of `Λ`
   is invertible and every finite-type `K`-scheme `W` of dimension at most `d`, `H^q(W, M) = 0`
   for every `q > 2d` and every torsion abelian sheaf `M` on `W_ét`.

In the blueprint `Λ` is a finite ring annihilated by an integer `N` prime to the characteristic
of `k`; in clause (2) the condition that the characteristic of `K` is prime to `N` is the
invertibility of the exponent of `Λ` on `Spec K`. -/
def DirectImageFinitenessInput (k : Type u) [Field k] : Prop :=
  (∀ (S T : Scheme.{u}) (aS : S ⟶ Spec (.of k)) (aT : T ⟶ Spec (.of k))
      [LocallyOfFiniteType aS] [QuasiCompact aS] [LocallyOfFiniteType aT] [QuasiCompact aT]
      (u : S ⟶ T), u ≫ aT = aS → ∀ (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsConstructibleSheaf F → ∀ q : ℕ, IsConstructibleSheaf (higherDirectImage Λ u q F)) ∧
    ∀ (K : Type u) [Field K] [IsSepClosed K], HasInvertibleExponent Λ (Spec (.of K)) →
      ∀ (d : ℕ) (W : Scheme.{u}) (a : W ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a],
      topologicalKrullDim W ≤ (d : WithBot ℕ∞) →
      ∀ (M : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}), M.IsTorsion →
      ∀ q : ℕ, 2 * d < q → Subsingleton (Sheaf.H M q)

/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: Open-complement cohomological-dimension
condition.

Let `j : V ⟶ T` be a morphism (in the blueprint: a quasi-compact open immersion), `Λ` a
coefficient ring (in the blueprint: a finite ring) and `c ∈ ℕ`. The pair `(V, T)` satisfies the
*open-complement condition with constant `c`* if `R^q j_* M = 0` for every sheaf `M` of
`Λ`-modules on `V_ét` and every `q > c`, and if `R^q j_*` carries constructible sheaves to
constructible sheaves in every degree. -/
def OpenComplementCondition {V T : Scheme.{u}} (j : V ⟶ T) (c : ℕ) : Prop :=
  (∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M)) ∧
    ∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)), IsConstructibleSheaf F →
      ∀ q : ℕ, IsConstructibleSheaf (higherDirectImage Λ j q F)

variable {Λ}

/-- The vanishing of the higher direct images `R^q j_* M = 0` for `q > c`, read on the derived
functors of `j_*`. -/
lemma isZero_rightDerived_lowerStar_of_isZero_higherDirectImage {V T : Scheme.{u}} {j : V ⟶ T}
    {c : ℕ} (h : ∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M))
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (hq : c < q) :
    IsZero (((j)_*[ModuleCat.{u + 1} Λ].rightDerived q).obj M) :=
  (h M q hq).of_iso
    ((((j)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso M q).symm ≪≫
      homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ j M q)

/-- If `R^q j_* M = 0` for every sheaf `M` and every `q > c` (the vanishing clause of the
open-complement condition), the derived direct image `Rj_*` sends `D^{≤ n}` into
`D^{≤ n + c}`. -/
lemma isLE_rightDerivedLowerStar_obj_of_isZero_higherDirectImage {V T : Scheme.{u}}
    {j : V ⟶ T} {c : ℕ} (h : ∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ),
      c < q → IsZero (higherDirectImage Λ j q M))
    (K : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsLE n] : ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K).IsLE (n + c) :=
  ((j)_*[ModuleCat.{u + 1} Λ]).isLE_rightDerivedFunctor_obj c
    (fun M q hq ↦ isZero_rightDerived_lowerStar_of_isZero_higherDirectImage h M q hq) K n

/-- Under the constructibility clause of the open-complement condition, every homology sheaf of
`Rj_* F`, for `F` constructible, is constructible. -/
lemma OpenComplementCondition.isConstructibleSheaf_homology {V T : Scheme.{u}} {j : V ⟶ T}
    {c : ℕ} (h : OpenComplementCondition Λ j c)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] (q : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  obtain hq | hq := lt_or_ge q 0
  · have : ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).IsGE 0 :=
      isGE_rightDerivedLowerStar_obj Λ j _ 0
    exact IsConstructibleSheaf.of_isZero (_root_.DerivedCategory.isZero_of_isGE _ 0 q hq)
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    have := h.2 F inferInstance n
    exact IsConstructibleSheaf.of_iso
      (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ j F n).symm

variable [Finite Λ]

/-- The higher direct images of a constructible sheaf along a morphism of finite-type schemes
over a field are constructible, if the exponent of `Λ` is invertible on the field. This is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType`
(blueprint `proposition-six-operations-dctf--2`) for the sheaf placed in degree `0`. -/
theorem isConstructibleSheaf_higherDirectImage {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {S T : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] [LocallyOfFiniteType aT]
    [QuasiCompact aT] (u : S ⟶ T) (hu : u ≫ aT = aS)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] (q : ℕ) :
    IsConstructibleSheaf (higherDirectImage Λ u q F) :=
  have := (boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType Λ u aS aT hu _
    (DerivedCategory.boundedConstructible_singleFunctor_obj F 0)).2 q
  IsConstructibleSheaf.of_iso (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ u F q)

/-- Blueprint `theorem-results-from-etale-theory`: The direct-image finiteness input holds.

Let `k` be a separably closed field and `Λ` a finite ring whose exponent is invertible in `k`.
Then both clauses of the direct-image finiteness input
(`AlgebraicGeometry.Etale.DirectImageFinitenessInput`) hold over `k`. Clause (1) is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType`
(`proposition-six-operations-dctf--2`), through
`AlgebraicGeometry.Etale.isConstructibleSheaf_higherDirectImage`; clause (2) is
`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`, the bound
`cd_tor(W) ≤ 2d + 0` of `lemma-uniform-bounds-pro-etale-affines` for the separably closed field `K`
(`lemma-cohomological-dimension-base-field--1`). Separable closedness of `k` is not needed for
clause (1). -/
theorem directImageFinitenessInput (k : Type u) [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] : DirectImageFinitenessInput Λ k :=
  ⟨fun _ _ aS aT _ _ _ _ u hu F _ q ↦ isConstructibleSheaf_higherDirectImage aS aT u hu F q,
    fun _ _ _ _ d _ a _ _ hW M hM q hq ↦
      Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed d a hW M hM q hq⟩

/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: The open-complement condition from the
direct-image input.

Let `k` be a field, `T` a `k`-scheme of finite type and of dimension at most `d`,
`j : V ⟶ T` a quasi-compact open immersion and `Λ` a finite ring whose exponent is invertible in
`k`. Then `(V, T)` satisfies the open-complement condition with constant `c = 2d`
(`AlgebraicGeometry.Etale.OpenComplementCondition`). The blueprint takes for `k` the algebraic
closure of a finite field and `Λ` killed by a power of a prime `ℓ ≠ char k`.

The constructibility clause is clause (1) of the direct-image finiteness input
(`AlgebraicGeometry.Etale.isConstructibleSheaf_higherDirectImage`, `thm-dg-finite-type-
constructibility`). For the vanishing clause, `V` is of finite type over `k` of dimension at most
`d`, so `R^q j_* M = 0` for `q > 2d` by
`AlgebraicGeometry.Etale.isZero_rightDerived_lowerStar_of_two_mul_lt`; over a separably closed
field this is the stalkwise argument of the blueprint, through the cohomological dimension
bound `lemma-uniform-bounds-pro-etale-affines` on the étale `V`-schemes.

This is also the content of blueprint `rem-pur-assembly-status` (status of the assembly): the
open-complement condition (`theorem-f-shriek-finite-coefficients--1`) is a theorem, not an
assumption, and its constant `2d` does not depend on `Λ`. The remaining claims of that remark
concern the general admissibility theorems `theorem-f-shriek-finite-coefficients` and
`theorem-f-shriek-finite-coefficients--1`, which are not formalised; for closed immersions see
`AlgebraicGeometry.Etale.isLeftAdjoint_and_constructibleIn_and_torAmplitudeIn_of_isClosedImmersion`.
-/
theorem openComplementCondition_two_mul {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {V T : Scheme.{u}} (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (d : ℕ) (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) :
    OpenComplementCondition Λ j (2 * d) := by
  have hV : topologicalKrullDim V ≤ (d : WithBot ℕ∞) := j.topologicalKrullDim_le_of_etale.trans hT
  refine ⟨fun M q hq ↦ ?_, fun F _ q ↦ isConstructibleSheaf_higherDirectImage (j ≫ aT) aT j rfl F q⟩
  exact (isZero_rightDerived_lowerStar_of_two_mul_lt Λ isAddTorsion_of_finite (j ≫ aT) aT j rfl
    d hV M q hq).of_iso
    ((((j)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso M q).symm ≪≫
      homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ j M q).symm

end Etale

end AlgebraicGeometry
