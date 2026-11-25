/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow

/-!
# The constructible exceptional unit along a closed immersion

For a closed immersion `i : Z ⟶ X` admitting a compactification, the pro-étale derived lower
shriek `Ri_!` is the right derived pushforward `Ri_*`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar`), hence
fully faithful for pro-étale sheaves of modules. Consequently the unit `Q ⟶ Ri^! Ri_! Q` of the
constructible exceptional adjunction `Hom(Ri_! K, L) ≃ Hom(K, Ri^! L)`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv`) is an isomorphism for every
bounded constructible `Q`
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedUpperShriekHomEquiv_id_of_isClosedImmersion`):
this is the last assertion of blueprint `lemma-local-cohomology-right-adjoint--1`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section LowerShriek

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i]

/-- For a closed immersion `i` admitting a compactification, the pro-étale `Ri_!` is the right
derived pushforward `Ri_*`. Write `Ri_! = D(k_!) ⋙ Rg_*` for the chosen compactification
`Z ⟶[k] Z̄ ⟶[g] X`. As `i` is proper, `k` has closed range, so `k_! ≅ k_*`
(`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range`) and
`k_!` preserves K-injective complexes; hence `Ri_! ≅ R(k_! ⋙ g_*)`, and `k_! ⋙ g_* ≅ i_*`
(`AlgebraicGeometry.ProEtale.isIso_lowerShriekToLowerStar`). -/
noncomputable def rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar :
    rightDerivedLowerShriek A i ≅ ((i)_*[A]).rightDerivedFunctor := by
  let c := HasCompactification.compactification i
  have : IsIso (openImmersionLowerShriekToLowerStar A c.i) :=
    isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A c.i
      (c.isClopen_range_openImmersion inferInstance).isClosed
  have : ((c.i)_*[A]).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction A c.i).preservesKInjectiveComplexes
  have : ((c.i)_!open[A]).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso
      (asIso (openImmersionLowerShriekToLowerStar A c.i)).symm
  exact Functor.isoWhiskerRight
      ((c.i)_!open[A]).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (asIso (lowerShriekToLowerStar A i))

end LowerShriek

section Unit

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {Z X : Scheme.{u}} (i : Z ⟶ X)
  [IsClosedImmersion i] [HasCompactification i]

instance full_rightDerivedLowerShriek_of_isClosedImmersion :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) i).Full :=
  Functor.Full.of_iso (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar _ i).symm

instance faithful_rightDerivedLowerShriek_of_isClosedImmersion :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) i).Faithful :=
  Functor.Faithful.of_iso (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar _ i).symm

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, last assertion: for a closed immersion
`i : Z ⟶ X` admitting a compactification, `X` quasi-compact, and a bounded constructible
`Q ∈ Dᵇc(Z_proét, Λ)`, `Λ` finite, the unit `Q ⟶ Ri^! Ri_! Q` of the constructible exceptional
adjunction `Hom(Ri_! K, L) ≃ Hom(K, Ri^! L)` of
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv` (the image of the identity of
`Ri_! Q`) is an isomorphism. Here `Ri_! = Ri_*`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar`).

For `P` bounded below of étale origin, composition with the unit `η` followed by the adjunction
bijection is `g ↦ Ri_! g`, which is bijective by full faithfulness of `Ri_!`; so `g ↦ g ≫ η` is
bijective on `Hom(P, Q)`. Taking `P = Ri^! Ri_! Q`, which is bounded below of étale origin, gives
a left inverse `r` of `η`, and taking `P = Q` shows that `η ≫ r = 𝟙`. -/
theorem isIso_rightDerivedUpperShriekHomEquiv_id_of_isClosedImmersion [CompactSpace X]
    {Q : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hQ : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z Q) :
    IsIso (rightDerivedUpperShriekHomEquiv i hQ.plusEtaleOrigin
      (hQ.plusEtaleOrigin.rightDerivedLowerShriek_obj i).plus (𝟙 _)) := by
  set hL := (hQ.plusEtaleOrigin.rightDerivedLowerShriek_obj i).plus
  set η := rightDerivedUpperShriekHomEquiv i hQ.plusEtaleOrigin hL (𝟙 _)
  -- composition with `η` is bijective on maps out of objects bounded below of étale origin
  have key : ∀ {P} (hP : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z P),
      Function.Bijective (fun g : P ⟶ Q ↦ g ≫ η) := fun {P} hP ↦ by
    have h : (fun g : P ⟶ Q ↦ g ≫ η) =
        rightDerivedUpperShriekHomEquiv i hP hL ∘
          (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) i).map := by
      ext g
      simp only [Function.comp_apply, η]
      rw [← rightDerivedUpperShriekHomEquiv_naturality_left i hP hQ.plusEtaleOrigin hL,
        Category.comp_id]
    rw [h]
    exact (rightDerivedUpperShriekHomEquiv i hP hL).bijective.comp
      ⟨(rightDerivedLowerShriek _ i).map_injective, (rightDerivedLowerShriek _ i).map_surjective⟩
  obtain ⟨r, hr⟩ := (key (plusEtaleOrigin_rightDerivedUpperShriek_obj i hL)).2 (𝟙 _)
  refine ⟨r, (key hQ.plusEtaleOrigin).1 ?_, hr⟩
  have hr' : r ≫ η = 𝟙 _ := hr
  simp only [Category.assoc, Category.id_comp, hr', Category.comp_id]

end Unit

end ProEtale

end AlgebraicGeometry
