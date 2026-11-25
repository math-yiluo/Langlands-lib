/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.OpenClosed.Supported
public import WeilConjectures.SixFunctors.OpenClosed.Supports
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# Sections supported on a closed subscheme

Let `s : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. For an étale sheaf `M`
on `X` the subsheaf of *sections supported on `Z`* is

`𝒢_Z M = ker (M ⟶ j_* j^* M)`,

the kernel of the unit of `j^* ⊣ j_*` (`AlgebraicGeometry.Etale.sectionsWithSupport`). Its
restriction to `U` vanishes, so it is the pushforward of a sheaf on `Z`, namely of
`s^! M := s^* 𝒢_Z M` (`AlgebraicGeometry.Etale.closedUpperShriek`), and `s_* s^! M ≅ 𝒢_Z M`.
The functor `s^!` is right adjoint to `s_*`; this sheaf-level adjunction is
`AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction`, defined together with `𝒢_Z` and
`s^!` in `WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek`. This file
records the additional facts used in the purity chapter: the identification `s_* s^! ≅ 𝒢_Z`, the
description of the counit of `s_* ⊣ s^!`, and flasqueness for the pair.

A sheaf `I` is *flasque for the pair* if `I ⟶ j_* j^* I` is an epimorphism; injective sheaves
are flasque.

## Main definitions

- `AlgebraicGeometry.Etale.IsFlasqueFor`: flasque sheaves for the pair.

## Main statements

- `AlgebraicGeometry.Etale.closedUpperShriekCompLowerStarIso`: `s_* s^! ≅ 𝒢_Z`.
- `AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction_counit_app`: the counit of
  `s_* ⊣ s^!` is `s_* s^! M ≅ 𝒢_Z M ⟶ M`.
- `AlgebraicGeometry.Etale.isFlasqueFor_of_injective`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U Z X : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)

instance (M : Sheaf X.smallEtaleTopology A) : Mono ((sectionsWithSupportι A j).app M) := by
  change Mono (kernel.ι _); infer_instance

/-- A morphism `f : N ⟶ M` from a sheaf vanishing on the open part is supported on `Z`: its
composite with the unit `M ⟶ j_* j^* M` vanishes. -/
lemma comp_unit_app_eq_zero_of_isZero {N M : Sheaf X.smallEtaleTopology A}
    (hN : IsZero ((j)^*[A].obj N)) (f : N ⟶ M) :
    f ≫ (upperStarLowerStarAdjunction A j).unit.app M = 0 := by
  have h := (upperStarLowerStarAdjunction A j).unit.naturality f
  dsimp at h
  rw [h, ((j)_*[A].map_isZero hN).eq_of_tgt ((upperStarLowerStarAdjunction A j).unit.app N) 0,
    zero_comp]

/-- On a sheaf vanishing on the open part, the inclusion of the supported sections is an
isomorphism. -/
lemma isIso_sectionsWithSupportι_app_of_isZero {M : Sheaf X.smallEtaleTopology A}
    (hM : IsZero ((j)^*[A].obj M)) : IsIso ((sectionsWithSupportι A j).app M) := by
  have h : (upperStarLowerStarAdjunction A j).unit.app M = 0 := by
    simpa using comp_unit_app_eq_zero_of_isZero A j hM (𝟙 M)
  change IsIso (kernel.ι ((upperStarLowerStarAdjunction A j).unit.app M))
  have : IsSplitEpi (kernel.ι ((upperStarLowerStarAdjunction A j).unit.app M)) :=
    ⟨⟨kernel.lift _ (𝟙 M) (by rw [h, comp_zero]), by simp⟩⟩
  exact isIso_of_mono_of_epi _

variable [IsClosedImmersion s] [IsOpenImmersion j]

/-- Blueprint `definition-local-cohomology`: Supported sections and flasque objects

`s_* s^! M ≅ 𝒢_Z M`: the sheaf `𝒢_Z M = ker (M ⟶ j_* j^* M)` of sections of `M` supported on
the closed complement `Z` of the open immersion `j : U ⟶ X`
(`AlgebraicGeometry.Etale.sectionsWithSupport`) is the pushforward of
`s^! M = s^* 𝒢_Z M` (`AlgebraicGeometry.Etale.closedUpperShriek`), through the unit of
`s^* ⊣ s_*`, which is invertible on sheaves vanishing on the open part. The functor `s^!` is
right adjoint to `s_*` (`AlgebraicGeometry.Etale.lowerStarClosedUpperShriekAdjunction`), and it
is distinct from the ordinary restriction `s^*`.

The blueprint node is stated on the pro-étale site; it is formalised here on the small étale
site, the site of the purity chapter (`def-pur-conventions`); the pro-étale forms are
`AlgebraicGeometry.ProEtale.sectionsWithSupport`, `AlgebraicGeometry.ProEtale.closedUpperShriek`
(with `AlgebraicGeometry.ProEtale.closedUpperShriekCompLowerStarIso`) and
`AlgebraicGeometry.ProEtale.IsFlasqueFor`. -/
noncomputable def closedUpperShriekCompLowerStarIso
    (hjs : Set.range s.base = (Set.range j.base)ᶜ) :
    closedUpperShriek A s j ⋙ (s)_*[A] ≅ sectionsWithSupport A j :=
  NatIso.ofComponents (fun M ↦
    haveI := isIso_upperStarLowerStarAdjunction_unit_app_of_isZero A s j hjs
      (isZero_upperStar_sectionsWithSupport A j M)
    (asIso ((upperStarLowerStarAdjunction A s).unit.app ((sectionsWithSupport A j).obj M))).symm)
    (fun f ↦ by
      dsimp [closedUpperShriek]
      rw [IsIso.comp_inv_eq, assoc, IsIso.eq_inv_comp]
      exact ((upperStarLowerStarAdjunction A s).unit.naturality _).symm)

/-- The counit `s_* s^! M ⟶ M` of `s_* ⊣ s^!` is the identification `s_* s^! M ≅ 𝒢_Z M`
followed by the inclusion of the supported sections. -/
lemma lowerStarClosedUpperShriekAdjunction_counit_app
    (hjs : Set.range s.base = (Set.range j.base)ᶜ) (M : Sheaf X.smallEtaleTopology A) :
    (lowerStarClosedUpperShriekAdjunction A s j hjs).counit.app M =
      (closedUpperShriekCompLowerStarIso A s j hjs).hom.app M ≫
        (sectionsWithSupportι A j).app M := by
  have := isIso_upperStarLowerStarAdjunction_unit_app_of_isZero A s j hjs
    (isZero_upperStar_sectionsWithSupport A j M)
  simp only [lowerStarClosedUpperShriekAdjunction, Adjunction.mkOfHomEquiv_counit_app,
    lowerStarClosedUpperShriekHomEquiv_symm_apply]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

instance (hjs : Set.range s.base = (Set.range j.base)ᶜ) (M : Sheaf X.smallEtaleTopology A) :
    Mono ((lowerStarClosedUpperShriekAdjunction A s j hjs).counit.app M) := by
  rw [lowerStarClosedUpperShriekAdjunction_counit_app]
  infer_instance

/-- Blueprint `definition-local-cohomology`: Supported sections and flasque objects

A sheaf `I` on `X` is *flasque for the pair* `(Z, U)` if the restriction `I ⟶ j_* j^* I` to the
open part is an epimorphism; then `0 ⟶ 𝒢_Z I ⟶ I ⟶ j_* j^* I ⟶ 0` is exact. As for
`AlgebraicGeometry.Etale.sectionsWithSupport`, this is the étale version; the pro-étale version
is `AlgebraicGeometry.ProEtale.IsFlasqueFor`. -/
def IsFlasqueFor (I : Sheaf X.smallEtaleTopology A) : Prop :=
  Epi ((upperStarLowerStarAdjunction A j).unit.app I)

section Concrete

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJZ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [hJX : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJX hJZ in
/-- Injective sheaves are flasque for the pair: the restriction `I ⟶ j_* j^* I` is even a split
epimorphism
(`AlgebraicGeometry.Etale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`). -/
lemma isFlasqueFor_of_injective (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    (I : Sheaf X.smallEtaleTopology A) [Injective I] : IsFlasqueFor A j I := by
  have := isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective A j s hjs I
  unfold IsFlasqueFor; infer_instance

end Concrete

end Etale

end AlgebraicGeometry
