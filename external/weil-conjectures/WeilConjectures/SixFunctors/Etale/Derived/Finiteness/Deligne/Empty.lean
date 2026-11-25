/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.Topology.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.OpenBase

/-!
# Generic constructibility when the generic fibre is empty

If the source `X` of `j : X ⟶ Y` is empty, every direct image along `j` vanishes after every base
change, so the generic constructibility property holds over the whole base
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_isEmpty`). If only the generic fibre
of `X` over an irreducible noetherian base `S` is empty, then `X` is empty over a nonempty open of
`S`, by Chevalley's theorem: the image of `X` is a constructible set missing the generic point
(`AlgebraicGeometry.Etale.exists_hasDirectImageBaseChangeOnPlus_of_genericPoint_not_mem_range`).
This is the start of the induction on the generic dimension in the proof of
`theorem-generic-constructibility-base-change-rj`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Empty source**: if `X` is empty, the direct image of every complex along `j : X ⟶ Y` is
bounded constructible and commutes with base change, all of them being zero. -/
theorem HasDirectImageBaseChangeOnPlus.of_isEmpty {S X Y : Scheme.{u}} [IsEmpty X] (fY : Y ⟶ S)
    (j : X ⟶ Y) (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (U : Set S) : HasDirectImageBaseChangeOnPlus Λ fY j K U := by
  intro T _ t _ YT XT gT fT gXT jT _ _
  have : IsEmpty XT := ⟨fun x ↦ isEmptyElim (gXT x)⟩
  have hK : IsZero K := (IsZero.iff_id_eq_zero K).2 (_root_.DerivedCategory.Plus.ι.map_injective
    ((isZero_derivedCategory_of_isEmpty _ X _).eq_of_src _ _))
  have h₁ : IsZero ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
      (((gXT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) :=
    Functor.map_isZero _ (Functor.map_isZero _ hK)
  have h₂ : IsZero (((gT)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
      ((j)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K)) :=
    Functor.map_isZero _ (Functor.map_isZero _ hK)
  exact ⟨boundedConstructible_of_isZero Λ (_root_.DerivedCategory.Plus.ι.map_isZero h₁),
    ⟨⟨h₁.to_ _, h₂.eq_of_src _ _, h₁.eq_of_src _ _⟩⟩⟩

/-- **Empty generic fibre**: let `S` be irreducible and noetherian and `j : X ⟶ Y` a morphism of
`S`-schemes with `X` of finite type over `S`. If the generic point of `S` is not in the image of
`X`, then over a nonempty open of `S` the direct image of every complex along `j` is bounded
constructible and commutes with base change. -/
theorem exists_hasDirectImageBaseChangeOnPlus_of_genericPoint_not_mem_range {S X Y : Scheme.{u}}
    [IrreducibleSpace S] [IsNoetherian S] (fY : Y ⟶ S) (j : X ⟶ Y)
    [LocallyOfFiniteType (j ≫ fY)] [QuasiCompact (j ≫ fY)]
    (hX : genericPoint S ∉ Set.range (j ≫ fY))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ HasDirectImageBaseChangeOnPlus Λ fY j K U := by
  have hc : IsConstructible (Set.range (j ≫ fY))ᶜ := by
    rw [← Set.image_univ]
    exact ((j ≫ fY).isConstructible_image IsConstructible.univ).compl
  obtain ⟨u, hu, hηu, hus⟩ := hc.exists_isOpen_mem_subset (ξ := genericPoint S) (by
    rw [genericPoint_spec S, irreducibleComponents_eq_singleton]
    rfl) hX
  let U₀ : S.Opens := ⟨u, hu⟩
  have : IsEmpty (j ⁻¹ᵁ (fY ⁻¹ᵁ U₀)) := ⟨fun x ↦ hus x.2 ⟨x.1, rfl⟩⟩
  refine ⟨U₀, ⟨_, hηu⟩, ?_⟩
  have h := HasDirectImageBaseChangeOnPlus.of_restrict_base (Λ := Λ) (fY := fY) j U₀ (K := K)
    (V := Set.univ) (HasDirectImageBaseChangeOnPlus.of_isEmpty _ _ _ _)
  rwa [Set.image_univ, Opens.range_ι] at h

end Etale

end AlgebraicGeometry
