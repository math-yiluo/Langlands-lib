/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite

/-!
# Sections over the spectrum of an algebraically closed field commute with colimits

Let `X` be a scheme isomorphic to `Spec K` for an algebraically closed field `K`. Every covering
sieve of the terminal object of `X_proét` contains the identity
(`AlgebraicGeometry.Scheme.ProEt.id_mem_of_mem_topology_of_iso`). As the map from a presheaf to
its sheafification is locally injective and locally surjective, it is bijective on sections over
`X`. Hence sections over `X` of the sheafification of a presheaf `G` are the sections `G(X)`, and
taking sections over `X` commutes with all colimits of sheaves which exist in the coefficient
category (colimits of sheaves being sheafified colimits of presheaves).

## Main statements

- `AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso`.
- `AlgebraicGeometry.ProEtale.preservesColimitsOfShape_sheafSections_of_iso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [HasSheafify (Scheme.ProEt.topology X) A]
  [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
  [(Scheme.ProEt.topology X).PreservesSheafification (CategoryTheory.forget A)]

/-- On a scheme `X` isomorphic to the spectrum of an algebraically closed field, the map from a
presheaf with values in a concrete category to its pro-étale sheafification is bijective on
sections over `X`. -/
lemma bijective_toSheafify_app_of_iso (e : X ≅ Spec (.of K)) (G : X.ProEtᵒᵖ ⥤ A) :
    Function.Bijective ((toSheafify (Scheme.ProEt.topology X) G).app
      (op (Scheme.ProEt.mk (𝟙 X)))) := by
  refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
  · simpa using Scheme.ProEt.id_mem_of_mem_topology_of_iso e
      (Presheaf.equalizerSieve_mem (Scheme.ProEt.topology X) (toSheafify _ G) x y hxy)
  · obtain ⟨t, ht⟩ := Scheme.ProEt.id_mem_of_mem_topology_of_iso e
      (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) (toSheafify _ G) s)
    exact ⟨t, by simpa using ht⟩

/-- On a scheme `X` isomorphic to the spectrum of an algebraically closed field, taking sections
over `X` of pro-étale sheaves with values in a concrete category `A` commutes with colimits of
shape `J` in `A`. -/
lemma preservesColimitsOfShape_sheafSections_of_iso (e : X ≅ Spec (.of K))
    [(CategoryTheory.forget A).ReflectsIsomorphisms] (J : Type*) [Category J]
    [HasColimitsOfShape J A] :
    PreservesColimitsOfShape J ((sheafSections (Scheme.ProEt.topology X) A).obj
      (op (Scheme.ProEt.mk (𝟙 X)))) := by
  have (G : X.ProEtᵒᵖ ⥤ A) : IsIso ((Functor.whiskerRight
      (sheafificationAdjunction (Scheme.ProEt.topology X) A).unit
      ((evaluation _ A).obj (op (Scheme.ProEt.mk (𝟙 X))))).app G) :=
    (isIso_iff_of_reflects_iso _ (CategoryTheory.forget A)).1
      ((isIso_iff_bijective _).2 (bijective_toSheafify_app_of_iso e G))
  have : IsIso (Functor.whiskerRight (sheafificationAdjunction (Scheme.ProEt.topology X) A).unit
      ((evaluation _ A).obj (op (Scheme.ProEt.mk (𝟙 X))))) :=
    NatIso.isIso_of_isIso_app _
  have : PreservesColimitsOfShape J (presheafToSheaf (Scheme.ProEt.topology X) A ⋙
      (sheafSections (Scheme.ProEt.topology X) A).obj (op (Scheme.ProEt.mk (𝟙 X)))) :=
    preservesColimitsOfShape_of_natIso (asIso (Functor.whiskerRight
      (sheafificationAdjunction (Scheme.ProEt.topology X) A).unit
      ((evaluation _ A).obj (op (Scheme.ProEt.mk (𝟙 X))))))
  exact (sheafificationAdjunction (Scheme.ProEt.topology X) A).preservesColimitsOfShape_of_comp
    _ J

end AlgebraicGeometry.ProEtale
