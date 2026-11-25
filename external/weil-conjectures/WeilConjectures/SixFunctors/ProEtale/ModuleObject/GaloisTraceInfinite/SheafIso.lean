/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsFilteredColimit

/-!
# Isomorphisms of abelian sheaves detected on a covering family of objects

A morphism `φ : F ⟶ G` of sheaves of abelian groups which is bijective on sections over the
objects of a class `P` is an isomorphism, as soon as every object is covered by objects of `P`
(`CategoryTheory.Sheaf.isIso_of_isIso_app_of_forall_exists_mem`): it is then locally injective
and locally surjective.

We also record the variant of
`AlgebraicGeometry.Scheme.ProEt.isColimitSectionsOfIsColimit` for filtered diagrams indexed by a
small category in `Type u`
(`AlgebraicGeometry.Scheme.ProEt.isColimitSectionsOfIsColimitOfShrink`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)

/-- A morphism of abelian sheaves which is bijective on the sections over the objects of a class
`P` covering every object is an isomorphism. -/
lemma isIso_of_isIso_app_of_forall_exists_mem
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] (P : C → Prop)
    (hP : ∀ X, ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f →
      ∃ (Z : C) (a : Y ⟶ Z) (b : Z ⟶ X), P Z ∧ a ≫ b = f)
    (hφ : ∀ X, P X → IsIso (φ.hom.app (op X))) : IsIso φ := by
  have hinj (X : C) (hX : P X) : Function.Injective (φ.hom.app (op X)) := by
    have := hφ X hX
    rw [← AddCommGrpCat.mono_iff_injective]
    infer_instance
  have hsurj (X : C) (hX : P X) : Function.Surjective (φ.hom.app (op X)) := by
    have := hφ X hX
    rw [← AddCommGrpCat.epi_iff_surjective]
    infer_instance
  refine (isLocallyBijective_iff_isIso φ).1 ⟨⟨fun {X} x y hxy ↦ ?_⟩, ⟨fun {U} s ↦ ?_⟩⟩
  · obtain ⟨S, hS, hSP⟩ := hP X.unop
    refine J.superset_covering (fun Y f hf ↦ ?_) hS
    obtain ⟨Z, a, b, hZ, rfl⟩ := hSP f hf
    have hb : F.obj.map b.op x = F.obj.map b.op y := by
      apply hinj Z hZ
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact congrArg _ hxy
    simp only [Presheaf.equalizerSieve_apply, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, hb]
  · obtain ⟨S, hS, hSP⟩ := hP U
    refine J.superset_covering (fun Y f hf ↦ ?_) hS
    obtain ⟨Z, a, b, hZ, rfl⟩ := hSP f hf
    obtain ⟨t, ht⟩ := hsurj Z hZ (G.obj.map b.op s)
    refine ⟨F.obj.map a.op t, ?_⟩
    rw [NatTrans.naturality_apply, ht, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} {c : Cocone F}

/-- `AlgebraicGeometry.Scheme.ProEt.isColimitSectionsOfIsColimit` for a filtered diagram indexed
by a small category in `Type u`, such as the finite Galois subextensions of a Galois extension. -/
noncomputable def isColimitSectionsOfIsColimitOfShrink (hc : IsColimit c) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    IsColimit ((abSectionsFunctor W).mapCocone c) :=
  let e := (AsSmall.equiv.{u, u, u + 1} (C := J)).symm
  (IsColimit.whiskerEquivalenceEquiv e).symm
    (isColimitSectionsOfIsColimit (hc.whiskerEquivalence e) W)

end AlgebraicGeometry.Scheme.ProEt
