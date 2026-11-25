/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep

import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The open-stabilizer right adjoint

Source: Stacks Project, Injectives, Tag 04JF, proof of Lemma 19.3.1
(blueprint: lem-exc-rg-open-stabilizer-adjoint).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

/-- (blueprint: lem-exc-rg-open-stabilizer-adjoint) Stacks, Tag 04JF.
The functor forgetting the open-stabilizer condition. -/
noncomputable abbrev forgetDiscreteGModule (R : Type u) (G : Type v) [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    Rep.DiscreteContinuousRep.{u, v, w} R G ⥤ Rep.{w} R G :=
  CategoryTheory.ObjectProperty.ι _

noncomputable section

-- Keep stabilizers as subgroups so that openness passes to larger stabilizers.
private def vectorStabilizer {R : Type u} {G : Type v} [Ring R] [Group G]
    (M : Rep.{w} R G) (x : M) : Subgroup G where
  carrier := {g | M.ρ g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at *
    rw [M.ρ_mul, LinearMap.comp_apply, hh, hg]
  inv_mem' := by
    intro g hg
    exact (M.ρ.inv_apply_eq_iff).2 hg.symm

private theorem open_image {R : Type u} {G : Type v} [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {M N : Rep.{w} R G}
    (f : M ⟶ N) (x : M) (hx : IsOpen {g : G | M.ρ g x = x}) :
    IsOpen {g : G | N.ρ g (f.hom x) = f.hom x} := by
  apply Subgroup.isOpen_mono (H₁ := vectorStabilizer M x)
    (H₂ := vectorStabilizer N (f.hom x)) _ hx
  intro g hg
  change N.ρ g (f.hom x) = f.hom x
  rw [← Rep.hom_comm_apply, hg]

private def openVectors {R : Type u} {G : Type v} [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{w} R G) : Submodule R M where
  carrier := {x | IsOpen {g : G | M.ρ g x = x}}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    apply Subgroup.isOpen_mono
      (H₁ := vectorStabilizer M x ⊓ vectorStabilizer M y)
      (H₂ := vectorStabilizer M (x + y))
    · intro g hg
      change M.ρ g (x + y) = x + y
      rw [map_add, hg.1, hg.2]
    · exact hx.inter hy
  smul_mem' := by
    intro r x hx
    apply Subgroup.isOpen_mono (H₁ := vectorStabilizer M x)
      (H₂ := vectorStabilizer M (r • x)) _ hx
    intro g hg
    change M.ρ g (r • x) = r • x
    rw [map_smul, hg]

-- Transport the stabilizer through the continuous conjugation map.
private theorem openVectors_stable {R : Type u} {G : Type v} [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{w} R G) (a : G) :
    openVectors M ≤ (openVectors M).comap (M.ρ a) := by
  intro x hx
  change IsOpen {g : G | M.ρ g (M.ρ a x) = M.ρ a x}
  have heq : {g : G | M.ρ g (M.ρ a x) = M.ρ a x} =
      (fun g : G => a⁻¹ * g * a) ⁻¹' {g : G | M.ρ g x = x} := by
    ext g
    change M.ρ g (M.ρ a x) = M.ρ a x ↔ M.ρ (a⁻¹ * g * a) x = x
    rw [M.ρ_mul, LinearMap.comp_apply, M.ρ_mul, LinearMap.comp_apply]
    constructor
    · intro h
      rw [h, M.ρ.inv_self_apply]
    · intro h
      have h' := congrArg (M.ρ a) h
      simpa only [M.ρ.self_inv_apply] using h'
  rw [heq]
  exact hx.preimage ((continuous_const.mul continuous_id).mul continuous_const)

private def openRepresentation {R : Type u} {G : Type v} [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{w} R G) :
    Rep.DiscreteContinuousRep.{u, v, w} R G :=
  ⟨M.subrepresentation (openVectors M) (openVectors_stable M), by
    intro x
    have hset : {g : G | (M.subrepresentation (openVectors M)
        (openVectors_stable M)).ρ g x = x} = {g : G | M.ρ g x.val = x.val} := by
      ext g
      exact Subtype.ext_iff
    rw [hset]
    exact x.property⟩

private def openInclusion {R : Type u} {G : Type v} [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{w} R G) :
    (openRepresentation M).obj ⟶ M :=
  M.subtype (openVectors M) (openVectors_stable M)

private def openFunctor (R : Type u) (G : Type v) [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    Rep.{w} R G ⥤ Rep.DiscreteContinuousRep.{u, v, w} R G where
  obj := openRepresentation
  map {M N} f := ObjectProperty.homMk (Rep.ofHom
    ⟨f.hom.toLinearMap.domRestrict (openVectors M) |>.codRestrict (openVectors N)
      (fun x => open_image f x.val x.property), by
      intro g
      ext x
      exact Rep.hom_comm_apply f g x.val⟩)
  map_id M := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    ext x
    rfl

private def openHomEquiv {R : Type u} {G : Type v} [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Rep.DiscreteContinuousRep.{u, v, w} R G) (M : Rep.{w} R G) :
    ((forgetDiscreteGModule R G).obj N ⟶ M) ≃ (N ⟶ (openFunctor R G).obj M) where
  toFun f := ObjectProperty.homMk (Rep.ofHom
    ⟨f.hom.toLinearMap.codRestrict (openVectors M)
      (fun x => open_image f x (N.property x)), by
      intro g
      ext x
      exact Rep.hom_comm_apply f g x⟩)
  invFun f := f.hom ≫ openInclusion M
  left_inv f := by
    apply Rep.hom_ext
    ext x
    rfl
  right_inv f := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    ext x
    rfl

private def openAdjunction (R : Type u) (G : Type v) [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    forgetDiscreteGModule.{u, v, w} R G ⊣ openFunctor R G :=
  Adjunction.mkOfHomEquiv {
    homEquiv := openHomEquiv
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      apply Rep.hom_ext
      ext x
      rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      ext x
      rfl }

/-- (blueprint: lem-exc-rg-open-stabilizer-adjoint) Stacks, Tag 04JF.
The full inclusion of discrete `R`-linear `G`-modules in all `R[G]`-modules is fully faithful
and preserves monomorphisms. The right adjoint sends a module to its open-stabilizer submodule:
the counit is injective and its image consists exactly of the elements with open stabilizer.

For the proof, morphisms in the full subcategory are precisely the equivariant linear maps.
For a monomorphism, the kernel of its underlying linear map is a `G`-stable submodule of its
source, and its elements still have open stabilizers. Its inclusion is therefore a morphism
in the full subcategory. Monicity makes this inclusion zero, so the underlying map is
injective and hence monic in the ambient representation category.

The open-stabilizer elements form a submodule: the stabilizer of a sum contains the
intersection of the two stabilizers, and the stabilizer of a scalar multiple contains the
original stabilizer. Conjugation carries the stabilizer of `x` to that of `g • x`, so this
submodule is `G`-stable and inherits the action. Every equivariant map from a discrete
module lands in this submodule, because it carries stabilizers into stabilizers.
Restriction and inclusion give inverse natural Hom-set bijections, yielding the adjunction.
The counit identifies the right adjoint with that submodule and its induced action.
Injectivity of objects has the meaning of `CategoryTheory.Injective` from
`def-sp-injective-resolutions`. -/
theorem openStabilizerAdjunction (R : Type u) (G : Type v) [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    (forgetDiscreteGModule.{u, v, w} R G).Full ∧
      (forgetDiscreteGModule.{u, v, w} R G).Faithful ∧
      (∀ ⦃N N' : Rep.DiscreteContinuousRep.{u, v, w} R G⦄ (f : N ⟶ N'),
        Mono f → Mono ((forgetDiscreteGModule.{u, v, w} R G).map f)) ∧
      ∃ (u : Rep.{w} R G ⥤ Rep.DiscreteContinuousRep.{u, v, w} R G)
        (adj : forgetDiscreteGModule.{u, v, w} R G ⊣ u),
        ∀ M : Rep.{w} R G,
          Function.Injective (adj.counit.app M).hom ∧
            ∀ x : M, x ∈ Set.range (adj.counit.app M).hom ↔
              IsOpen {g : G | M.ρ g x = x} := by
  refine ⟨inferInstance, inferInstance, ?_, openFunctor R G, openAdjunction R G, ?_⟩
  · intro N N' f hf
    -- The kernel is still discrete; monicity forces its inclusion to vanish.
    let K := LinearMap.ker f.hom.hom.toLinearMap
    have hk : ∀ g, K ≤ K.comap (N.obj.ρ g) := by
      intro g x hx
      change f.hom.hom (N.obj.ρ g x) = 0
      rw [Rep.hom_comm_apply]
      rw [show f.hom.hom x = 0 from hx, map_zero]
    let Kn : Rep.DiscreteContinuousRep.{u, v, w} R G :=
      ⟨N.obj.subrepresentation K hk, by
        intro x
        have hset : {g : G | (N.obj.subrepresentation K hk).ρ g x = x} =
            {g : G | N.obj.ρ g x.val = x.val} := by
          ext g
          exact Subtype.ext_iff
        rw [hset]
        exact N.property x.val⟩
    let i : Kn ⟶ N := ObjectProperty.homMk (N.obj.subtype K hk)
    let z : Kn ⟶ N := ObjectProperty.homMk 0
    have hcomp : i ≫ f = z ≫ f := by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      ext x
      change f.hom.hom x.val = f.hom.hom 0
      rw [map_zero]
      exact x.property
    have hi : i = z := (cancel_mono f).1 hcomp
    apply (Rep.mono_iff_injective _).2
    intro x y hxy
    change f.hom.hom x = f.hom.hom y at hxy
    have hx : x - y ∈ K := by
      change f.hom.hom (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hx0 := congrArg (fun j : Kn ⟶ N => j.hom.hom ⟨x - y, hx⟩) hi
    change x - y = 0 at hx0
    exact sub_eq_zero.mp hx0
  · intro M
    change Function.Injective (openInclusion M).hom ∧ _
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    change (∃ y : openVectors M, y.val = x) ↔ x ∈ openVectors M
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

end

end ModuleCat
