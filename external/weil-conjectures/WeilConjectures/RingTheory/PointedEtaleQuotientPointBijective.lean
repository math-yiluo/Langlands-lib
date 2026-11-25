/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import WeilConjectures.RingTheory.SurjectiveQuotientBaseChange

/-! # Bijection on hom sets into a residue-field point

Source: Stacks Project, Tag 05WS, and the universal property of the ring pushout.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace Algebra

private theorem quotient_base_change_unit_isIso {A K B : Type u}
    [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [Algebra A K]
    [IsScalarTower A (IsLocalRing.ResidueField A) K] [CommRing B] [IsLocalRing B]
    (π : A →+* B) (hπ : Function.Surjective π) :
    let adj := (commAlgCatEquivUnder (CommRingCat.of A)).toAdjunction.comp
      ((Under.mapPushoutAdj (CommRingCat.ofHom π)).comp
        (commAlgCatEquivUnder (CommRingCat.of B)).symm.toAdjunction)
    IsIso (adj.unit.app (CommAlgCat.of A K)) := by
  classical
  have : IsLocalHom π := IsLocalHom.of_surjective π hπ
  have hk : RingHom.ker π ≤ RingHom.ker (algebraMap A K) := by
    intro a ha
    have hm : a ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.maximalIdeal_comap π]
      change π a ∈ IsLocalRing.maximalIdeal B
      rw [RingHom.mem_ker.mp ha]
      exact Ideal.zero_mem _
    change algebraMap A K a = 0
    rw [IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) K]
    change algebraMap (IsLocalRing.ResidueField A) K (IsLocalRing.residue A a) = 0
    rw [(IsLocalRing.residue_eq_zero_iff a).mpr hm, map_zero]
  let β := π.liftOfSurjective hπ ⟨algebraMap A K, hk⟩
  have hβ (a : A) : β (π a) = algebraMap A K a :=
    π.liftOfSurjective_comp_apply hπ _ a
  let s : PushoutCocone (CommRingCat.ofHom (algebraMap A K)) (CommRingCat.ofHom π) :=
    PushoutCocone.mk (𝟙 (CommRingCat.of K)) (CommRingCat.ofHom β) (by
      ext a
      exact (hβ a).symm)
  have hs : IsColimit s := PushoutCocone.isColimitAux' s fun t ↦ by
    refine ⟨t.inl, ?_, ?_, ?_⟩
    · exact Category.id_comp _
    · ext b
      obtain ⟨a, rfl⟩ := hπ b
      change t.inl.hom (β (π a)) = t.inr.hom (π a)
      rw [hβ]
      exact congrArg (fun f ↦ f a) t.condition
    · intro m hm _
      change (𝟙 (CommRingCat.of K)) ≫ m = t.inl at hm
      simpa only [Category.id_comp] using hm
  let hp := IsPushout.of_isColimit hs
  have hcan : hp.isoPushout.hom =
      pushout.inl (CommRingCat.ofHom (algebraMap A K)) (CommRingCat.ofHom π) := by
    simpa only [s, PushoutCocone.mk_inl, Category.id_comp] using hp.inl_isoPushout_hom
  have : IsIso (pushout.inl (CommRingCat.ofHom (algebraMap A K))
      (CommRingCat.ofHom π)) := by
    rw [← hcan]
    infer_instance
  dsimp only
  let adj := (commAlgCatEquivUnder (CommRingCat.of A)).toAdjunction.comp
    ((Under.mapPushoutAdj (CommRingCat.ofHom π)).comp
      (commAlgCatEquivUnder (CommRingCat.of B)).symm.toAdjunction)
  change IsIso (adj.unit.app (CommAlgCat.of A K))
  have heq : (forget (CommAlgCat A)).map (adj.unit.app (CommAlgCat.of A K)) =
      (forget CommRingCat).map
        (pushout.inl (CommRingCat.ofHom (algebraMap A K)) (CommRingCat.ofHom π)) := by
    ext x
    rfl
  have : IsIso ((forget (CommAlgCat A)).map (adj.unit.app (CommAlgCat.of A K))) := by
    rw [heq]
    infer_instance
  exact isIso_of_reflects_iso _ (forget (CommAlgCat A))
private theorem map_surjective_of_unit_iso
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {H : C ⥤ D} {R : D ⥤ C} (adj : H ⊣ R) (K S : C)
    [IsIso (adj.unit.app K)] : Function.Surjective (fun f : S ⟶ K ↦ H.map f) := by
  intro q
  let q' := adj.homEquiv S (H.obj K) q ≫ inv (adj.unit.app K)
  refine ⟨q', ?_⟩
  apply (adj.homEquiv S (H.obj K)).injective
  rw [adj.homEquiv_unit]
  change adj.unit.app S ≫ (H ⋙ R).map q' = _
  rw [← adj.unit.naturality q']
  simp [q', Category.assoc]

private theorem map_bijective_of_unit_iso
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {H : C ⥤ D} {R : D ⥤ C} (adj : H ⊣ R) (K S : C)
    [IsIso (adj.unit.app K)] : Function.Bijective (fun f : S ⟶ K ↦ H.map f) := by
  refine ⟨?_, map_surjective_of_unit_iso adj K S⟩
  intro f g h
  change H.map f = H.map g at h
  apply (cancel_mono (adj.unit.app K)).mp
  have hf := adj.unit.naturality f
  have hg := adj.unit.naturality g
  simp only [Functor.id_map, Functor.comp_map] at hf hg
  rw [hf, hg, h]


/-- Maps from an A-algebra to K are unchanged by extension of scalars along π.
Source: Stacks Project, Tag 05WS, the fact that ker π acts trivially on K.
(blueprint: lem-sbc-pointed-etale-quotient-point-bijective)

Proof: A surjective local map is local, so ker π is in the maximal ideal of A.
Consequently it acts by zero on K. Descend A -> K to β:B -> K. The cocone
with legs id_K and β is a pushout: its universal map is the K-leg, compatibility
with its B-leg is checked after π, and uniqueness follows from its identity leg.
Thus the canonical K -> H(K) is an isomorphism. Use the explicit base-change
adjunction, obtained by composing the two algebra/under-category equivalences
with Under.mapPushoutAdj. Its unit at K has this canonical underlying map,
so it too is an isomorphism. The adjunction hom equivalence and the inverse
unit give surjectivity on maps to K. For injectivity, naturality of the unit
and cancellation of its component at K suffice. -/
theorem quotientBaseChange_point_bijective
    (A K B : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [Algebra A K]
    [IsScalarTower A (IsLocalRing.ResidueField A) K] [CommRing B] [IsLocalRing B]
    (π : A →+* B) (hπ : Function.Surjective π) (S : CommAlgCat.{u} A) :
    Function.Bijective (fun f : S ⟶ CommAlgCat.of A K ↦ (quotientBaseChange π).map f) := by
  let R := (commAlgCatEquivUnder (CommRingCat.of B)).functor ⋙
    Under.map (CommRingCat.ofHom π) ⋙ (commAlgCatEquivUnder (CommRingCat.of A)).inverse
  let adj : quotientBaseChange π ⊣ R :=
    (commAlgCatEquivUnder (CommRingCat.of A)).toAdjunction.comp
      ((Under.mapPushoutAdj (CommRingCat.ofHom π)).comp
        (commAlgCatEquivUnder (CommRingCat.of B)).symm.toAdjunction)
  have : IsIso (adj.unit.app (CommAlgCat.of A K)) :=
    quotient_base_change_unit_isIso π hπ
  exact map_bijective_of_unit_iso adj (CommAlgCat.of A K) S

end Algebra
