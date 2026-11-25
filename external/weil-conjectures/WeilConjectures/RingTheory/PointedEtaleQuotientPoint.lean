/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import WeilConjectures.RingTheory.SurjectiveQuotientBaseChange

/-! # Comparing the base-changed separable closures

Source: Stacks Project, Tag 05WS.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

private theorem exists_compatible_equiv
    (A K B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π) :
    ∃ e : K ≃+* L, ∀ a : A, e (algebraMap A K a) = algebraMap B L (π a) := by
  classical
  have : IsLocalHom π := IsLocalHom.of_surjective π hπ
  let r := IsLocalRing.ResidueField.map π
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨a, rfl⟩ := hπ b
    exact ⟨IsLocalRing.residue A a, rfl⟩
  let e₀ := RingEquiv.ofBijective r ⟨r.injective, hr⟩
  let : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    e₀.toRingHom.toAlgebra
  let : Algebra (IsLocalRing.ResidueField A) L :=
    ((algebraMap (IsLocalRing.ResidueField B) L).comp e₀.toRingHom).toAlgebra
  have : IsScalarTower (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e₁ : IsLocalRing.ResidueField A ≃ₐ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField B := AlgEquiv.ofRingEquiv (f := e₀) fun _ ↦ rfl
  have : Algebra.IsSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) := AlgEquiv.Algebra.isSeparable e₁
  have : Algebra.IsSeparable (IsLocalRing.ResidueField A) L :=
    Algebra.IsSeparable.trans (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) L
  have : IsSepClosed L := IsSepClosure.sep_closed (IsLocalRing.ResidueField B)
  have : IsSepClosure (IsLocalRing.ResidueField A) L := ⟨inferInstance, inferInstance⟩
  let e := IsSepClosure.equiv (IsLocalRing.ResidueField A) K L
  refine ⟨e.toRingEquiv, fun a ↦ ?_⟩
  rw [IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) K]
  change e (algebraMap (IsLocalRing.ResidueField A) K (IsLocalRing.residue A a)) = _
  rw [e.commutes]
  change algebraMap (IsLocalRing.ResidueField B) L (r (IsLocalRing.residue A a)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  exact (IsScalarTower.algebraMap_apply B (IsLocalRing.ResidueField B) L (π a)).symm

/-- The base change of the chosen separable closure is isomorphic to the new one.
Source: Stacks Project, Tag 05WS, and step 1 of
`lem-sbc-pointed-etale-quotient-final`.
(blueprint: lem-sbc-pointed-etale-quotient-point)

Proof: A surjective map between local rings identifies B with A/ker π and identifies
its residue field with that of A. The ideal ker π lies in the maximal ideal of A,
so it acts by zero on K. Consequently the pushout of A -> K along π is K with
its descended B-action. Transport the residue-field algebra structure of L across
the residue-field isomorphism. Both K and L are then separable closures of the
same field. The separable-closure equivalence is a B-algebra equivalence because
the B-actions factor through that field. Compose this equivalence with the pushout
identification to obtain the claimed isomorphism. -/
theorem pointedEtaleQuotient_point_iso
    (A K B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π) :
    Nonempty ((quotientBaseChange π).obj (CommAlgCat.of A K) ≅ CommAlgCat.of B L) := by
  classical
  obtain ⟨e, he⟩ := exists_compatible_equiv A K B L π hπ
  let β : B →+* K := e.symm.toRingHom.comp (algebraMap B L)
  have hβ (a : A) : β (π a) = algebraMap A K a := by
    change e.symm (algebraMap B L (π a)) = _
    rw [← he, e.symm_apply_apply]
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
  let d := hp.isoPushout.symm ≪≫ e.toCommRingCatIso
  let d' : Under.mk (pushout.inr (CommRingCat.ofHom (algebraMap A K))
      (CommRingCat.ofHom π)) ≅ CommRingCat.mkUnder (CommRingCat.of B) L :=
    Under.isoMk d (by
      change pushout.inr (CommRingCat.ofHom (algebraMap A K)) (CommRingCat.ofHom π) ≫
        (hp.isoPushout.inv ≫ e.toCommRingCatIso.hom) = CommRingCat.ofHom (algebraMap B L)
      rw [← Category.assoc, hp.inr_isoPushout_inv]
      ext b
      change e (e.symm (algebraMap B L b)) = algebraMap B L b
      exact e.apply_symm_apply _)
  exact ⟨(commAlgCatEquivUnder (CommRingCat.of B)).inverse.mapIso d' ≪≫
    ((commAlgCatEquivUnder (CommRingCat.of B)).unitIso.app (CommAlgCat.of B L)).symm⟩


end Algebra
