/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic

/-!
# Vanishing of germs and the support of an étale sheaf

Let `F` be an étale sheaf of `Λ`-modules on a scheme `X`. The germ of a section `z` of `F` over
an étale `X`-scheme `V` at a geometric point `t` of `V` vanishes if and only if `z` vanishes on
an étale neighbourhood of the image point of `t` in `V`; the geometric point itself plays no
role, since every geometric point lifts along étale morphisms. Consequently the vanishing of the
stalk of `F` at a geometric point only depends on the underlying point of `X`.

## Main statements

- `AlgebraicGeometry.Etale.toPresheafFiber_eq_zero_iff`: the vanishing criterion for germs.
- `AlgebraicGeometry.Etale.isZero_sheafFiber_iff_of_apply_eq`
  (`lem-kun-support-geometric-point-independent`): two geometric points with the same image
  have simultaneously vanishing stalks.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

instance preservesFilteredColimitsOfSize_forget_moduleCat :
    PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

/-- A morphism of étale `X`-schemes is étale. -/
lemma etale_left {X : Scheme.{u}} {W V : X.Etale} (a : W ⟶ V) : Etale a.left :=
  have : Etale W.hom := W.prop
  have : Etale (a.left ≫ V.hom) := by
    rw [MorphismProperty.Over.w a]
    infer_instance
  Etale.of_comp a.left V.hom

/-- **Vanishing of germs.** Let `t` be a geometric point, over the geometric point `s` of `X`,
of an étale `X`-scheme `V`. The germ at `t` of a section `z` of an étale sheaf `F` of
`Λ`-modules over `V` vanishes if and only if `z` restricts to zero on some étale `W ⟶ V` whose
image contains the image point of `t`. -/
lemma toPresheafFiber_eq_zero_iff {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {s : Spec (.of Ω) ⟶ X} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V : X.Etale} (t : (pointSmallEtale s).fiber.obj V) (z : F.obj.obj (op V)) :
    (pointSmallEtale s).toPresheafFiber V t F.obj z = 0 ↔
      ∃ (W : X.Etale) (a : W ⟶ V), t.left (default : Spec (.of Ω)) ∈ Set.range a.left ∧
        F.obj.map a.op z = 0 := by
  constructor
  · intro h
    rw [← map_zero ((pointSmallEtale s).toPresheafFiber V t F.obj).hom] at h
    obtain ⟨W, a, w, hw, hz⟩ := ((pointSmallEtale s).toPresheafFiber_eq_iff' V t z 0).1 h
    refine ⟨W, a, ⟨w.left (default : Spec (.of Ω)), ?_⟩, by simpa using hz⟩
    rw [← hw]
    rfl
  · rintro ⟨W, a, ⟨w, hw⟩, hz⟩
    have := etale_left a
    obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed a.left t.left w hw
    have hls : l ≫ W.hom = s := by
      rw [← MorphismProperty.Over.w a, ← Category.assoc, hl]
      exact Over.w t
    have ht : (pointSmallEtale s).fiber.map a (Over.homMk l hls) = t := by
      apply Over.OverMorphism.ext
      simpa [pointSmallEtale, Etale.forget] using hl
    rw [← ht, ← GrothendieckTopology.Point.toPresheafFiber_w_apply, hz, map_zero]

/-- Blueprint `lem-kun-support-geometric-point-independent`: **the support does not depend on
the chosen geometric point.** Two geometric points `s₁`, `s₂` of `X` with the same image point
have simultaneously vanishing stalks: a nonzero germ at `s₂` of a section `z` over `V` shows
that `z` does not vanish near the image point in `V`, so its germ at a lift of `s₁` to `V`
(which exists, `V ⟶ X` being étale) does not vanish either
(`AlgebraicGeometry.Etale.toPresheafFiber_eq_zero_iff`). -/
theorem isZero_sheafFiber_iff_of_apply_eq {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂] [IsSepClosed Ω₂]
    (s₁ : Spec (.of Ω₁) ⟶ X) (s₂ : Spec (.of Ω₂) ⟶ X)
    (h : s₁ default = s₂ default) :
    IsZero ((pointSmallEtale s₁).sheafFiber.obj F) ↔
      IsZero ((pointSmallEtale s₂).sheafFiber.obj F) := by
  suffices H : ∀ {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂]
      [IsSepClosed Ω₂] (s₁ : Spec (.of Ω₁) ⟶ X) (s₂ : Spec (.of Ω₂) ⟶ X),
      s₁ default = s₂ default →
        IsZero ((pointSmallEtale s₁).sheafFiber.obj F) →
          IsZero ((pointSmallEtale s₂).sheafFiber.obj F) from
    ⟨H s₁ s₂ h, H s₂ s₁ h.symm⟩
  intro Ω₁ Ω₂ _ _ _ _ s₁ s₂ h h₁
  suffices hp : ∀ p : ↥((pointSmallEtale s₂).sheafFiber.obj F), p = 0 by
    have : Subsingleton ↥((pointSmallEtale s₂).sheafFiber.obj F) :=
      ⟨fun p q ↦ by rw [hp p, hp q]⟩
    exact ModuleCat.isZero_of_subsingleton _
  intro p
  obtain ⟨V, t, z, rfl⟩ := (pointSmallEtale s₂).toPresheafFiber_jointly_surjective
    (P := F.obj) p
  have hV : V.hom (t.left (default : Spec (.of Ω₂))) = s₁ default := by
    rw [h]
    exact congrArg (fun f : Spec (.of Ω₂) ⟶ X ↦ f default) (Over.w t)
  obtain ⟨l, hl, hl'⟩ := exists_fac_of_etale_of_isSepClosed V.hom s₁ _ hV
  have h0 : (pointSmallEtale s₁).toPresheafFiber V (Over.homMk l hl) F.obj z = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 h₁).elim _ _
  obtain ⟨W, a, ⟨w, hw⟩, hz⟩ := (toPresheafFiber_eq_zero_iff F _ z).1 h0
  refine (toPresheafFiber_eq_zero_iff F t z).2 ⟨W, a, ⟨w, ?_⟩, hz⟩
  rw [hw, ← hl']
  rfl

end Etale

end AlgebraicGeometry
