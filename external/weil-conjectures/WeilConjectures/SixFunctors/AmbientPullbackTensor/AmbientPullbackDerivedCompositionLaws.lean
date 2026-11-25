/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackOrdinaryCompositionLaws
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Derived pullback associativity and unit laws.

Source: Stacks 015F and 04VG.
(blueprint: new-lem-sf-ambient-pullback-derived-composition-laws).

This is the exact-localization part of the ambient pullback coherence argument.
The ordinary equations are preserved by the exact termwise functors and their
localizations; the resulting three equations are recorded here separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections

private theorem derivedPostcompose
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Abelian C] [Abelian D] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]
    {F : C ⥤ D} {G : D ⥤ B} {H H' : C ⥤ B}
    [F.Additive] [G.Additive] [H.Additive] [H'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (γ : F ⋙ G ≅ H) (e : H ≅ H') :
    Functor.mapDerivedCategoryCompNatIso (γ ≪≫ e) =
      Functor.mapDerivedCategoryCompNatIso γ ≪≫ Functor.mapDerivedCategoryNatIso e := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom,
    Functor.mapDerivedCategoryNatIso_trans, Category.assoc]

private theorem derivedTransport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {A : Type*} (F : A → C ⥤ D) [∀ a, (F a).Additive]
    [∀ a, PreservesFiniteLimits (F a)] [∀ a, PreservesFiniteColimits (F a)]
    {a b : A} (h : a = b) :
    Functor.mapDerivedCategoryNatIso (eqToIso (congrArg F h)) =
      eqToIso (congrArg (fun x ↦ (F x).mapDerivedCategory) h) := by
  subst b
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem derivedInnerUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : C ⥤ C) (F H : C ⥤ D)
    [I.Additive] [F.Additive] [H.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : I ⋙ F ≅ H) (e : I ≅ 𝟭 C) (q : H ≅ F)
    (hc : ∀ M, c.hom.app M ≫ q.hom.app M = F.map (e.hom.app M))
    (M : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompNatIso c).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso q).hom.app M =
      F.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app M) := by
  have hi : c ≪≫ q = Functor.isoWhiskerRight e F := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    exact hc M
  have hd := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app M) hi
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hd
  have hw := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hw
  have hu := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hu
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso I F).inv.app M)).mp
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom,
    NatTrans.comp_app, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [hd, Functor.map_comp]
  rw [← Category.assoc, ← hw, Category.assoc, hu]
  erw [Category.comp_id]

private theorem derivedOuterUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : D ⥤ D) (F H : C ⥤ D)
    [I.Additive] [F.Additive] [H.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : F ⋙ I ≅ H) (e : I ≅ 𝟭 D) (q : H ≅ F)
    (hc : ∀ M, c.hom.app M ≫ q.hom.app M = e.hom.app (F.obj M))
    (M : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompNatIso c).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso q).hom.app M =
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
        (F.mapDerivedCategory.obj M) := by
  have hi : c ≪≫ q = Functor.isoWhiskerLeft F e := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    exact hc M
  have hd := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app M) hi
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hd
  have hw := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hw
  have hu := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hu
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F I).inv.app M)).mp
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom,
    NatTrans.comp_app, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [hd, ← hw, Category.assoc, hu]
  erw [Category.comp_id]

namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Derived associativity and unit laws for the ambient pullback comparisons.
Source: Stacks 015F and 04VG.
(blueprint: new-lem-sf-ambient-pullback-derived-composition-laws).
Proof: apply the exact termwise pullback functors to the ordinary equations,
then use the localization universal property and the specified factorization
isomorphisms.  This preserves composition, identities and all endpoint
transports, giving the three displayed derived clauses. -/
theorem derived_pullback_compositionLaws (K : Scheme.{t}) (s : Option ℕ) :
    (∀ {W X Y Z : Scheme.{t}} (w : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
      (aW : W ⟶ K) (aX : X ⟶ K) (aY : Y ⟶ K) (aZ : Z ⟶ K)
      [LocallyOfFiniteType aW] [QuasiCompact aW] [LocallyOfFiniteType aX]
      [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
      [LocallyOfFiniteType aZ] [QuasiCompact aZ]
      (_hw : w ≫ aX = aW) (_hf : f ≫ aY = aX) (_hg : g ≫ aZ = aY)
      (M : Derived ell E Z s),
      (derivedPull ell E w s).map ((derivedComp ell E f g s).hom.app M) ≫
          (derivedComp ell E w (f ≫ g) s).hom.app M =
        (derivedComp ell E w f s).hom.app ((derivedPull ell E g s).obj M) ≫
          (derivedComp ell E (w ≫ f) g s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (derivedPull ell E a s).obj M)
            (Category.assoc w f g))) ∧
    (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Derived ell E Y s),
      (derivedPull ell E f s).map ((derivedIdentity ell E Y s).hom.app M) =
        (derivedComp ell E f (𝟙 Y) s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (derivedPull ell E a s).obj M)
            (Category.comp_id f))) ∧
    (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Derived ell E Y s),
      (derivedIdentity ell E X s).hom.app ((derivedPull ell E f s).obj M) =
        (derivedComp ell E (𝟙 X) f s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (derivedPull ell E a s).obj M)
            (Category.id_comp f))) := by
  obtain ⟨ha, hr, hl⟩ := ordinary_pullback_compositionLaws ell E K s
  refine ⟨?_, ?_, ?_⟩
  · intro W X Y Z w f g aW aX aY aZ _ _ _ _ _ _ _ _ hw hf hg M
    have h := Functor.mapDerivedCategoryCompNatIso_cocycle
      (comp ell E f g s) (comp ell E w (f ≫ g) s) (comp ell E w f s)
      (comp ell E (w ≫ f) g s ≪≫
        eqToIso (congrArg (fun a ↦ pull ell E a s) (Category.assoc w f g)))
      (fun N ↦ ha w f g aW aX aY aZ hw hf hg N) M
    rw [derivedPostcompose,
      derivedTransport (fun a ↦ pull ell E a s) (Category.assoc w f g)] at h
    simpa only [derivedComp, derivedPull, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app] using h
  · intro X Y f aX aY _ _ _ _ hf M
    have h := derivedInnerUnit (pull ell E (𝟙 Y) s) (pull ell E f s)
      (pull ell E (f ≫ 𝟙 Y) s) (comp ell E f (𝟙 Y) s) (identity ell E Y s)
      (eqToIso (congrArg (fun a ↦ pull ell E a s) (Category.comp_id f)))
      (fun N ↦ (hr f aX aY hf N).symm) M
    rw [derivedTransport (fun a ↦ pull ell E a s) (Category.comp_id f)] at h
    simpa only [derivedComp, derivedIdentity, derivedPull, eqToIso.hom, eqToHom_app] using h.symm
  · intro X Y f aX aY _ _ _ _ hf M
    have h := derivedOuterUnit (pull ell E (𝟙 X) s) (pull ell E f s)
      (pull ell E (𝟙 X ≫ f) s) (comp ell E (𝟙 X) f s) (identity ell E X s)
      (eqToIso (congrArg (fun a ↦ pull ell E a s) (Category.id_comp f)))
      (fun N ↦ (hl f aX aY hf N).symm) M
    rw [derivedTransport (fun a ↦ pull ell E a s) (Category.id_comp f)] at h
    simpa only [derivedComp, derivedIdentity, derivedPull, eqToIso.hom, eqToHom_app] using h.symm

end WeilConjectures.AmbientPullbackTensor
