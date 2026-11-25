/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
import WeilConjectures.SmoothPurity.PurityFiniteSetting.NormalizedIntegrationTensor

/-! # Counit tests for the ordinary direct-sum orientation square -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace WeilConjectures.PurityFiniteSetting.AffineOrdinaryIntegrationCoordinates

/-- Cancellation of the three orientation isomorphisms, before adjunction.
Source: composition proof Step 1, the last cancellation.
(blueprint: new-pur-affine-integration-ordinary-counit-calculus).
Proof: postcompose the forward square with the total inverse, then precompose by the
inverse source and coefficient comparisons. For the converse cancel the same maps. -/
theorem orientation_square_iff_inverse
    {C : Type*} [Category C] {U V W T : C}
    (a : U ≅ V) (m : V ≅ W) (o : T ≅ W) (s : U ⟶ T) :
    s ≫ o.hom = a.hom ≫ m.hom ↔ o.inv = m.inv ≫ a.inv ≫ s := by
  constructor
  · intro h
    have hh := congrArg (fun x ↦ m.inv ≫ a.inv ≫ x ≫ o.inv) h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using hh.symm
  · intro h
    have hh := congrArg (fun x ↦ a.hom ≫ m.hom ≫ x ≫ o.hom) h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using hh.symm

/-- An orientation square is equivalent to equality of the inverse maps after the actual
exceptional counit. No faithfulness of the exceptional left adjoint is assumed.
Source: composition proof Step 1, cancellation of the normalized integration isomorphisms.
(blueprint: new-pur-affine-integration-ordinary-counit-calculus).
Proof: the adjunction Hom equivalence detects equality of the inverse arrows. Precompose
by the two source isomorphisms and postcompose by the total orientation to recover the
forward square. Conversely cancel the same invertible maps in the forward square. -/
theorem orientation_square_iff_counit
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {U V W : C} {K : D} (a : U ≅ V) (m : V ≅ W) (o : R.obj K ≅ W)
    (s : U ⟶ R.obj K) :
    s ≫ o.hom = a.hom ≫ m.hom ↔
      L.map (m.inv ≫ a.inv ≫ s) ≫ adj.counit.app K =
        L.map o.inv ≫ adj.counit.app K := by
  constructor
  · intro h
    have hi : m.inv ≫ a.inv ≫ s = o.inv := by
      apply (cancel_mono o.hom).mp
      simp only [Category.assoc]
      rw [h]
      simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
    rw [hi]
  · intro h
    have hi : m.inv ≫ a.inv ≫ s = o.inv := adj.ext_of_comp_counit h
    have hh := congrArg (fun x ↦ a.hom ≫ m.hom ≫ x ≫ o.hom) hi
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using hh

/-- The actual conjugate of a compact-support compositor obeys the two-counit equation.
Source: composition proof Step 1, the exceptional map as the mate of compact support.
(blueprint: new-pur-affine-integration-ordinary-counit-calculus).
Proof: the inverse of the conjugate is the conjugate of the inverse compositor.
The defining counit equation for conjugation applies. Naturality of the compositor moves
an arbitrary source arrow through it; expand the actual composite adjunction counit. -/
theorem conjugate_composite_counit
    {X Y Z : Type*} [Category X] [Category Y] [Category Z]
    {Lq : X ⥤ Y} {Rq : Y ⥤ X} {Lp : Y ⥤ Z} {Rp : Z ⥤ Y}
    {Lh : X ⥤ Z} {Rh : Z ⥤ X}
    (aq : Lq ⊣ Rq) (ap : Lp ⊣ Rp) (ah : Lh ⊣ Rh)
    (c : Lq ⋙ Lp ≅ Lh) (M : X) (K : Z) (f : M ⟶ Rq.obj (Rp.obj K)) :
    Lh.map (f ≫ (conjugateIsoEquiv ah (aq.comp ap) c).inv.app K) ≫
        ah.counit.app K =
      c.inv.app M ≫ Lp.map (Lq.map f ≫ aq.counit.app (Rp.obj K)) ≫
        ap.counit.app K := by
  have hm := conjugateEquiv_counit (aq.comp ap) ah c.inv K
  change Lh.map ((conjugateIsoEquiv ah (aq.comp ap) c).inv.app K) ≫
      ah.counit.app K = c.inv.app _ ≫ (aq.comp ap).counit.app K at hm
  rw [Functor.map_comp, Category.assoc, hm]
  have hc := c.inv.naturality f
  change Lh.map f ≫ c.inv.app _ = c.inv.app M ≫ Lp.map (Lq.map f) at hc
  simp only [Functor.comp_obj]
  rw [← Category.assoc, hc]
  simp only [Adjunction.comp_counit_app, Functor.map_comp, Category.assoc]

/-- Counit of the ordered tensor of two integration adjuncts, with the actual
conjugate of the compact-support compositor. This is a formal calculation and contains
no smoothness or orientation compatibility hypothesis.
Source: composition proof Step 1, direct-sum integration and adjunction transposition.
(blueprint: new-pur-affine-integration-ordinary-counit-calculus).
Proof: extend the first unit adjunct to its normalized tensor family. Naturality moves
the second adjunct past this family. The defining counit equation for the tensor family
leaves inverse projection and the first scalar trace. The conjugate-compositor counit
law and the second scalar counit give precisely the displayed iterated integration. -/
theorem ordered_tensor_counit
    {X Y Z : Type*} [Category X] [Category Y] [Category Z]
    [MonoidalCategory X] [MonoidalCategory Y]
    {Lq : X ⥤ Y} {Rq Pq : Y ⥤ X} {Lp : Y ⥤ Z} {Rp : Z ⥤ Y}
    {Lh : X ⥤ Z} {Rh : Z ⥤ X}
    (aq : Lq ⊣ Rq) (ap : Lp ⊣ Rp) (ah : Lh ⊣ Rh)
    (c : Lq ⋙ Lp ≅ Lh)
    (π : ∀ M : X, tensorLeft (Lq.obj M) ⟶ (Pq ⋙ tensorLeft M) ⋙ Lq)
    [∀ M, IsIso (π M)]
    (np : ∀ {M M' : X} (f : M ⟶ M') (K : Y),
      Lq.map f ▷ K ≫ (π M').app K = (π M).app K ≫ Lq.map (f ▷ Pq.obj K))
    {M Wq : X} {Wp : Y} {K : Z}
    (n : M ⟶ Wq ⊗ Pq.obj Wp)
    (ωq : Wq ⟶ Rq.obj (𝟙_ Y)) (ωp : Wp ⟶ Rp.obj K) :
    Lh.map (n ≫ (ωq ▷ Pq.obj Wp) ≫ (Rq.obj (𝟙_ Y) ◁ Pq.map ωp) ≫
        aq.projectionTensorMap (fun M K ↦ (π M).app K) (𝟙_ Y) (Rp.obj K) ≫
        Rq.map (λ_ (Rp.obj K)).hom ≫
        (conjugateIsoEquiv ah (aq.comp ap) c).inv.app K) ≫ ah.counit.app K =
      c.inv.app M ≫ Lp.map (Lq.map n ≫ inv ((π Wq).app Wp) ≫
        (Lq.map ωq ≫ aq.counit.app (𝟙_ Y)) ▷ Wp ≫ (λ_ Wp).hom) ≫
        (Lp.map ωp ≫ ap.counit.app K) := by
  obtain ⟨σ, hs, hn⟩ := normalizedIntegration_tensor Lq Rq Pq aq π np Wq ωq
  have hσ := σ.naturality ωp
  change (Wq ◁ Pq.map ωp) ≫ σ.app (Rp.obj K) = σ.app Wp ≫ Rq.map ωp at hσ
  have he : (ωq ▷ Pq.obj Wp) ≫ (Rq.obj (𝟙_ Y) ◁ Pq.map ωp) ≫
        aq.projectionTensorMap (fun M K ↦ (π M).app K) (𝟙_ Y) (Rp.obj K) ≫
        Rq.map (λ_ (Rp.obj K)).hom =
      σ.app Wp ≫ Rq.map ωp := by
    calc
      _ = (Wq ◁ Pq.map ωp) ≫ ((ωq ▷ Pq.obj (Rp.obj K)) ≫
          aq.projectionTensorMap (fun M K ↦ (π M).app K) (𝟙_ Y) (Rp.obj K) ≫
          Rq.map (λ_ (Rp.obj K)).hom) := by
        rw [← Category.assoc, ← whisker_exchange]
        simp only [Category.assoc]
      _ = _ := by rw [← hs, hσ]
  rw [reassoc_of% he]
  rw [show n ≫ σ.app Wp ≫ Rq.map ωp ≫
      (conjugateIsoEquiv ah (aq.comp ap) c).inv.app K =
      (n ≫ σ.app Wp ≫ Rq.map ωp) ≫
        (conjugateIsoEquiv ah (aq.comp ap) c).inv.app K by simp only [Category.assoc]]
  rw [conjugate_composite_counit aq ap ah c]
  have hε := aq.counit.naturality ωp
  change Lq.map (Rq.map ωp) ≫ aq.counit.app (Rp.obj K) =
    aq.counit.app Wp ≫ ωp at hε
  have ht : Lq.map (n ≫ σ.app Wp ≫ Rq.map ωp) ≫ aq.counit.app (Rp.obj K) =
      (Lq.map n ≫ inv ((π Wq).app Wp) ≫
        (Lq.map ωq ≫ aq.counit.app (𝟙_ Y)) ▷ Wp ≫ (λ_ Wp).hom) ≫ ωp := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hε]
    rw [← Category.assoc (Lq.map (σ.app Wp)), hn]
    simp only [Category.assoc]
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]

end WeilConjectures.PurityFiniteSetting.AffineOrdinaryIntegrationCoordinates
