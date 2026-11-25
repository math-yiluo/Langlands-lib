/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.SixFunctors.Integral.StalkRestrict

/-!
# The restrictions of germs of a direct image along an integral morphism are jointly injective

For a section `σ` of an étale sheaf `G` over an étale `X`-scheme `W`, the points of `W` near
which `σ` vanishes form an open subset `AlgebraicGeometry.Etale.vanishingSet` of `W`, and the
germ of `σ` at a geometric point of `W` vanishes exactly when the point lies in this open
subset (`AlgebraicGeometry.Etale.toPresheafFiber_eq_zero_iff_mem_vanishingSet`).

Let `f : X ⟶ Y` be an integral morphism and `y` a geometric point of `Y` with algebraically
closed residue field. A germ of `f_* G` at `y` all of whose restrictions to the geometric points
of `X` over `y` vanish is zero
(`AlgebraicGeometry.Etale.eq_zero_of_forall_stalkRestrict_eq_zero`): the germ is a section `σ`
of `G` over `U ×_Y X`, the closed complement of the vanishing set of `σ` contains no point
`(u, t)`, so it disappears over a smaller pointed étale neighbourhood of `y`
(`AlgebraicGeometry.Scheme.Hom.exists_hom_preimage_eq_bot_of_isIntegralHom`), on which `σ`
vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme Scheme.Hom

section Vanishing

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
  (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {W : X.Etale}
  (σ : ToType (G.obj.obj (op W)))

/-- The sieve of the morphisms to `W` on which the section `σ` vanishes. -/
def Etale.vanishingSieve : Sieve W where
  arrows _ m := G.obj.map m.op σ = 0
  downward_closed {_ _} m hm h := by
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    change G.obj.map h.op (G.obj.map m.op σ) = 0
    rw [hm, map_zero]

lemma Etale.vanishingSieve_apply {V : X.Etale} (m : V ⟶ W) :
    Etale.vanishingSieve Λ G σ m ↔ G.obj.map m.op σ = 0 :=
  Iff.rfl

/-- The set of points of `W` near which the section `σ` vanishes. -/
def Etale.vanishingSet : Set W.left :=
  ⋃ (V : X.Etale) (m : V ⟶ W) (_ : Etale.vanishingSieve Λ G σ m), Set.range m.left

lemma Etale.mem_vanishingSet_iff (w : W.left) :
    w ∈ Etale.vanishingSet Λ G σ ↔
      ∃ (V : X.Etale) (m : V ⟶ W) (v : V.left), G.obj.map m.op σ = 0 ∧ m.left v = w := by
  simp only [Etale.vanishingSet, Set.mem_iUnion, Set.mem_range]
  exact ⟨fun ⟨V, m, hm, v, hv⟩ ↦ ⟨V, m, v, hm, hv⟩, fun ⟨V, m, v, hm, hv⟩ ↦ ⟨V, m, hm, v, hv⟩⟩

/-- The vanishing set of a section is open: étale morphisms are open. -/
lemma Etale.isOpen_vanishingSet : IsOpen (Etale.vanishingSet Λ G σ) :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun m ↦ isOpen_iUnion fun _ ↦
    m.left.isOpenMap.isOpen_range

/-- **The germ of a section at a geometric point vanishes exactly when the point lies in the
vanishing set of the section.** -/
lemma Etale.toPresheafFiber_eq_zero_iff_mem_vanishingSet {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) (w : (pointSmallEtale x).fiber.obj W) :
    (pointSmallEtale x).toPresheafFiber W w G.obj σ = 0 ↔
      w.left (default : Spec (.of Ω)) ∈ Etale.vanishingSet Λ G σ := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have h0 : (pointSmallEtale x).toPresheafFiber W w G.obj 0 = 0 := map_zero _
  rw [← h0, GrothendieckTopology.Point.toPresheafFiber_eq_iff', Etale.mem_vanishingSet_iff]
  constructor
  · rintro ⟨V, m, v, hv, hm⟩
    refine ⟨V, m, v.left (default : Spec (.of Ω)), ?_, ?_⟩
    · rw [hm, map_zero]
    · rw [← hv]
      rfl
  · rintro ⟨V, m, z, hm, hz⟩
    obtain ⟨l, hl, hlz⟩ := exists_fac_of_etale_of_isSepClosed m.left w.left z hz
    refine ⟨V, m, CategoryTheory.Over.homMk l ?_, ?_, ?_⟩
    · change l ≫ V.hom = x
      rw [← MorphismProperty.Over.w m, ← Category.assoc, hl]
      exact CategoryTheory.Over.w w
    · exact CategoryTheory.Over.OverMorphism.ext hl
    · rw [hm, map_zero]

end Vanishing

section Injective

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

/-- **The restrictions of germs of a direct image along an integral morphism are jointly
injective**: a germ of `f_* G` at a geometric point `y` of `Y` with algebraically closed residue
field is zero as soon as its restrictions to all geometric points of `X` over `y` vanish. -/
lemma Etale.eq_zero_of_forall_stalkRestrict_eq_zero {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : ToType ((pointSmallEtale y).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj G)))
    (ha : ∀ t : f.GeometricFiber y, Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t G a = 0) :
    a = 0 := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨V, v, σ, rfl⟩ := (pointSmallEtale y).toPresheafFiber_jointly_surjective
    (P := ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj) a
  let c : Nbhd y := Functor.elementsMk _ V v
  let σ' : ToType (G.obj.obj (op (f.Etale.obj c.1))) := σ
  -- the germs of `σ` at the points `(u, t)` vanish
  have hσ (t : f.GeometricFiber y) : basePt f c t default ∈ Etale.vanishingSet Λ G σ' := by
    have h : Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t G
        ((pointSmallEtale y).toPresheafFiber c.1 c.2 ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj σ) =
        (pointSmallEtale t.1).toPresheafFiber _ ((Etale.baseChangeNbhd f y t).obj c).2 G.obj σ' :=
      ConcreteCategory.congr_hom
        (Etale.toPresheafFiber_stalkRestrict (ModuleCat.{u + 1} Λ) f y t G c) σ
    exact (Etale.toPresheafFiber_eq_zero_iff_mem_vanishingSet Λ G σ' t.1 _).1 (h ▸ ha t)
  -- so `σ` vanishes over a smaller pointed étale neighbourhood of `y`
  obtain ⟨c', g, hg⟩ := exists_hom_preimage_eq_bot_of_isIntegralHom f c
    (Etale.vanishingSet Λ G σ')ᶜ (Etale.isOpen_vanishingSet Λ G σ').isClosed_compl
    fun t ht ↦ ht (hσ t)
  let F := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G
  have hR : (Etale.vanishingSieve Λ G σ').pullback (f.Etale.map g.val) ∈
      X.smallEtaleTopology _ := by
    refine (Scheme.mem_smallEtaleTopology_iff _).2 fun z ↦ ?_
    have hz : (f.Etale.map g.val).left z ∈ Etale.vanishingSet Λ G σ' := by
      by_contra hc
      have : z ∈ (f.Etale.map g.val).left.base ⁻¹' (Etale.vanishingSet Λ G σ')ᶜ := hc
      rw [hg] at this
      exact this
    obtain ⟨V', m, z', hm, hz'⟩ := (Etale.mem_vanishingSet_iff Λ G σ' _).1 hz
    obtain ⟨Z, p₁, p₂, z'', hcomm, hp₁, -⟩ := exists_eq_of_apply_eq (f.Etale.map g.val) m z z'
      hz'.symm
    refine ⟨Z, p₁, ?_, z'', hp₁⟩
    change Etale.vanishingSieve Λ G σ' (p₁ ≫ f.Etale.map g.val)
    rw [hcomm]
    exact (Etale.vanishingSieve Λ G σ').downward_closed hm p₂
  have hzero : G.obj.map (f.Etale.map g.val).op σ' = 0 := by
    have hsep := (((isSheaf_iff_isSheaf_of_type _ _).1 F.property) _ hR).isSeparatedFor
    refine hsep.ext fun Z p hp ↦ ?_
    change G.obj.map p.op (G.obj.map (f.Etale.map g.val).op σ') = G.obj.map p.op 0
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact hp
  have h₂ := (pointSmallEtale y).toPresheafFiber_w_apply g.val c'.2
    ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj σ
  rw [Functor.Elements.Hom.val, g.map_val] at h₂
  rw [← h₂]
  change (pointSmallEtale y).toPresheafFiber c'.1 c'.2 ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj
    (G.obj.map (f.Etale.map g.val).op σ') = 0
  rw [hzero, map_zero]

end Injective

end AlgebraicGeometry
