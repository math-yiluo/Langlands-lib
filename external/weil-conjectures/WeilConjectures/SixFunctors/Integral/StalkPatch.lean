/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FibreTopology
public import WeilConjectures.SixFunctors.Integral.StalkInjective

/-!
# Patching germs of a direct image along an integral morphism

Let `f : X ⟶ Y` be an integral morphism, `y` a geometric point of `Y` with algebraically closed
residue field and `(U₀, u₀)` an affine pointed étale neighbourhood of `y`. Given finitely many
germs `a i` of `f_* G` at `y` and a decomposition `m` of the geometric fibre of `f` over `y`
which only depends on the values of `(u₀, t)` on finitely many functions on `U₀ ×_Y X`, there is
a germ of `f_* G` at `y` whose restriction to every geometric point `t` over `y` is that of
`a (m t)` (`AlgebraicGeometry.Etale.exists_stalkRestrict_eq_of_finset`): after shrinking the
neighbourhood, `U ×_Y X` decomposes into disjoint opens adapted to `m`
(`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_disjoint_cover`), and the representatives of
the `a i` glue along this decomposition.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme Scheme.Hom

namespace Scheme.Hom.Nbhd

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] {y : Spec (.of Ω) ⟶ Y}

/-- Every pointed étale neighbourhood is refined by one with affine underlying scheme. -/
lemma exists_hom_isAffine (c : Nbhd y) : ∃ (c' : Nbhd y) (_ : c' ⟶ c), IsAffine c'.1.left := by
  obtain ⟨U₁, hU₁, hu, -⟩ := exists_isAffineOpen_mem_and_subset (X := c.1.left)
    (x := c.2.left (default : Spec (.of Ω))) (U := ⊤) trivial
  exact ⟨c.restrict U₁ hu, c.restrictHom U₁ hu, hU₁⟩

end Scheme.Hom.Nbhd

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

/-- **Patching germs of a direct image along an integral morphism.** Let `(U₀, u₀)` be an affine
pointed étale neighbourhood of `y` and `m` a map from the geometric fibre of `f` over `y` to
`Fin n` which only depends on the values of the points `(u₀, t)` on a finite set `S` of
functions on `U₀ ×_Y X`. For germs `a i` of `f_* G` at `y` there is a germ of `f_* G` at `y`
whose restriction to every geometric point `t` of `X` over `y` is that of `a (m t)`. -/
theorem Etale.exists_stalkRestrict_eq_of_finset {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {y : Spec (.of Ω) ⟶ Y} (c₀ : Nbhd y) [IsAffine c₀.1.left]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {n : ℕ}
    (a : Fin n → ToType ((pointSmallEtale y).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj G)))
    (m : f.GeometricFiber y → Fin n) (S : Finset Γ(pullback c₀.1.hom f, ⊤))
    (hm : ∀ t₁ t₂, (∀ b ∈ S, (basePt f c₀ t₁).appTopPoint b = (basePt f c₀ t₂).appTopPoint b) →
      m t₁ = m t₂) :
    ∃ a₀, ∀ t, Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t G a₀ =
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t G (a (m t)) := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  -- representatives of the germs `a i`
  have hrep (i : Fin n) : ∃ (c : Nbhd y)
      (σ : ToType (((f)_*[ModuleCat.{u + 1} Λ].obj G).obj.obj (op c.1))),
      (pointSmallEtale y).toPresheafFiber c.1 c.2 ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj σ =
        a i := by
    obtain ⟨V, v, σ, hσ⟩ := (pointSmallEtale y).toPresheafFiber_jointly_surjective
      (P := ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj) (a i)
    exact ⟨Functor.elementsMk _ V v, σ, hσ⟩
  choose cs σs hσs using hrep
  -- a common affine refinement of `c₀` and the `cs i`
  obtain ⟨c₁, hc₁⟩ := IsCofiltered.inf_objs_exists (insert c₀ (Finset.univ.image cs))
  obtain ⟨c₂, h₂₁, hc₂⟩ := Nbhd.exists_hom_isAffine c₁
  have h₁₀ : c₁ ⟶ c₀ := (hc₁ (Finset.mem_insert_self _ _)).some
  have h₁ (i : Fin n) : c₁ ⟶ cs i :=
    (hc₁ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))).some
  -- the decomposition `m` in terms of `c₂`
  let B₂ := Γ(pullback c₂.1.hom f, ⊤)
  let r : Γ(pullback c₀.1.hom f, ⊤) →+* B₂ := (f.Etale.map (h₂₁ ≫ h₁₀).val).left.appTop.hom
  have hr (t : f.GeometricFiber y) (b : Γ(pullback c₀.1.hom f, ⊤)) :
      (basePt f c₀ t).appTopPoint b = (basePt f c₂ t).appTopPoint (r b) := by
    rw [← basePt_comp_etale_map_left f (h₂₁ ≫ h₁₀) t, Scheme.Hom.appTopPoint_comp]
    rfl
  let P : Fin n → StandardEtalePair B₂ := fun _ ↦ StandardEtalePair.trivialPair B₂
  let χ : ∀ j, {t // m t = j} → ((P j).Ring →+* Ω) := fun _ t ↦
    (StandardEtalePair.trivialPair B₂).liftOfRingHom (basePt f c₂ t.1).appTopPoint 0
      (StandardEtalePair.trivialPair_eval₂ _)
  obtain ⟨c, h, ι, Q, k, ν, hdisj, hsup, -, hpt⟩ :=
    Nbhd.exists_pointed_disjoint_cover f c₂ P m (Set.toFinite _) χ
      (fun _ _ ↦ StandardEtalePair.liftOfRingHom_comp_algebraMap _ _ _ _)
      ⟨S.image r, fun t₁ t₂ ht ↦ hm t₁ t₂ fun b hb ↦ by
        rw [hr, hr]
        exact ht _ (Finset.mem_image_of_mem _ hb)⟩
      (fun j ζ ↦ by
        obtain ⟨S', hS'⟩ := (StandardEtalePair.trivialPair B₂).exists_finset_liftOfRingHom_eq
          (0 : Ω) ζ
        exact ⟨S', fun t₁ t₂ ht ↦ hS' _ _ _ _ ht⟩)
  -- the sections over the pieces, and their gluing
  let g (i : Fin n) : c ⟶ cs i := h ≫ h₂₁ ≫ h₁ i
  let π (l : ι) := Nbhd.openIncl f c (Q l)
  let τ (l : ι) : ToType (G.obj.obj (op (Nbhd.openObj f c (Q l)))) :=
    G.obj.map (π l ≫ f.Etale.map (g (k l)).val).op (σs (k l))
  let F := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G
  have hcov : Sieve.ofArrows _ π ∈ X.smallEtaleTopology _ := by
    rw [ofArrows_mem_smallEtaleTopology_iff, Set.eq_univ_iff_forall]
    intro w
    have : w ∈ (⨆ l, Q l) := hsup ▸ trivial
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine Set.mem_iUnion.mpr ⟨l, ?_⟩
    change w ∈ Set.range (Q l).ι
    rw [Scheme.Opens.range_ι]
    exact hl
  have hdisj' : ∀ i j, i ≠ j →
      Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base) := by
    intro i j hij
    change Disjoint (Set.range (Q i).ι.base) (Set.range (Q j).ι.base)
    simp only [Scheme.Opens.range_ι]
    rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Opens.coe_inf,
      (hdisj i j hij).eq_bot, TopologicalSpace.Opens.coe_bot]
  obtain ⟨b, hb, -⟩ := F.property.existsUnique_amalgamation_ofArrows π hcov (E := PUnit)
    (fun l ↦ TypeCat.ofHom fun _ ↦ τ l) (Etale.comp_map_eq_of_disjoint F _ π hdisj' _)
  refine ⟨(pointSmallEtale y).toPresheafFiber c.1 c.2 ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj
    (b PUnit.unit), fun t ↦ ?_⟩
  -- the restriction to `t` is computed on the piece containing `(u, t)`
  have hmem : basePt f c t default ∈ (⨆ l, Q l) := hsup ▸ trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  have hrange : Set.range (basePt f c t).base ⊆ Set.range (Q l).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of Ω)) p default]
    exact hl
  let q := IsOpenImmersion.lift (Q l).ι (basePt f c t) hrange
  have hq : q ≫ (Q l).ι = basePt f c t := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e, -⟩ := hpt t l q hq
  let ptQ : (pointSmallEtale t.1).fiber.obj (Nbhd.openObj f c (Q l)) :=
    CategoryTheory.Over.homMk q (by
      change q ≫ (Q l).ι ≫ pullback.snd c.1.hom f = t.1
      rw [← Category.assoc, hq, basePt_snd])
  have hbl := congrArg (fun φ ↦ φ PUnit.unit) (hb l)
  change G.obj.map (π l).op (b PUnit.unit) = τ l at hbl
  have hpt₁ : (pointSmallEtale t.1).fiber.map (π l) ptQ =
      ((Etale.baseChangeNbhd f y t).obj c).2 :=
    CategoryTheory.Over.OverMorphism.ext hq
  have hpt₂ : (pointSmallEtale t.1).fiber.map (π l ≫ f.Etale.map (g (k l)).val) ptQ =
      ((Etale.baseChangeNbhd f y t).obj (cs (k l))).2 := by
    refine CategoryTheory.Over.OverMorphism.ext ?_
    change q ≫ (Q l).ι ≫ (f.Etale.map (g (k l)).val).left = basePt f (cs (k l)) t
    rw [← Category.assoc, hq, basePt_comp_etale_map_left]
  have e₁ : Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t G
      ((pointSmallEtale y).toPresheafFiber c.1 c.2 ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj
        (b PUnit.unit)) =
      (pointSmallEtale t.1).toPresheafFiber _ ((Etale.baseChangeNbhd f y t).obj c).2 G.obj
        (b PUnit.unit) :=
    ConcreteCategory.congr_hom
      (Etale.toPresheafFiber_stalkRestrict (ModuleCat.{u + 1} Λ) f y t G c) _
  have e₂ : Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t G (a (k l)) =
      (pointSmallEtale t.1).toPresheafFiber _ ((Etale.baseChangeNbhd f y t).obj (cs (k l))).2
        G.obj (σs (k l)) := by
    rw [← hσs (k l)]
    exact ConcreteCategory.congr_hom
      (Etale.toPresheafFiber_stalkRestrict (ModuleCat.{u + 1} Λ) f y t G (cs (k l))) _
  rw [e, e₁, e₂, ← hpt₁, ← hpt₂]
  have w₁ := (pointSmallEtale t.1).toPresheafFiber_w_apply (π l) ptQ G.obj (b PUnit.unit)
  have w₂ := (pointSmallEtale t.1).toPresheafFiber_w_apply (π l ≫ f.Etale.map (g (k l)).val)
    ptQ G.obj (σs (k l))
  exact w₁.symm.trans ((congrArg _ hbl).trans w₂)

end AlgebraicGeometry
