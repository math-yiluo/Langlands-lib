/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Pullbacks along a quasi-compact jointly surjective family detect sections

Let `g k : Z k ⟶ U`, for `k` in a finite type, be quasi-compact morphisms of schemes jointly
covering `U`, for instance the immersions of the strata of a finite stratification of a
Noetherian scheme. For a sheaf of modules `F` on the small pro-étale site of `U`, a section of
`F` whose restrictions to all the pullbacks `(g k)^* F` vanish is zero
(`AlgebraicGeometry.ProEtale.eq_zero_of_forall_unit_app_eq_zero`).

The pullback `g^* F` is the sheafification of the left Kan extension of `F` along the opposite
of the base change functor `V ↦ V ×_U Z`, which is representably flat. If the restriction of a
section `s` over `V` vanishes, then, sheafification being locally injective, it vanishes locally
in the left Kan extension, a filtered colimit
(`CategoryTheory.Functor.exists_map_eq_of_leftKanExtensionUnit_eq`). So the members of a
pro-étale cover of `V ×_U Z` factor through base changes `V' ×_U Z` of morphisms `V' ⟶ V` of
the pro-étale site along which `s` vanishes
(`AlgebraicGeometry.ProEtale.exists_mem_precoverage_map_eq_zero`). For the finitely many
quasi-compact `g k` jointly covering `U`, these `V'` form a pro-étale cover of `V`
(`AlgebraicGeometry.QuasiCompactCover.of_comp_factor`), on which `s` vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (R : Type (u + 1)) [Ring R] {U Z : Scheme.{u}} (g : Z ⟶ U)

/-- The forgetful functor of modules preserves the colimits computing the left Kan extension
along the opposite of base change: they are filtered, base change being representably flat. -/
instance preservesColimitsOfShape_costructuredArrow_overPullback (Y) : PreservesColimitsOfShape
    (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op Y)
    (forget (ModuleCat.{u + 1} R)) := by
  have : IsFiltered (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op Y) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ Y.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  infer_instance

variable {R} (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))

/-- **Local vanishing.** If the image of a section `s` of `F` over `V` under the unit
`F ⟶ g_* g^* F` vanishes, then there is a pro-étale cover of `V ×_U Z` each of whose members
factors through the base change `V' ×_U Z` of a morphism `f : V' ⟶ V` of the pro-étale site
with `s|_{V'} = 0`. -/
lemma exists_mem_precoverage_map_eq_zero {V : U.ProEt} (s : ToType (F.obj.obj (op V)))
    (hs : ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).unit.app F).hom.app (op V) s =
      0) :
    ∃ P ∈ Scheme.ProEt.precoverage Z ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V),
      ∀ ⦃T⦄ (φ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V), P φ →
        ∃ (V' : U.ProEt) (f : V' ⟶ V)
          (ψ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V'),
          ψ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f = φ ∧
            F.obj.map f.op s = 0 := by
  set G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
  have hunit : ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).unit.app F).hom.app
      (op V) = (G.op.leftKanExtensionUnit F.obj).app (op V) ≫
        (toSheafify _ (G.op.leftKanExtension F.obj)).app (op (G.obj V)) := rfl
  rw [hunit, ConcreteCategory.comp_apply] at hs
  have hS := Presheaf.equalizerSieve_mem (Scheme.ProEt.topology Z)
    (toSheafify (Scheme.ProEt.topology Z) (G.op.leftKanExtension F.obj)) (X := op (G.obj V))
      ((G.op.leftKanExtensionUnit F.obj).app (op V) s) 0
      (hs.trans (map_zero _).symm)
  obtain ⟨P, hP, hle⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  refine ⟨P, hP, fun T φ hφ ↦ ?_⟩
  have h₁ := hle _ _ hφ
  obtain ⟨V', f, ψ, hψ, h⟩ := Functor.exists_map_eq_of_leftKanExtensionUnit_eq G F.obj φ s 0
    (by simpa using h₁)
  exact ⟨V', f, ψ, hψ, by simpa using h⟩

variable (R) in
/-- **Restrictions along a quasi-compact jointly surjective family detect sections.** Let
`g k : Z k ⟶ U` be finitely many quasi-compact morphisms jointly covering `U`. A section `s` of
a pro-étale sheaf of modules `F` on `U` whose images under the units `F ⟶ (g k)_* (g k)^* F` all
vanish is zero: `s` vanishes on weakly étale neighbourhoods of the points of every
`V ×_U Z k` (`AlgebraicGeometry.ProEtale.exists_mem_precoverage_map_eq_zero`), and these
neighbourhoods form a pro-étale cover of `V`
(`AlgebraicGeometry.QuasiCompactCover.of_comp_factor`). -/
theorem eq_zero_of_forall_unit_app_eq_zero {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}}
    (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R)) {V : U.ProEt}
    (s : ToType (F.obj.obj (op V)))
    (hs : ∀ k, ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (g k)).unit.app F).hom.app
      (op V) s = 0) :
    s = 0 := by
  choose P hP hPs using fun k ↦ exists_mem_precoverage_map_eq_zero (g k) F s (hs k)
  choose ι T φ hTφ using fun k ↦ (P k).exists_eq_ofArrows
  choose V' f ψ hψ hf using fun (p : Σ k, ι k) ↦
    hPs p.1 (φ p.1 p.2) (by rw [hTφ p.1]; exact .mk p.2)
  let D : PreZeroHypercover V.left := ⟨Σ k, ι k, fun p ↦ (V' p).left, fun p ↦ (f p).left⟩
  let E (k : κ) : PreZeroHypercover
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (g k)).obj V).left :=
    ⟨ι k, fun m ↦ (T k m).left, fun m ↦ (φ k m).left⟩
  have hE (k : κ) : (E k).presieve₀ ∈ Scheme.proetalePrecoverage _ := by
    have := hP k
    rw [hTφ k, Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at this
    exact this
  have : ∀ k, QuasiCompactCover (E k) := fun k ↦
    Scheme.presieve₀_mem_qcPrecoverage_iff.1 (hE k).1
  have hD : QuasiCompactCover D := by
    refine QuasiCompactCover.of_comp_factor (fun k ↦ pullback.fst V.hom (g k)) (fun x ↦ ?_) E D
      (fun k m ↦ ⟨k, m⟩) (fun k m ↦ (ψ ⟨k, m⟩).left ≫ pullback.fst _ _) fun k m ↦ ?_
    · obtain ⟨k, z, hz⟩ := hg (V.hom x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
      exact ⟨k, w, hw⟩
    · have := congrArg (fun a ↦ a.left ≫ pullback.fst V.hom (g k)) (hψ ⟨k, m⟩)
      simpa using this
  have hDmem : D.presieve₀ ∈ Scheme.proetalePrecoverage V.left := by
    refine ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hD, ?_⟩
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2 ⟨fun x ↦ ?_, fun p ↦ ?_⟩
    · obtain ⟨k, z, hz⟩ := hg (V.hom x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
      obtain ⟨m, τ, rfl⟩ :=
        ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 (hE k).2).1 w
      refine ⟨⟨k, m⟩, (ψ ⟨k, m⟩).left ≫ pullback.fst _ _ |>.base τ, ?_⟩
      have key : (ψ ⟨k, m⟩).left ≫ pullback.fst _ _ ≫ (f ⟨k, m⟩).left =
          (φ k m).left ≫ pullback.fst V.hom (g k) := by
        rw [← hψ ⟨k, m⟩]
        simp
      rw [← hw]
      change ((ψ ⟨k, m⟩).left ≫ pullback.fst _ _ ≫ (f ⟨k, m⟩).left).base τ =
        ((φ k m).left ≫ pullback.fst V.hom (g k)).base τ
      exact congrArg (fun a ↦ a.base τ) key
    · exact MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) (f p).left
        V.hom V.prop (by rw [MorphismProperty.Over.w (f p)]; exact (V' p).prop)
  have hmem : Presieve.ofArrows V' f ∈ Scheme.ProEt.precoverage U V := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hDmem
  have hS : Sieve.generate (Presieve.ofArrows V' f) ∈ Scheme.ProEt.topology U V :=
    Scheme.ProEt.mem_topology_iff.2 ⟨_, hmem, Sieve.le_generate _⟩
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (forget (ModuleCat.{u + 1} R)) F.property) _ hS
  rw [← Presieve.isSheafFor_iff_generate] at hsh
  refine hsh.isSeparatedFor.ext fun _ _ ⟨p⟩ ↦ ?_
  change F.obj.map (f p).op s = F.obj.map (f p).op 0
  rw [hf p, map_zero]

variable (R) in
/-- **Pullbacks along a quasi-compact jointly surjective family are jointly faithful.** A
morphism of pro-étale sheaves of modules on `U` whose pullbacks along finitely many
quasi-compact morphisms `g k : Z k ⟶ U` jointly covering `U` vanish is zero. -/
theorem eq_zero_of_forall_upperStar_map_eq_zero {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}}
    (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    {F G : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R)} (φ : F ⟶ G)
    (h : ∀ k, (g k)^*[ModuleCat.{u + 1} R].map φ = 0) : φ = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ModuleCat.hom_ext
    (LinearMap.ext fun x ↦ ?_)))
  refine eq_zero_of_forall_unit_app_eq_zero R g hg G (φ.hom.app V x) fun k ↦ ?_
  have h0 : φ ≫ (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (g k)).unit.app G = 0 := by
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (g k)).unit.naturality φ
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map, h k,
      Functor.map_zero, comp_zero] at this
    exact this
  have := congrArg (fun ψ ↦ (ψ.hom.app V).hom x) h0
  simpa using this

end ProEtale

end AlgebraicGeometry
