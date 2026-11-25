/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# The pro-étale pushforward along a qcqs morphism preserves filtered colimits

For a quasi-compact quasi-separated morphism `g : T ⟶ Y`, the pushforward `g_*` of abelian
pro-étale sheaves preserves colimits of `u + 1`-small filtered diagrams
(`AlgebraicGeometry.ProEtale.isColimit_lowerStar_mapCocone`): isomorphisms of pro-étale sheaves
are detected on the affine pro-étale site, and over an affine `W` the sections of `g_* F` are those
of `F` over the quasi-compact quasi-separated `W ×_Y T`, which commute with filtered colimits
(`CategoryTheory.Sheaf.exists_app_eq_of_isColimit_of_finite`). This is the degree `0` case of
the commutation of `Rg_*` with filtered colimits, needed to compare `Rg_* E_X` with
`(Rg_* 𝒪_{E,X})[1/ℓ]` (`WeilConjectures.SixFunctors.ProEtale.Adic.SubfieldSheafColimit`).

Moreover a filtered colimit of injective sheaves is `g_*`-acyclic
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isColimit_of_injective`), its higher
cohomology over the quasi-compact quasi-separated `W ×_Y T` vanishing by
`CategoryTheory.Sheaf.subsingleton_H_succ_of_isColimit_of_injective`. By induction on `i`, this
gives the commutation of `Rⁱg_*` with filtered colimits
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **The pushforward along a qcqs morphism preserves filtered colimits** of abelian pro-étale
sheaves: on an object `W` of the affine pro-étale site of `Y`, the sections of `g_* F` are those
of `F` over the quasi-compact quasi-separated `W ×_Y T`, which commute with filtered colimits
(`CategoryTheory.Sheaf.exists_app_eq_of_isColimit_of_finite`). -/
theorem isColimit_lowerStar_mapCocone {T Y : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g]
    [QuasiSeparated g] {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
    {F : K ⥤ Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) :
    Nonempty (IsColimit ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).mapCocone c)) := by
  let G := ProEtale.lowerStar AddCommGrpCat.{u + 1} g
  let c' := colimit.cocone (F ⋙ G)
  let φ : c'.pt ⟶ G.obj c.pt := colimit.desc _ (G.mapCocone c)
  have hφ (k : K) : c'.ι.app k ≫ φ = G.map (c.ι.app k) := colimit.ι_desc _ _
  suffices IsIso φ from ⟨IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (asIso φ) fun k ↦ hφ k)⟩
  refine isIso_of_isIso_app_affineProEt _ φ fun W ↦ ?_
  let W' := (AffineProEt.toProEt Y).obj W
  let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj W'
  have : CompactSpace W'.left := inferInstanceAs (CompactSpace W.left)
  have : QuasiSeparatedSpace W'.left := inferInstanceAs (QuasiSeparatedSpace W.left)
  have : CompactSpace V.left := by
    have : CompactSpace ((𝟭 Scheme).obj W'.left) := inferInstanceAs (CompactSpace W'.left)
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst W'.hom g)
  have : QuasiSeparatedSpace V.left := by
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj W'.left) :=
      inferInstanceAs (QuasiSeparatedSpace W'.left)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst W'.hom g)
  have hc' : IsColimit c' := colimit.isColimit _
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero (φ.hom.app (op W')).hom).2 fun x hx ↦ ?_, fun s ↦ ?_⟩
  · obtain ⟨k, t, rfl⟩ := Sheaf.exists_app_eq_of_isColimit_of_finite hc'
      (fun W : Y.ProEt ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left)
      (fun _ hW _ hR ↦ ProEt.exists_finite_cechNerve_of_mem_topology hW hR) ⟨‹_›, ‹_›⟩ x
    have h0 : (c.ι.app k).hom.app (op V) t = 0 := by
      change ((c'.ι.app k ≫ φ).hom.app (op W')) t = 0 at hx
      rw [hφ] at hx
      exact hx
    obtain ⟨k', a, ha⟩ := Sheaf.exists_map_eq_zero_of_isColimit_of_finite hc
      (fun R hR ↦ by
        obtain ⟨n, U, -, hUR, hUJ⟩ := ProEt.exists_finite_cechNerve_of_mem_topology ⟨‹_›, ‹_›⟩ hR
        exact ⟨n, U, hUR, hUJ⟩) t h0
    rw [← c'.w a]
    change ((c'.ι.app k').hom.app (op W')) ((F.map a).hom.app (op V) t) = 0
    rw [ha, map_zero]
  · obtain ⟨k, t, ht⟩ := Sheaf.exists_app_eq_of_isColimit_of_finite hc
      (fun W : T.ProEt ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left)
      (fun _ hW _ hR ↦ ProEt.exists_finite_cechNerve_of_mem_topology hW hR) ⟨‹_›, ‹_›⟩ s
    refine ⟨(c'.ι.app k).hom.app (op W') t, ?_⟩
    change ((c'.ι.app k ≫ φ).hom.app (op W')) t = s
    rw [hφ]
    exact ht

/-- **A filtered colimit of injective sheaves is acyclic for the pushforward along a qcqs
morphism**: by `AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isZero_rightDerived` it
suffices that its higher cohomology over `W ×_Y T` vanishes for `W` affine, and the restriction to
the quasi-compact quasi-separated `W ×_Y T` is a filtered colimit of injective sheaves, which has
no higher cohomology
(`CategoryTheory.Sheaf.subsingleton_H_succ_of_isColimit_of_injective`).
-/
theorem rightAcyclic_lowerStar_of_isColimit_of_injective {T Y : Scheme.{u}} (g : T ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g] {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
    {I : K ⥤ Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}} [∀ k, Injective (I.obj k)]
    {c : Cocone I} (hc : IsColimit c) :
    (ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightAcyclic c.pt := by
  refine rightAcyclic_lowerStar_of_isZero_rightDerived _ g _ fun W q ↦ ?_
  let W' := (AffineProEt.toProEt Y).obj W
  let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj W'
  have : CompactSpace W'.left := inferInstanceAs (CompactSpace W.left)
  have : QuasiSeparatedSpace W'.left := inferInstanceAs (QuasiSeparatedSpace W.left)
  have : CompactSpace V.left := by
    have : CompactSpace ((𝟭 Scheme).obj W'.left) := inferInstanceAs (CompactSpace W'.left)
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst W'.hom g)
  have : QuasiSeparatedSpace V.left := by
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj W'.left) :=
      inferInstanceAs (QuasiSeparatedSpace W'.left)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst W'.hom g)
  refine isZero_rightDerived_sectionsFunctor_of_upperStar _ V _ _ ?_
  have : WeaklyEtale V.hom := V.prop
  have hc₂ := isColimitOfPreserves (ProEtale.upperStar AddCommGrpCat.{u + 1} V.hom) hc
  have (k : K) : Injective ((I ⋙ ProEtale.upperStar AddCommGrpCat.{u + 1} V.hom).obj k) :=
    injective_upperStar_obj_of_weaklyEtale _ V.hom (I.obj k)
  have hs := Sheaf.subsingleton_H_succ_of_isColimit_of_injective
    (MorphismProperty.Over.mkIdTerminal @WeaklyEtale V.left)
    (fun W : V.left.ProEt ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left) ⟨‹_›, ‹_›⟩
    (fun _ hW _ hR ↦ ProEt.exists_finite_cechNerve_of_mem_topology hW hR) hc₂ q
  obtain ⟨e⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    (ProEt.topology V.left) _ (ProEt.isTerminalMkId V.left)
    ((ProEtale.upperStar AddCommGrpCat.{u + 1} V.hom).obj c.pt) q
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact ⟨fun a b ↦ e.symm.injective (@Subsingleton.elim _ hs _ _)⟩

end AlgebraicGeometry.ProEtale
