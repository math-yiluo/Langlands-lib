/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleLocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperTruncationBound
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperBoundedBelowCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Proper adic direct image preserves coproducts on the constructible localizing hull

Source: blueprint `theorem-exceptional-inverse-image` (2), with the identity compactification of a
proper map. (blueprint: lem-sfb-adic-proper-localizing-coproducts)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

private theorem coproduct_isGE
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (K : I → DerivedCategory A) (a : ℤ)
    (hK : ∀ i, (K i).IsGE a) : (∐ K).IsGE a := by
  apply (DerivedCategory.isGE_iff (∐ K) a).2
  intro q hq
  exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
    (coproductIsCoproduct K)).isZero_pt
    (Functor.isZero _ fun i ↦ (DerivedCategory.isGE_iff (K i.as) a).1 (hK i.as) q hq)

private theorem truncGE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncGE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncGE a
  let π := t.truncGEπ a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : (∐ L).IsGE a := coproduct_isGE L a (fun i ↦ inferInstance)
    let f : ∐ K ⟶ ∐ L := Sigma.desc (fun i ↦ π.app (K i) ≫ Sigma.ι L i)
    let r : T.obj (∐ K) ⟶ ∐ L := t.descTruncGE f a
    let c := sigmaComparison T K
    have hc : IsIso c := by
      refine ⟨⟨r, ?_, ?_⟩⟩
      · apply Sigma.hom_ext
        intro i
        change Sigma.ι L i ≫ (c ≫ r) = Sigma.ι L i ≫ 𝟙 _
        rw [← Category.assoc, ι_comp_sigmaComparison]
        apply t.from_truncGE_obj_ext
        simp only [Category.comp_id]
        rw [← Category.assoc]
        change (π.app (K i) ≫ T.map (Sigma.ι K i)) ≫ r =
          π.app (K i) ≫ Sigma.ι L i
        rw [← π.naturality (Sigma.ι K i)]
        change (Sigma.ι K i ≫ (t.truncGEπ a).app (∐ K)) ≫ t.descTruncGE f a = _
        rw [Category.assoc, t.π_descTruncGE, Sigma.ι_comp_desc]
      · apply t.from_truncGE_obj_ext
        dsimp only [r]
        rw [← Category.assoc, t.π_descTruncGE]
        apply Sigma.hom_ext
        intro i
        change Sigma.ι K i ≫ f ≫ c = Sigma.ι K i ≫ π.app (∐ K) ≫ 𝟙 _
        calc
          _ = π.app (K i) ≫ (Sigma.ι L i ≫ c) := by simp [f]
          _ = π.app (K i) ≫ T.map (Sigma.ι K i) := by
            rw [ι_comp_sigmaComparison]
          _ = _ := by simpa using (π.naturality (Sigma.ι K i)).symm
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k hΛ

/-- Proper derived pushforward, restricted to the source localizing hull, preserves
small coproducts. The target here is still the full ambient derived category.

Source: blueprint `theorem-exceptional-inverse-image` (2),
`proposition-proper-direct-image-extension-zero--1`, `sk-lem-proper-unbounded-window-ii`, and
`proposition-compactness-proper-direct-image--2` (3). (blueprint:
lem-sfb-adic-proper-localizing-coproducts)

Proof: distinguish the three constructors of the coefficient certificate. The schemes
and their locally closed strata are Noetherian. For E and Qlbar, identify the library's
local finite presentations with lisse local models using
`exists_finiteFree_cover_of_condensedField_lfp` and `condensedQbar_lfp_locally_free`.
For OE, use `integral_lfp_local_torsion_charts` and
`integral_lfp_locallyFree_resolution` for the integral constructible comparison and
finite Tor amplitude. These comparisons concern ordinary module sheaves; they do not
replace their ambient coproducts by completed coproducts.
In the E and Qlbar cases, bounded constructibility equals constructibility with finite Tor
amplitude. The subcategory of complexes with ind-constructible cohomology contains
bounded constructible complexes and is replete, triangulated and closed under ambient
sums (`corollary-ambient-ind-derived` (3)). It therefore contains the source hull.
The proper unbounded-window theorem gives preservation of sums on this larger
subcategory: a uniform geometric fibre-dimension bound reduces each target cohomology
degree to a fixed finite truncation window, where proper direct-image continuity
commutes with sums. For Qlbar use the finite-subextension coefficient convention.
In the OE case, choose a uniform bound d on geometric fibre dimensions. Integral
proper finiteness gives the bound [0, 2d+1] on ind-constructible sheaves; the associated
truncation window gives preservation of sums on ind-constructible complexes and hence
on the hull (`proposition-compactness-proper-direct-image--2` (1)-(3)). In each case the comparison
comes from the coprojections. Its cohomology maps are the continuity comparisons just
proved, so it is an isomorphism and the image cocone is a coproduct cocone. This also
handles the empty family, for which exact pushforward sends zero to zero.
-/
theorem ellAdic_localizingLowerStar_preservesCoproducts (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      ((boundedConstructibleLocalizingClosure Λ Z.left).ι ⋙ R((g.left)_*⟦Λ⟧)) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
    (condensedRingObj Λ Z.left)
  let D := Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
    (condensedRingObj Λ Y.left)
  let F : DerivedCategory C ⥤ DerivedCategory D := R((g.left)_*⟦Λ⟧)
  have : HasColimitsOfSize.{u + 1, u + 1} C := IsGrothendieckAbelian.hasColimits C
  have : HasColimitsOfSize.{u + 1, u + 1} D := IsGrothendieckAbelian.hasColimits D
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{u + 1} D := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{u + 1} (DerivedCategory C) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory D) := derived_hasCoproducts
  let Q := boundedConstructibleLocalizingClosure Λ Z.left
  obtain ⟨c, htail⟩ := ellAdic_proper_lowerTail_bound Λ ℓ g hΛ
  have hc (q : ℤ) (K : DerivedCategory C) (hK : Q K) :
      IsIso ((F ⋙ DerivedCategory.homologyFunctor D q).map
        ((DerivedCategory.TStructure.t.truncGEπ (q - (c : ℤ))).app K)) := by
    let t := DerivedCategory.TStructure.t (C := C)
    let T := F.mapTriangle.obj ((t.triangleLTGE (q - (c : ℤ))).obj K)
    have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
      F.map_distinguished _ (t.triangleLTGE_distinguished (q - (c : ℤ)) K)
    have : T.obj₁.IsLE (q - 1) := htail q K hK
    exact DerivedCategory.isIso_homologyMap_mor₂ T hT q (q + 1) rfl
      (DerivedCategory.isZero_of_isLE _ (q - 1) q (by omega))
      (DerivedCategory.isZero_of_isLE _ (q - 1) (q + 1) (by omega))
  have hA (A : I → DerivedCategory C) (hA : ∀ i, Q (A i)) :
      PreservesColimit (Discrete.functor A) F := by
    have hS : Q (∐ A) := Q.prop_of_isColimit (coproductIsCoproduct A) (fun i ↦ hA i.as)
    have hcomp : IsIso (sigmaComparison F A) := by
      apply (DerivedCategory.isIso_iff D _).2
      intro q
      let H := DerivedCategory.homologyFunctor D q
      let G := F ⋙ H
      let t := DerivedCategory.TStructure.t (C := C)
      let T := t.truncGE (q - (c : ℤ))
      let π := t.truncGEπ (q - (c : ℤ))
      have : PreservesColimitsOfShape (Discrete I) T :=
        truncGE_preservesCoproducts (q - (c : ℤ))
      have hbound : ∀ i, (T.obj (A i)).IsGE (q - (c : ℤ)) := fun i ↦ inferInstance
      have : PreservesColimit (Discrete.functor (fun i ↦ T.obj (A i))) F :=
        condensed_boundedBelow_preservesCoproduct Λ g.left I _ _ hbound
      have : PreservesColimit (Discrete.functor A ⋙ T) F :=
        preservesColimit_of_iso_diagram F
          (Discrete.natIso (fun _ ↦ Iso.refl _) :
            Discrete.functor (fun i ↦ T.obj (A i)) ≅ Discrete.functor A ⋙ T)
      have : PreservesColimit (Discrete.functor A) (T ⋙ G) := inferInstance
      let d := sigmaComparison (T ⋙ G) A
      let l := Limits.Sigma.map (fun i ↦ G.map (π.app (A i)))
      let r := G.map (π.app (∐ A))
      have hd : IsIso d := inferInstance
      have hl (i : I) : IsIso (G.map (π.app (A i))) := hc q (A i) (hA i)
      have : IsIso l := by dsimp only [l]; infer_instance
      have : IsIso r := hc q (∐ A) hS
      have square : sigmaComparison G A ≫ r = l ≫ d := by
        apply Sigma.hom_ext
        intro i
        simp only [l, d, r, ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc]
        change G.map (Sigma.ι A i) ≫ G.map (π.app (∐ A)) =
          G.map (π.app (A i)) ≫
            Sigma.ι (fun i ↦ (T ⋙ G).obj (A i)) i ≫ sigmaComparison (T ⋙ G) A
        rw [ι_comp_sigmaComparison]
        simpa only [Functor.comp_map, ← G.map_comp, Functor.id_map] using
          congrArg G.map (π.naturality (Sigma.ι A i))
      have : IsIso (sigmaComparison G A ≫ r) := by rw [square]; infer_instance
      have : IsIso (sigmaComparison G A) := IsIso.of_isIso_comp_right _ r
      have heq : sigmaComparison G A =
          sigmaComparison H (fun i ↦ F.obj (A i)) ≫ H.map (sigmaComparison F A) := by
        exact (sigmaComparison_map_desc H (fun i ↦ F.obj (A i)) _
          (fun i ↦ F.map (Sigma.ι A i))).symm
      have : IsIso (sigmaComparison H (fun i ↦ F.obj (A i)) ≫
          H.map (sigmaComparison F A)) := by rw [← heq]; infer_instance
      exact IsIso.of_isIso_comp_left (sigmaComparison H (fun i ↦ F.obj (A i))) _
    exact PreservesCoproduct.of_iso_comparison F A
  let ι := (boundedConstructibleLocalizingClosure Λ Z.left).ι
  have hK (K : I → (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory) :
      PreservesColimit (Discrete.functor K) (ι ⋙ F) := by
    have : PreservesColimit (Discrete.functor (fun i ↦ (K i).obj)) F :=
      hA _ (fun i ↦ (K i).property)
    have : PreservesColimit (Discrete.functor K ⋙ ι) F :=
      preservesColimit_of_iso_diagram F
        (Discrete.natIso (fun _ ↦ Iso.refl _) :
          Discrete.functor (fun i ↦ (K i).obj) ≅ Discrete.functor K ⋙ ι)
    infer_instance
  let : ∀ K : I → (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory,
      PreservesColimit (Discrete.functor K) (ι ⋙ F) := hK
  exact preservesColimitsOfShape_of_discrete (ι ⋙ F)

end AlgebraicGeometry.ProEtale.CondensedRing
