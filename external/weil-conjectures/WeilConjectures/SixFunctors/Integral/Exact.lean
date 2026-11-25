/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Claude
-/
module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.DisjointCover
public import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.AlgebraicGeometry.IntegralPointedClopenRefinement

/-!
# Exactness of the direct image along an integral morphism

For an integral morphism `f : X ⟶ Y` the pushforward `f_*` on étale sheaves of `Λ`-modules is
exact (`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`). That it
also detects the zero sheaf, hence is conservative, is proved in
`WeilConjectures.SixFunctors.Integral.StalkRestrict`.

The finite case of the exactness is
`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`, proved through the
stalk formula `AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`. For an integral morphism the
geometric fibres need no longer be finite, and the exactness is instead proved directly on
germs: a section of `f_* G'` lifting locally along an epimorphism `G ⟶ G'` lifts, after
shrinking the étale neighbourhood of the geometric point, on a decomposition of the base change
into pairwise disjoint opens (`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_hom_disjoint_cover`),
and there the local lifts glue
(`AlgebraicGeometry.Etale.surjective_sheafFiber_lowerStar_map_of_isIntegralHom`).

## Main statements

- `AlgebraicGeometry.Etale.surjective_sheafFiber_lowerStar_map_of_isIntegralHom`: the direct
  image along an integral morphism of an epimorphism is surjective on stalks at geometric points
  with algebraically closed residue field.
- `AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`: the direct
  image along an integral morphism is exact.

## References

- Stacks Project, Lemma 59.43.5, <https://stacks.math.columbia.edu/tag/04C2>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

/-- **The direct image along an integral morphism is surjective on stalks at geometric points
with algebraically closed residue field**, on an epimorphism `φ : G ⟶ G'`. A germ of `f_* G'` at
`y` is a section `z` of `G'` over `U ×_Y X` for a pointed étale neighbourhood `(U, u)`; it lifts
along `φ` locally on `U ×_Y X`, and after shrinking `(U, u)` this local lifting can be done on
a decomposition of `U ×_Y X` into pairwise disjoint opens
(`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_hom_disjoint_cover`), on which the lifts glue. -/
lemma Etale.surjective_sheafFiber_lowerStar_map_of_isIntegralHom {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : G ⟶ G') [Epi φ] :
    Function.Surjective
      ((pointSmallEtale y).sheafFiber.map ((f)_*[ModuleCat.{u + 1} Λ].map φ)) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro p
  obtain ⟨V, v, z, rfl⟩ := (pointSmallEtale y).toPresheafFiber_jointly_surjective
    (P := ((f)_*[ModuleCat.{u + 1} Λ].obj G').obj) p
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u + 1} Λ) φ).2 inferInstance
  have hR := Presheaf.imageSieve_mem X.smallEtaleTopology φ.hom z
  obtain ⟨c', g, ι, P, hdisj, hsup, hP⟩ :=
    Scheme.Hom.Nbhd.exists_hom_disjoint_cover f (Functor.elementsMk _ V v) _ hR
  choose a ha using hP
  -- glue the local lifts `a i` over the disjoint cover `P i` of `U' ×_Y X`
  let F := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G
  let F' :=
    (sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G'
  let π (i : ι) := Scheme.Hom.Nbhd.openIncl f c' (P i)
  have hcov : Sieve.ofArrows _ π ∈ X.smallEtaleTopology _ := by
    rw [ofArrows_mem_smallEtaleTopology_iff, Set.eq_univ_iff_forall]
    intro w
    have : w ∈ (⨆ i, P i) := hsup ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change w ∈ Set.range (P i).ι
    rw [Scheme.Opens.range_ι]
    exact hi
  have hdisj' : ∀ i j, i ≠ j →
      Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base) := by
    intro i j hij
    change Disjoint (Set.range (P i).ι.base) (Set.range (P j).ι.base)
    simp only [Scheme.Opens.range_ι]
    rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Opens.coe_inf,
      (hdisj i j hij).eq_bot, TopologicalSpace.Opens.coe_bot]
  obtain ⟨b, hb, -⟩ := F.property.existsUnique_amalgamation_ofArrows π hcov (E := PUnit)
    (fun i ↦ TypeCat.ofHom fun _ ↦ a i) (Etale.comp_map_eq_of_disjoint F _ π hdisj' _)
  have huniq := F'.property.existsUnique_amalgamation_ofArrows π hcov (E := PUnit)
    (fun i ↦ TypeCat.ofHom fun _ ↦ G'.obj.map (π i ≫ f.Etale.map g.val).op z)
    (Etale.comp_map_eq_of_disjoint F' _ π hdisj' _)
  have h₁ : φ.hom.app _ (b PUnit.unit) = G'.obj.map (f.Etale.map g.val).op z := by
    have := huniq.unique (y₁ := TypeCat.ofHom fun _ ↦ φ.hom.app _ (b PUnit.unit))
      (y₂ := TypeCat.ofHom fun _ ↦ G'.obj.map (f.Etale.map g.val).op z) (fun i ↦ ?_)
      (fun i ↦ ?_)
    · exact congrArg (fun h ↦ h PUnit.unit) this
    · ext ⟨⟩
      have hbi := congrArg (fun h ↦ h PUnit.unit) (hb i)
      change G.obj.map (π i).op (b PUnit.unit) = a i at hbi
      change G'.obj.map (π i).op (φ.hom.app _ (b PUnit.unit)) =
        G'.obj.map (π i ≫ f.Etale.map g.val).op z
      rw [← NatTrans.naturality_apply, hbi, ha i]
      rfl
    · ext ⟨⟩
      change G'.obj.map (π i).op (G'.obj.map (f.Etale.map g.val).op z) =
        G'.obj.map (π i ≫ f.Etale.map g.val).op z
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  refine ⟨(pointSmallEtale y).toPresheafFiber c'.1 c'.2 ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj
    (b PUnit.unit), ?_⟩
  change (pointSmallEtale y).presheafFiber.map ((f)_*[ModuleCat.{u + 1} Λ].map φ).hom _ = _
  rw [← ConcreteCategory.comp_apply, GrothendieckTopology.Point.toPresheafFiber_naturality,
    ConcreteCategory.comp_apply]
  change (pointSmallEtale y).toPresheafFiber c'.1 c'.2 ((f)_*[ModuleCat.{u + 1} Λ].obj G').obj
    (φ.hom.app _ (b PUnit.unit)) = _
  refine (congrArg (fun w ↦ (pointSmallEtale y).toPresheafFiber c'.1 c'.2
    ((f)_*[ModuleCat.{u + 1} Λ].obj G').obj w) h₁).trans ?_
  have h₂ := (pointSmallEtale y).toPresheafFiber_w_apply g.val c'.2
    ((f)_*[ModuleCat.{u + 1} Λ].obj G').obj z
  rw [Functor.Elements.Hom.val, g.map_val] at h₂
  exact h₂


/-- **The direct image along an integral morphism preserves epimorphisms.** The geometric points
`AlgebraicGeometry.Scheme.algClosurePoint s` of `Y` jointly reflect epimorphisms, and `f_* φ` is
surjective on the stalk at each of them by
`AlgebraicGeometry.Etale.surjective_sheafFiber_lowerStar_map_of_isIntegralHom`. -/
theorem Etale.preservesEpimorphisms_lowerStar_of_isIntegralHom :
    (f)_*[ModuleCat.{u + 1} Λ].PreservesEpimorphisms where
  preserves {G G'} φ _ := by
    refine (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale Y
      (ModuleCat.{u + 1} Λ)).epi_of_epi_map _ ?_
    rintro ⟨-, ⟨s⟩⟩
    have : Epi (((pointSmallEtale (Y.algClosurePoint s)).ulift.{u + 1}).sheafFiber.map
        ((f)_*[ModuleCat.{u + 1} Λ].map φ)) := by
      rw [← NatIso.naturality_2 ((pointSmallEtale (Y.algClosurePoint s)).uliftSheafFiberIso
        (ModuleCat.{u + 1} Λ)) ((f)_*[ModuleCat.{u + 1} Λ].map φ)]
      have : Epi ((pointSmallEtale (Y.algClosurePoint s)).sheafFiber.map
          ((f)_*[ModuleCat.{u + 1} Λ].map φ)) :=
        (ModuleCat.epi_iff_surjective _).mpr
          (Etale.surjective_sheafFiber_lowerStar_map_of_isIntegralHom Λ f _ φ)
      exact epi_comp _ _
    exact this

/-- Blueprint `lemma-integral-changes-source-base`: Étale direct image is exact for
integral morphisms.

The direct image `f_*` along an integral morphism `f` is exact on étale sheaves of
`Λ`-modules: it is left exact for every morphism, and it preserves epimorphisms by
`AlgebraicGeometry.Etale.preservesEpimorphisms_lowerStar_of_isIntegralHom`. -/
@[stacks 04C2]
theorem Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom :
    PreservesFiniteColimits (f)_*[ModuleCat.{u + 1} Λ] :=
  have := Etale.preservesEpimorphisms_lowerStar_of_isIntegralHom Λ f
  have : (f)_*[ModuleCat.{u + 1} Λ].PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Extend a germ from the pointed clopen piece, putting zero on its complement. -/
private lemma surjective_stalkRestrict_of_isIntegralHom {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (t : Scheme.Hom.GeometricFiber f y)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Surjective (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t G) := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro z
  obtain ⟨V, v, a, rfl⟩ := (pointSmallEtale t.1).toPresheafFiber_jointly_surjective
    (P := G.obj) z
  obtain ⟨c, P, Q, hPQ, hsup, p, α, hα, hp⟩ :=
    Scheme.Hom.Nbhd.exists_pointed_clopen_refinement f y t V v
  let R : Bool → (pullback c.1.hom f).Opens := fun i ↦ if i then P else Q
  let π (i : Bool) := Scheme.Hom.Nbhd.openIncl f c (R i)
  have hsup' : (⨆ i, R i) = ⊤ := by
    simpa [R, iSup_bool_eq, sup_comm] using hsup
  have hcov : Sieve.ofArrows _ π ∈ X.smallEtaleTopology _ := by
    rw [ofArrows_mem_smallEtaleTopology_iff, Set.eq_univ_iff_forall]
    intro w
    have : w ∈ (⨆ i, R i) := hsup' ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change w ∈ Set.range (R i).ι
    rw [Scheme.Opens.range_ι]
    exact hi
  have hdisj : ∀ i j, i ≠ j → Disjoint (R i) (R j) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [R, disjoint_comm]
  have hdisj' : ∀ i j, i ≠ j →
      Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base) := by
    intro i j hij
    change Disjoint (Set.range (R i).ι.base) (Set.range (R j).ι.base)
    simp only [Scheme.Opens.range_ι]
    rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Opens.coe_inf,
      (hdisj i j hij).eq_bot, TopologicalSpace.Opens.coe_bot]
  let F := (sheafCompose X.smallEtaleTopology
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G
  let s : ∀ i : Bool, G.obj.obj (.op (Scheme.Hom.Nbhd.openObj f c (R i))) := fun i ↦
    match i with
    | false => 0
    | true => G.obj.map α.op a
  obtain ⟨b, hb, -⟩ := F.property.existsUnique_amalgamation_ofArrows π hcov (E := PUnit)
    (fun i ↦ TypeCat.ofHom fun _ ↦ s i) (Etale.comp_map_eq_of_disjoint F _ π hdisj' _)
  have hbP : G.obj.map (Scheme.Hom.Nbhd.openIncl f c P).op (b PUnit.unit) =
      G.obj.map α.op a := by
    exact congrArg (fun h ↦ h PUnit.unit) (hb true)
  refine ⟨(pointSmallEtale y).toPresheafFiber c.1 c.2
    ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj (b PUnit.unit), ?_⟩
  have hr := congrArg (fun h ↦ h (b PUnit.unit))
    (Etale.toPresheafFiber_stalkRestrict (ModuleCat.{u + 1} Λ) f y t G c)
  simp only [ConcreteCategory.comp_apply] at hr
  erw [hr]
  rw [← hp]
  erw [← (pointSmallEtale t.1).toPresheafFiber_w_apply
    (Scheme.Hom.Nbhd.openIncl f c P) p G.obj, hbP]
  erw [(pointSmallEtale t.1).toPresheafFiber_w_apply α p G.obj, hα]

/-- The direct image along an integral morphism detects the zero sheaf: if `f_* G = 0` then
`G = 0`. This is the conservativity step of the proof of blueprint
`lemma-integral-changes-source-base--2`. For a geometric point `x` of `X` over the geometric point
`y` of `Y`, the stalk `G_x` is a colimit of factors of the sections of `G` over the integral base
change of the strict henselisation at `y`, which is the stalk `(f_* G)_y`; so `G_x` is a quotient of
`(f_* G)_y`.  (blueprint: lem-sbc-integral-direct-image-detects-zero)
-/
theorem Etale.isZero_of_isZero_lowerStar_obj
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hG : IsZero ((f)_*[ModuleCat.{u + 1} Λ].obj G)) : IsZero G := by
  refine (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale X
    (ModuleCat.{u + 1} Λ)).isZero_iff.mpr ?_
  rintro ⟨-, ⟨x⟩⟩
  let s := X.algClosurePoint x
  let t : Scheme.Hom.GeometricFiber f (s ≫ f) := ⟨s, rfl⟩
  let ρ : ((pointSmallEtale (s ≫ f)).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((f)_*[ModuleCat.{u + 1} Λ].obj G) ⟶
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G :=
    Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f (s ≫ f) t G
  have : Epi ρ := (ModuleCat.epi_iff_surjective ρ).mpr
    (surjective_stalkRestrict_of_isIntegralHom Λ f (s ≫ f) t G)
  have hsource : IsZero (((pointSmallEtale (s ≫ f)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj ((f)_*[ModuleCat.{u + 1} Λ].obj G)) :=
    (Functor.map_isZero (((pointSmallEtale (s ≫ f)).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ)) hG).of_iso
        (((pointSmallEtale (s ≫ f)).uliftSheafFiberIso (ModuleCat.{u + 1} Λ)).app
          ((f)_*[ModuleCat.{u + 1} Λ].obj G)).symm
  have h : IsZero (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) :=
    by
      apply IsZero.of_epi ρ
      exact hsource
  let e : (((pointSmallEtale s).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj G ≅
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G :=
    ((pointSmallEtale s).uliftSheafFiberIso (ModuleCat.{u + 1} Λ)).app G
  exact h.of_iso e

/-- The direct image along an integral morphism is conservative: being exact by
`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`, it sends the
kernel and the cokernel of a morphism to those of its image, and it detects their vanishing by
`AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj`. -/
theorem Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom :
    (f)_*[ModuleCat.{u + 1} Λ].ReflectsIsomorphisms where
  reflects {G G'} φ _ := by
    have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ f
    have : Mono φ := Preadditive.mono_of_isZero_kernel φ <|
      Etale.isZero_of_isZero_lowerStar_obj Λ f <|
      (isZero_kernel_of_mono ((f)_*[ModuleCat.{u + 1} Λ].map φ)).of_iso
        (PreservesKernel.iso _ φ)
    have : Epi φ := Preadditive.epi_of_isZero_cokernel φ <|
      Etale.isZero_of_isZero_lowerStar_obj Λ f <|
      (isZero_cokernel_of_epi ((f)_*[ModuleCat.{u + 1} Λ].map φ)).of_iso
        (PreservesCokernel.iso _ φ)
    exact isIso_of_mono_of_epi φ

end AlgebraicGeometry
