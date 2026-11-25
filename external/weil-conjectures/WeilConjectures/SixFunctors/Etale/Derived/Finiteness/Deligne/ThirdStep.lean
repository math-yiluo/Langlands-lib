/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.OpenClosed
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.SecondStep

/-!
# The third step of Deligne's generic constructibility: an arbitrary constructible sheaf

Let `j : X ⟶ Y` be an immersion of finite type `S`-schemes with `X` reduced, let `v : V ⟶ X` be
an open immersion with `V` smooth over `S`, and `F` a constructible sheaf on `X` which is finite
locally constant on `V`. Assume that every point of the generic fibre of `X` outside `V` is a
specialization of a point of the generic fibre in `V`, and that the generic fibre of `X` has
dimension `< n + 1`. Granting the theorem in generic dimension `< n` and the smooth case, there
is a nonempty open of `S` over which `Rj_* F` is bounded constructible and commutes with every
base change from a noetherian scheme
(`AlgebraicGeometry.Etale.exists_hasDirectImageBaseChangeOnPlus_of_dense_smooth`).

Over a nonempty open `U ⊆ S`, the second step applies to `v` and to `v ≫ j`. Over `U`, complete
the unit `F ⟶ Rv_* v^* F` to a distinguished triangle `F ⟶ Rv_* v^* F ⟶ Δ ⟶`. Then `Δ` is
supported on the closed complement `W` of `V`, whose generic fibre has dimension `< n`, so the
induction hypothesis applies to the finitely many cohomology sheaves of `i^* Δ` along
`W ⟶ X ⟶ Y`, and the open–closed dévissage
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_distTriang_unit`) concludes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The comparison `a^* (b^* F)[0] ≅ c^* (d^* F)[0]` of the restrictions of a sheaf along two
factorizations `a ≫ b = c ≫ d` of the same morphism. -/
noncomputable def restrictSingleIso {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ D)
    (d : D ⟶ C) (h : a ≫ b = c ≫ d) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) b).obj F)) ≅
      ((c)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) d).obj F)) :=
  ((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.mapIso
      ((((b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F).symm ≪≫
    ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a b).app _).symm ≪≫
    (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) c d (a ≫ b) h).app _ ≪≫
    ((c)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.mapIso
      ((((d)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F)

variable [Finite Λ]

/-- **The third step of Deligne's generic constructibility**, for a reduced source with a dense
smooth open on which the sheaf is finite locally constant. -/
theorem exists_hasDirectImageBaseChangeOnPlus_of_dense_smooth {n : ℕ}
    (hQ : DeligneStatement Λ n) (hsm : SmoothGenericDirectImage Λ) {k : Type u} [Field k]
    {S X Y V : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (fY : Y ⟶ S) [LocallyOfFiniteType fY]
    [QuasiCompact fY] (j : X ⟶ Y) [IsImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (v : V ⟶ X) [IsOpenImmersion v] [Smooth (v ≫ j ≫ fY)]
    [IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).obj F)]
    (hdim : genericFiberDim (j ≫ fY) < (n + 1 : ℕ))
    (hgen : ∀ x : X, (j ≫ fY) x = genericPoint S → x ∉ Set.range v →
      ∃ y : X, (j ≫ fY) y = genericPoint S ∧ y ∈ Set.range v ∧ y ⤳ x) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ HasDirectImageBaseChangeOnPlus Λ fY j
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (fY ≫ aS)
  have := quasiCompact_of_isImmersion j
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (j ≫ fY ≫ aS)
  have : IsNoetherian S :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian aS
      __ := QuasiCompact.compactSpace_of_compactSpace aS }
  -- the closed complement `W` of `V`, whose generic fibre has smaller dimension
  let i := v.opensRange.closedComplement
  have hvi : Set.range i.base = (Set.range v.base)ᶜ := by
    rw [Opens.range_closedComplement]
    rfl
  have hdimW : genericFiberDim (i ≫ j ≫ fY) < n := by
    refine WithBot.ENat.lt_of_add_one_le_of_lt
      (genericFiberDim_add_one_le_of_generalizes i (j ≫ fY) fun x hx hxi ↦ ?_) hdim
    have hxv : x ∉ Set.range v := by
      have : x ∈ Set.range i.base := hxi
      rw [hvi] at this
      exact this
    obtain ⟨y, hy, hyv, hyx⟩ := hgen x hx hxv
    refine ⟨y, hy, fun hyi ↦ ?_, hyx⟩
    have : y ∈ Set.range i.base := hyi
    rw [hvi] at this
    exact this hyv
  -- the second step for `v` and for `v ≫ j`
  have := quasiCompact_of_isImmersion (v ≫ j)
  obtain ⟨U₁, hU₁, hv⟩ := exists_hasDirectImageBaseChangeOnPlus_of_smooth hQ hsm aS (j ≫ fY) v
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).obj F)
    ((genericFiberDim_comp_le v (j ≫ fY)).trans_lt hdim)
  have : Smooth ((v ≫ j) ≫ fY) := by rw [Category.assoc]; infer_instance
  obtain ⟨U₂, hU₂, hjv⟩ := exists_hasDirectImageBaseChangeOnPlus_of_smooth hQ hsm aS fY (v ≫ j)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).obj F)
    (by rw [Category.assoc]; exact (genericFiberDim_comp_le v (j ≫ fY)).trans_lt hdim)
  -- restriction of all the data over the nonempty open `U = U₁ ∩ U₂`
  let U : S.Opens := U₁ ⊓ U₂
  have hU : (U : Set S).Nonempty := Scheme.Opens.nonempty_inf hU₁ hU₂
  have : Nonempty U := hU.to_subtype
  have : IsNoetherian U := isNoetherian_opens U
  have : HasInvertibleExponent Λ U := HasInvertibleExponent.of_hom U.ι
  have hUim : U.ι '' (Set.univ : Set U) = U := by rw [Set.image_univ, Opens.range_ι]
  let YU := fY ⁻¹ᵁ U
  let fYU : YU.toScheme ⟶ U := fY ∣_ U
  let XU := j ⁻¹ᵁ YU
  let jU : XU.toScheme ⟶ YU := j ∣_ YU
  let VU := v ⁻¹ᵁ XU
  let vU : VU.toScheme ⟶ XU := v ∣_ XU
  let WU := i ⁻¹ᵁ XU
  let iU : WU.toScheme ⟶ XU := i ∣_ XU
  let FU := (Etale.upperStar (ModuleCat.{u + 1} Λ) XU.ι).obj F
  have := IsConstructibleSheaf.upperStar XU.ι F
  let KU := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj FU
  have hvU : HasDirectImageBaseChangeOnPlus Λ (jU ≫ fYU) vU
      (((vU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj KU) Set.univ := by
    have h := HasDirectImageBaseChangeOnPlus.restrict_base (fY := j ≫ fY) v U (V := Set.univ)
      (hv.mono (by rw [hUim]; exact Set.inter_subset_left))
    rw [morphismRestrict_comp] at h
    exact h.of_iso (restrictSingleIso VU.ι v vU XU.ι (morphismRestrict_ι v XU).symm F)
  have hjvU : HasDirectImageBaseChangeOnPlus Λ fYU (vU ≫ jU)
      (((vU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj KU) Set.univ := by
    have h := HasDirectImageBaseChangeOnPlus.restrict_base (fY := fY) (v ≫ j) U (V := Set.univ)
      (hjv.mono (by rw [hUim]; exact Set.inter_subset_right))
    rw [morphismRestrict_comp] at h
    exact h.of_iso (restrictSingleIso VU.ι v vU XU.ι (morphismRestrict_ι v XU).symm F)
  -- the triangle `K ⟶ Rv_* v^* K ⟶ Δ ⟶`, over `U`
  obtain ⟨Δ, w₂, w₃, hT⟩ := distinguished_cocone_triangle
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) vU).derivedPlus.unit.app KU)
  have : IsLocallyNoetherian XU := isLocallyNoetherian_of_isOpenImmersion XU.ι
  have hcv : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) XU
      (_root_.DerivedCategory.Plus.ι.obj ((vU)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        (((vU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj KU))) := by
    obtain ⟨c, -⟩ := hvU U (𝟙 _) (Set.subset_univ _) XU VU (𝟙 _) (jU ≫ fYU) (𝟙 _) vU
      (IsPullback.id_horiz _) (IsPullback.id_horiz _)
    exact ObjectProperty.prop_of_iso _ (_root_.DerivedCategory.Plus.ι.mapIso
      ((vU)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
        ((upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) VU).app _))) c
  have hcK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) XU
      (_root_.DerivedCategory.Plus.ι.obj KU) :=
    DerivedCategory.boundedConstructible_singleFunctor_obj FU 0
  have hcΔ : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) XU
      (_root_.DerivedCategory.Plus.ι.obj Δ) :=
    ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
      (_root_.DerivedCategory.Plus.ι.map_distinguished _ hT) hcK hcv
  let M := ((iU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj Δ
  have hΔ : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) WU
      (_root_.DerivedCategory.Plus.ι.obj M) := hcΔ.mapDerivedCategory_upperStar iU
  obtain ⟨a, b, hab⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 hΔ.1
  have : M.IsGE a := (M.isGE_ι_obj_iff a).1 hab.1
  have : M.IsLE b := (M.isLE_ι_obj_iff b).1 hab.2
  -- the induction hypothesis for the cohomology sheaves of `i^* Δ`, over `U`
  have hdimWU : genericFiberDim ((iU ≫ jU) ≫ fYU) < n := by
    refine (genericFiberDim_le_of_isEmbedding WU.ι WU.ι.isOpenEmbedding.isEmbedding _
      (i ≫ j ≫ fY) U.ι (genericPoint_eq_of_isOpenImmersion U.ι) ?_).trans_lt hdimW
    simp only [Category.assoc, morphismRestrict_ι, iU, jU, fYU]
    rw [← Category.assoc (j ∣_ YU), morphismRestrict_ι, Category.assoc, ← Category.assoc (i ∣_ XU),
      morphismRestrict_ι, Category.assoc]
  have hIH : ∀ q : ℤ, ∃ V' : (U : Scheme.{u}).Opens, (V' : Set U).Nonempty ∧
      HasDirectImageBaseChangeOnPlus Λ fYU (iU ≫ jU)
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj M)) V' := by
    intro q
    have : IsConstructibleSheaf ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj M) :=
      hΔ.2 q
    exact hQ (U.ι ≫ aS) fYU (iU ≫ jU) _ hdimWU
  choose V' hV'ne hV' using hIH
  let Vf : (U : Scheme.{u}).Opens := (Finset.Icc a b).inf V'
  have hVf : (Vf : Set U).Nonempty :=
    Scheme.Opens.nonempty_finset_inf _ _ fun q _ ↦ hV'ne q
  have hW : HasDirectImageBaseChangeOnPlus Λ fYU (iU ≫ jU) M Vf := by
    refine HasDirectImageBaseChangeOnPlus.of_bounded M a b fun q ↦ ?_
    by_cases hq : q ∈ Finset.Icc a b
    · exact (hV' q).mono fun x hx ↦ (Finset.inf_le (f := V') hq) hx
    · refine .of_isZero (Functor.map_isZero _ ?_)
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hq
      rcases hq with hq | hq
      · exact _root_.DerivedCategory.Plus.isZero_homology_of_isGE M a q hq
      · exact _root_.DerivedCategory.Plus.isZero_homology_of_isLE M b q hq
  -- the open–closed dévissage over `U`
  have hrange : ∀ {A : Scheme.{u}} (g : A ⟶ X) (x : XU),
      x ∈ Set.range (g ∣_ XU) ↔ XU.ι x ∈ Set.range g := by
    intro A g x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(g ⁻¹ᵁ XU).ι w, by
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]⟩
    · rintro ⟨w, hw⟩
      have hw' : w ∈ g ⁻¹ᵁ XU := by
        change g w ∈ XU
        rw [hw]
        exact x.2
      refine ⟨⟨w, hw'⟩, XU.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
      exact hw
  have hviU : Set.range iU.base = (Set.range vU.base)ᶜ := by
    ext x
    change x ∈ Set.range iU ↔ x ∉ Set.range vU
    rw [hrange, hrange, hvi]
    rfl
  have hres := HasDirectImageBaseChangeOnPlus.of_distTriang_unit jU vU iU hviU w₂ w₃ hT
    (hvU.mono (Set.subset_univ _)) (hjvU.mono (Set.subset_univ _)) hΔ hW
  have hS := HasDirectImageBaseChangeOnPlus.of_restrict_base (fY := fY) j U (V := (Vf : Set U))
    (hres.of_iso ((((XU.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app
      F).symm)
  refine ⟨U.ι ''ᵁ Vf, ?_, hS⟩
  obtain ⟨x, hx⟩ := hVf
  exact ⟨U.ι x, x, hx, rfl⟩

end Etale

end AlgebraicGeometry
