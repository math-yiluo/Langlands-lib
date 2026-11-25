/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary

/-!
# The exceptional Künneth maps along a closed immersion

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, and `Y`, `W` schemes
of finite type over `k`, with product `P = Y ×_k W` and projections `q : P ⟶ Y`, `r : P ⟶ W`.
For a closed immersion `i : Z ⟶ Y`, with base change `i_W : Z ×_k W ⟶ P` and
`q_Z : Z ×_k W ⟶ Z`, the two canonical maps of the exceptional inverse image entering the
exceptional Künneth formula (`proposition-exceptional-external-kunneth--1`) are isomorphisms:

* the base change map `Lq_Z^* Ri^! N ⟶ Ri_W^! Lq^* N`
  (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`), for every `N`;
* the tensor map `Ri_W^!(Lq^* N) ⊗ᴸ Li_W^* Lr^* M ⟶ Ri_W^!(Lq^* N ⊗ᴸ Lr^* M)`
  (`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`), for all `N` and `M`.

This is the closed-immersion case of the blueprint proof: by the supported localization triangle
`Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶` of the open complement `j : U ⟶ Y`
(`lemma-local-cohomology-right-adjoint--2`), the cone of the transpose of either map is of the form
`Rj_W*(-)`, by the base change formula for `Rj_*` tensored with a complex
(`lemma-kunneth-field-coefficients--1`, `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`); such
objects receive no maps from objects supported on `Z ×_k W`, and `Ri_W!` is fully faithful.

## Main statements

- `CategoryTheory.Pretriangulated.isIso_of_distTriang_of_subsingleton`: the abstract criterion.
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion`: the
  tensor map of a closed immersion, for any coefficients.
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isClosedImmersion`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekTensorMap_pullback_of_isClosedImmersion`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Let `F ⊣ G` with `F` fully faithful, and let `T` be a distinguished triangle whose third
vertex receives no maps from the shifts of objects in the image of `F`. Then a morphism
`φ : X ⟶ G T₂` whose transpose `F X ⟶ T₂` is, up to an isomorphism `F X ≅ T₁`, the first
morphism of `T`, is an isomorphism: `Hom(M, X) ≅ Hom(F M, T₁) ≅ Hom(F M, T₂) ≅ Hom(M, G T₂)`. -/
theorem isIso_of_distTriang_of_subsingleton {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    (hF : F.FullyFaithful) {T : Triangle C} (hT : T ∈ distTriang C)
    (h₃ : ∀ (M : D) (n : ℤ), Subsingleton ((F.obj M)⟦n⟧ ⟶ T.obj₃)) {X : D}
    (φ : X ⟶ G.obj T.obj₂) (e : F.obj X ≅ T.obj₁)
    (he : e.hom ≫ T.mor₁ = (adj.homEquiv _ _).symm φ) : IsIso φ := by
  refine isIso_of_yoneda_map_bijective _ fun M ↦ ?_
  have hb : Function.Bijective (fun x : F.obj M ⟶ T.obj₁ ↦ x ≫ T.mor₁) := by
    have := h₃ M 1
    have : Subsingleton (F.obj M ⟶ T.obj₃) :=
      have := h₃ M 0
      ((shiftFunctorZero C ℤ).app (F.obj M)).homFromEquiv.symm.subsingleton
    exact ⟨fun _ _ hxy ↦ Triangle.cancel_mor₁_of_subsingleton hT hxy,
      fun y ↦ (Triangle.coyoneda_exact₂ T hT y (Subsingleton.elim _ _)).imp fun _ hx ↦ hx.symm⟩
  have he' : Function.Bijective (fun x : F.obj M ⟶ F.obj X ↦ x ≫ e.hom) :=
    Function.bijective_iff_has_inverse.2 ⟨(· ≫ e.inv), fun x ↦ by simp, fun x ↦ by simp⟩
  have hc : (fun x : M ⟶ X ↦ x ≫ φ) = (adj.homEquiv _ _) ∘ (fun x ↦ x ≫ T.mor₁) ∘
      (fun x ↦ x ≫ e.hom) ∘ hF.homEquiv := by
    ext x
    simp only [Function.comp_apply, Functor.FullyFaithful.homEquiv_apply, Category.assoc, he,
      ← Adjunction.homEquiv_naturality_left_symm, Equiv.apply_symm_apply]
  rw [hc]
  exact (adj.homEquiv _ _).bijective.comp (hb.comp (he'.comp hF.homEquiv.bijective))

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Vanishing

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- An object isomorphic to some `Rj_* C`, for an open immersion `j`, receives no maps from the
shifts of objects `Ri_! D` supported on a closed subscheme disjoint from `j`. -/
lemma subsingleton_hom_shift_of_iso_rightDerivedLowerStar {Z X U : Scheme.{u}} (i : Z ⟶ X)
    [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    {T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {C : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)} (e : T ≅ (R((j)_*[A])).obj C)
    (D : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) (n : ℤ) :
    Subsingleton (((R(i)_![A]).obj D)⟦n⟧ ⟶ T) :=
  have := subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar A i j hij D C n
  ((Iso.refl _).homCongr e).subsingleton

end Vanishing

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [HasSmallSiteSheafify A]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **The tensor map of a closed immersion.** Let `i : Z ⟶ X` be a closed immersion with open
complement `j : U ⟶ X`. If `Rj_* Lj^* M ⊗ᴸ N` receives no maps from the shifts of objects
`Ri_! D`, then the tensor map `Ri^! M ⊗ᴸ Li^* N ⟶ Ri^!(M ⊗ᴸ N)` is an isomorphism: its transpose
is, up to the projection formula, the supported localization triangle of `M` tensored with
`N`. -/
theorem isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion {Z X U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [HasCompactification i]
    [IsIso (projectionMap (ModuleCat.{u + 1} Λ) i)] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : ∀ (D : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ),
      Subsingleton (((R(i)_![ModuleCat.{u + 1} Λ]).obj D)⟦n⟧ ⟶
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
            ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M))).obj N)) :
    IsIso (rightDerivedUpperShriekTensorMap i M N) := by
  have := isIso_rightDerivedUpperShriekAdjunction_unit_app Λ i
  have : IsIso (rightDerivedUpperShriekAdjunction Λ i).unit := NatIso.isIso_of_isIso_app _
  have hT := ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj N).map_distinguished _
    (supportedLocalizationTriangle_mem_distTriang Λ i j hij M)
  let e : (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M ⊗ (L((i)^*[ModuleCat.{u + 1} Λ])).obj
      N) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj N).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
          ((R(i)^![Λ]).obj M)) :=
    (asIso (((projectionMap (ModuleCat.{u + 1} Λ) i).app ((R(i)^![Λ]).obj M)).app N)).symm
  refine Pretriangulated.isIso_of_distTriang_of_subsingleton
    (rightDerivedUpperShriekAdjunction Λ i)
    (rightDerivedUpperShriekAdjunction Λ i).fullyFaithfulLOfIsIsoUnit hT h
    (rightDerivedUpperShriekTensorMap i M N) e ?_
  rw [Adjunction.homEquiv_counit]
  erw [Adjunction.map_projectionTensorMap_comp_counit]
  rfl

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section Kunneth

variable {Y W P U UW : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : W ⟶ Spec (.of k))
  [LocallyOfFiniteType b] [QuasiCompact b] [LocallyOfFiniteType c] [QuasiCompact c]
  {q : P ⟶ Y} {r : P ⟶ W} (sqP : IsPullback q r b c)
  (j : U ⟶ Y) [QuasiCompact j] [LocallyOfFiniteType j] {qU : UW ⟶ U} {jW : UW ⟶ P}
  (sqU : IsPullback qU jW j q)

include sqP sqU

/-- The base change formula for `Rj_*` along the projection `q : Y ×_k W ⟶ Y`, tensored with
an object pulled back from `W` (`lemma-kunneth-field-coefficients--1`):
`Lr^* M ⊗ᴸ Lq^* Rj_* F ≅ Rj_W*(Lj_W^* Lr^* M ⊗ᴸ Lq_U^* F)`. -/
theorem nonempty_iso_derivedTensor_leftDerivedUpperStar_rightDerivedLowerStar
    (M : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj
        ((L((r)^*[ModuleCat.{u + 1} Λ])).obj M)).obj
          ((L((q)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj F)) ≅
      (R((jW)_*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor (ModuleCat.{u + 1} Λ) UW).obj
        ((L((jW)^*[ModuleCat.{u + 1} Λ])).obj ((L((r)^*[ModuleCat.{u + 1} Λ])).obj M))).obj
          ((L((qU)^*[ModuleCat.{u + 1} Λ])).obj F))) :=
  have := isIso_tensorBaseChangeMap Λ c b (j ≫ b) r q jW qU j rfl sqP.flip sqU.flip M F
  ⟨asIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) jW qU q j sqU.flip.w
    ((L((r)^*[ModuleCat.{u + 1} Λ])).obj M) F)⟩

/-- The base change formula for `Rj_*` along the projection `q : Y ×_k W ⟶ Y`:
`Lq^* Rj_* F ≅ Rj_W* Lq_U^* F` (`lemma-kunneth-field-coefficients--1` with `M = Λ_W`). -/
theorem nonempty_iso_leftDerivedUpperStar_rightDerivedLowerStar
    (F : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((L((q)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj F) ≅
      (R((jW)_*[ModuleCat.{u + 1} Λ])).obj ((L((qU)^*[ModuleCat.{u + 1} Λ])).obj F)) := by
  obtain ⟨e⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_rightDerivedLowerStar Λ b c
    sqP j sqU (𝟙_ _) F
  exact ⟨(derivedTensorLeftUnitor _ P _).symm ≪≫
    ((derivedTensor _ P).mapIso (leftDerivedUpperStarUnitIso _ r).symm).app _ ≪≫ e ≪≫
    (R((jW)_*[ModuleCat.{u + 1} Λ])).mapIso
      (((derivedTensor _ UW).mapIso ((L((jW)^*[ModuleCat.{u + 1} Λ])).mapIso
        (leftDerivedUpperStarUnitIso _ r) ≪≫ leftDerivedUpperStarUnitIso _ jW)).app _ ≪≫
        derivedTensorLeftUnitor _ UW _)⟩

end Kunneth

section ClosedImmersion

variable {Y W P Z ZW : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : W ⟶ Spec (.of k))
  [LocallyOfFiniteType b] [QuasiCompact b] [LocallyOfFiniteType c] [QuasiCompact c]
  {q : P ⟶ Y} {r : P ⟶ W} (sqP : IsPullback q r b c)
  (i : Z ⟶ Y) [IsClosedImmersion i] {qZ : ZW ⟶ Z} {iW : ZW ⟶ P}
  (sqZ : IsPullback qZ iW i q)

/-- The open complement of the closed immersion `i`. -/
noncomputable abbrev complOpens : Y.Opens :=
  ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

include sqZ in
/-- The base change `i_W` of a closed immersion `i` and the base change of the open complement of
`i` have complementary ranges. -/
lemma range_eq_compl_range_pullback_snd :
    Set.range iW.base = (Set.range (pullback.snd (complOpens i).ι q).base)ᶜ := by
  have h₁ : Set.range iW.base = Set.range (pullback.snd i q).base := by
    rw [← sqZ.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 sqZ.isoPullback.hom.surjective, Set.image_univ]
  rw [h₁]
  change Set.range ⇑(pullback.snd i q) = (Set.range ⇑(pullback.snd (complOpens i).ι q))ᶜ
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Scheme.Opens.range_ι,
    ← Set.preimage_compl]
  simp

include sqP sqZ in
/-- **Base change of `Ri^!` along a product projection, for a closed immersion.** For a closed
immersion `i : Z ⟶ Y` and the projection `q : Y ×_k W ⟶ Y`, the base change map
`Lq_Z^* Ri^! N ⟶ Ri_W^! Lq^* N` is an isomorphism for every `N`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_isClosedImmersion
    [HasCompactification iW] [QuasiCompact iW]
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqZ).app N) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian b }
  have : IsClosedImmersion iW := MorphismProperty.of_isPullback sqZ ‹_›
  let j := (complOpens i).ι
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    change _ = (Set.range ⇑(complOpens i).ι)ᶜ
    rw [Scheme.Opens.range_ι]
    simp
  have hdisj : Disjoint (Set.range iW.base) (Set.range (pullback.snd j q).base) := by
    rw [range_eq_compl_range_pullback_snd i sqZ]
    exact disjoint_compl_left
  have := isIso_rightDerivedUpperShriekAdjunction_unit_app Λ iW
  have : IsIso (rightDerivedUpperShriekAdjunction Λ iW).unit :=
    NatIso.isIso_of_isIso_app _
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqZ
  have hT := (L((q)^*[ModuleCat.{u + 1} Λ])).map_distinguished _
    (supportedLocalizationTriangle_mem_distTriang _ i j hij N)
  let e : (R(iW)_![ModuleCat.{u + 1} Λ]).obj ((L((qZ)^*[ModuleCat.{u + 1} Λ])).obj
      ((R(i)^![Λ]).obj N)) ≅ (L((q)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj N)) :=
    (asIso ((rightDerivedLowerShriekBaseChangeMap Λ sqZ).app ((R(i)^![_]).obj N))).symm
  have he : e.hom ≫ (L((q)^*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekAdjunction _ i).counit.app N) =
      (R(iW)_![ModuleCat.{u + 1} Λ]).map ((rightDerivedUpperShriekBaseChangeMap Λ sqZ).app N) ≫
        (rightDerivedUpperShriekAdjunction _ iW).counit.app _ := by
    simp only [rightDerivedUpperShriekBaseChangeMap]
    rw [mateEquiv_counit]
    simp [e, NatIso.isIso_inv_app]
  obtain ⟨e'⟩ := nonempty_iso_leftDerivedUpperStar_rightDerivedLowerStar Λ b c sqP j
    (IsPullback.of_hasPullback j q) ((L((j)^*[ModuleCat.{u + 1} Λ])).obj N)
  exact Pretriangulated.isIso_of_distTriang_of_subsingleton
    (rightDerivedUpperShriekAdjunction _ iW)
    (rightDerivedUpperShriekAdjunction _ iW).fullyFaithfulLOfIsIsoUnit hT
    (subsingleton_hom_shift_of_iso_rightDerivedLowerStar iW (pullback.snd j q) hdisj e')
    ((rightDerivedUpperShriekBaseChangeMap Λ sqZ).app N) e
    (by rw [Adjunction.homEquiv_counit]; exact he)

include sqP sqZ in
/-- **The tensor map of a closed immersion along a product.** For a closed immersion
`i : Z ⟶ Y` with base change `i_W : Z ×_k W ⟶ Y ×_k W`, the tensor map
`Ri_W^!(Lq^* N) ⊗ᴸ Li_W^* Lr^* M ⟶ Ri_W^!(Lq^* N ⊗ᴸ Lr^* M)` is an isomorphism for all `N`
and `M`. -/
theorem isIso_rightDerivedUpperShriekTensorMap_pullback_of_isClosedImmersion
    [HasCompactification iW]
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (rightDerivedUpperShriekTensorMap iW ((L((q)^*[ModuleCat.{u + 1} Λ])).obj N)
      ((L((r)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian b }
  have : IsClosedImmersion iW := MorphismProperty.of_isPullback sqZ ‹_›
  let j := (complOpens i).ι
  have hdisj : Disjoint (Set.range iW.base) (Set.range (pullback.snd j q).base) := by
    rw [range_eq_compl_range_pullback_snd i sqZ]
    exact disjoint_compl_left
  let jW := pullback.snd j q
  let qU := pullback.fst j q
  have sqU : IsPullback qU jW j q := IsPullback.of_hasPullback j q
  refine isIso_rightDerivedUpperShriekTensorMap_of_isClosedImmersion iW jW
    (range_eq_compl_range_pullback_snd i sqZ) _ _ fun D n ↦ ?_
  obtain ⟨e₁⟩ := nonempty_iso_leftDerivedUpperStar_rightDerivedLowerStar Λ b c sqP j sqU
    ((L((j)^*[ModuleCat.{u + 1} Λ])).obj N)
  obtain ⟨e₂⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_rightDerivedLowerStar Λ b c
    sqP j sqU M ((L((j)^*[ModuleCat.{u + 1} Λ])).obj N)
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) P
  -- `Lj_W^* Lq^* N ≅ Lq_U^* Lj^* N`
  let e₀ : (L((jW)^*[ModuleCat.{u + 1} Λ])).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj N) ≅
      (L((qU)^*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj N) :=
    ((leftDerivedUpperStarComp _ jW q).app N).symm ≪≫
      (leftDerivedUpperStarComp _ qU j (jW ≫ q) sqU.w.symm).app N
  let e : ((derivedTensor (ModuleCat.{u + 1} Λ) P).obj ((R((jW)_*[ModuleCat.{u + 1} Λ])).obj
      ((L((jW)^*[ModuleCat.{u + 1} Λ])).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj N)))).obj
        ((L((r)^*[ModuleCat.{u + 1} Λ])).obj M) ≅ _ :=
    ((derivedTensor _ P).mapIso ((R((jW)_*[ModuleCat.{u + 1} Λ])).mapIso e₀ ≪≫ e₁.symm)).app _ ≪≫
      (β.app _).app _ ≪≫ e₂
  exact subsingleton_hom_shift_of_iso_rightDerivedLowerStar iW jW hdisj e D n

end ClosedImmersion

end Etale

end AlgebraicGeometry
