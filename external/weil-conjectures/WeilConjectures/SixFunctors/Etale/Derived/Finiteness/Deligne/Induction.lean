/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.ThirdStep

/-!
# The induction step of Deligne's generic constructibility

Granting the smooth case `lemma-smooth-morphisms-locally-constant-sheaves`
(`AlgebraicGeometry.Etale.SmoothGenericDirectImage`), the induction statement in generic dimension
`< n` implies it in generic dimension `< n + 1`
(`AlgebraicGeometry.Etale.deligneStatement_succ`). Hence Deligne's generic constructibility
theorem follows from the smooth case
(`exists_hasConstructibleDirectImageBaseChangeOn_of_smoothGenericDirectImage`).

For the induction step, after shrinking `S` to a nonempty open `U₀`, a finite, surjective and
radicial base change `π : S' ⟶ U₀` with `S'` integral makes the reduction of `X' = X ×_S S'`
contain a dense open `V`, smooth over `S'`, on which the sheaf is finite locally constant
(`AlgebraicGeometry.exists_isFinite_universallyInjective_smooth_dense`). The third step applies
over `S'` to the reduction of `X'`
(`AlgebraicGeometry.Etale.exists_hasDirectImageBaseChangeOnPlus_of_dense_smooth`); one passes
from the reduction to `X'`
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_surjective_closedImmersion`), descends
along `π` (`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_isFinite_of_surjective`)
and finally from `U₀` to `S`
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_restrict_base`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **The induction step of Deligne's generic constructibility**: granting the smooth case, the
induction statement in generic dimension `< n` implies it in generic dimension `< n + 1`. -/
theorem deligneStatement_succ (hsm : SmoothGenericDirectImage Λ) {n : ℕ}
    (hQ : DeligneStatement Λ n) : DeligneStatement Λ (n + 1) := by
  intro k _ S X Y _ aS _ _ _ fY _ _ j _ F _ hdim
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (fY ≫ aS)
  have := quasiCompact_of_isImmersion j
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨⊤, ⟨Classical.arbitrary S, trivial⟩, .of_isEmpty fY j _ _⟩
  obtain ⟨U₀, S', π, X', q, f', V, v, hU₀, _, _, _, _, hq, _, _, hvo, -, _, hF, hgen⟩ :=
    exists_isFinite_universallyInjective_smooth_dense aS (j ≫ fY) Λ F
  have : Nonempty U₀ := hU₀.to_subtype
  have : IsUniversalHomeomorphism π := { }
  have : IsUniversalHomeomorphism q := MorphismProperty.of_isPullback hq.flip inferInstance
  -- the base change of the data along `π`
  let Y₀ := fY ⁻¹ᵁ U₀
  let fY₀ : Y₀.toScheme ⟶ U₀ := fY ∣_ U₀
  let X₀ := j ⁻¹ᵁ Y₀
  let j₀ : X₀.toScheme ⟶ Y₀ := j ∣_ Y₀
  have hq' : IsPullback q f' (j₀ ≫ fY₀) π := by rw [← morphismRestrict_comp]; exact hq
  let Y' := pullback fY₀ π
  let g : Y' ⟶ Y₀ := pullback.fst fY₀ π
  let fY' : Y' ⟶ S' := pullback.snd fY₀ π
  have hY : IsPullback g fY' fY₀ π := IsPullback.of_hasPullback fY₀ π
  let j' : X' ⟶ Y' := pullback.lift (q ≫ j₀) f' (by rw [Category.assoc]; exact hq'.w)
  have hj'f : j' ≫ fY' = f' := pullback.lift_snd _ _ _
  have hX : IsPullback q j' j₀ g :=
    IsPullback.of_bot (by rw [hj'f]; exact hq') (pullback.lift_fst _ _ _).symm hY
  have : LocallyOfFiniteType fY' := MorphismProperty.of_isPullback hY inferInstance
  have : QuasiCompact fY' := MorphismProperty.of_isPullback hY inferInstance
  have : IsImmersion j' := MorphismProperty.of_isPullback hX inferInstance
  have : LocallyOfFiniteType (j' ≫ fY') := by
    rw [hj'f]; exact MorphismProperty.of_isPullback hq inferInstance
  let aS' : S' ⟶ Spec (.of k) := π ≫ U₀.ι ≫ aS
  have : IsNoetherian S :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian aS
      __ := QuasiCompact.compactSpace_of_compactSpace aS }
  have : QuasiCompact aS' := by dsimp only [aS']; infer_instance
  have : LocallyOfFiniteType aS' := by dsimp only [aS']; infer_instance
  have : HasInvertibleExponent Λ S' := HasInvertibleExponent.of_hom (π ≫ U₀.ι)
  -- the reduction of `X'` and the dense smooth open `V` in it
  let r := X'.nilradical.subschemeι
  have : Surjective r := ⟨by
    rw [← Set.range_eq_univ, IdealSheafData.range_subschemeι, support_nilradical]
    rfl⟩
  let v' : V ⟶ X'.nilradical.subscheme := v.liftNilradical
  have hv' : v' ≫ r = v := v.liftNilradical_subschemeι
  have hrv : Set.range v' = r ⁻¹' Set.range v := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [← hv', Scheme.Hom.comp_apply]⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, r.isHomeomorph.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hv', hy]
  have : IsImmersion v' := by
    have : IsImmersion (v' ≫ r) := by rw [hv']; infer_instance
    exact .of_comp v' r
  have : IsOpenImmersion v' := IsImmersion.isOpenImmersion_of_isOpen_range v' (by
    rw [hrv]
    exact hvo.preimage r.continuous)
  have hsmooth : v' ≫ (r ≫ j') ≫ fY' = v ≫ f' := by
    rw [Category.assoc, hj'f, ← Category.assoc, hv']
  have : Smooth (v' ≫ (r ≫ j') ≫ fY') := by rw [hsmooth]; infer_instance
  let G := (Etale.upperStar (ModuleCat.{u + 1} Λ) (r ≫ q ≫ X₀.ι)).obj F
  have : IsConstructibleSheaf G := IsConstructibleSheaf.upperStar _ F
  have : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (v ≫ q ≫ X₀.ι)).obj F) := hF
  have : IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) v').obj G) :=
    IsFiniteLocallyConstantSheaf.of_iso ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) v'
      (r ≫ q ≫ X₀.ι) (v ≫ q ≫ X₀.ι) (by rw [← hv', Category.assoc])).app F)
  -- the dimension of the generic fibre does not grow
  have hπη : (π ≫ U₀.ι) (genericPoint S') = genericPoint S := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.apply_genericPoint_of_surjective π]
    exact genericPoint_eq_of_isOpenImmersion U₀.ι
  have hdim' : genericFiberDim ((r ≫ j') ≫ fY') < (n + 1 : ℕ) := by
    refine (genericFiberDim_le_of_isEmbedding (r ≫ q ≫ X₀.ι)
      (X₀.ι.isOpenEmbedding.isEmbedding.comp
        (q.isHomeomorph.isEmbedding.comp r.isHomeomorph.isEmbedding))
      _ (j ≫ fY) (π ≫ U₀.ι) hπη ?_).trans_lt hdim
    have h₁ : X₀.ι ≫ j ≫ fY = j₀ ≫ fY₀ ≫ U₀.ι := by
      rw [morphismRestrict_ι, morphismRestrict_ι_assoc]
    rw [Category.assoc r j', hj'f, Category.assoc, Category.assoc, Category.assoc, h₁,
      ← Category.assoc j₀, ← Category.assoc q, hq'.w, Category.assoc]
  have hgen' : ∀ x : X'.nilradical.subscheme, ((r ≫ j') ≫ fY') x = genericPoint S' →
      x ∉ Set.range v' → ∃ y : X'.nilradical.subscheme,
        ((r ≫ j') ≫ fY') y = genericPoint S' ∧ y ∈ Set.range v' ∧ y ⤳ x := by
    have hf : ∀ x, ((r ≫ j') ≫ fY') x = f' (r x) := fun x ↦ by
      rw [Category.assoc, hj'f, Scheme.Hom.comp_apply]
    intro x hx hxv
    rw [hf] at hx
    rw [hrv] at hxv
    obtain ⟨_, ⟨z, rfl⟩, hz, hzx, -⟩ := hgen (r x) (hx ▸ genericPoint_spec S') hxv
    have hrz : r (v' z) = v z := by rw [← Scheme.Hom.comp_apply, hv']
    refine ⟨v' z, ?_, ⟨z, rfl⟩, ?_⟩
    · rw [hf, hrz]
      exact hz.eq (genericPoint_spec S')
    · rw [← r.isHomeomorph.isInducing.specializes_iff, hrz]
      exact hzx
  -- the third step over `S'`
  obtain ⟨W', hW', hP⟩ := exists_hasDirectImageBaseChangeOnPlus_of_dense_smooth hQ hsm aS' fY'
    (r ≫ j') G v' hdim' hgen'
  let K₀ := ((X₀.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
    ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)
  let e : ((r)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
      (((q)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K₀) ≅
      (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G :=
    (((r)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.mapIso
        ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) q X₀.ι).app _).symm ≪≫
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) r (q ≫ X₀.ι)).app _).symm ≪≫
      (((r ≫ q ≫ X₀.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F)
  have hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X'
      (_root_.DerivedCategory.Plus.ι.obj
        (((q)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K₀)) :=
    ((DerivedCategory.boundedConstructible_singleFunctor_obj F 0).mapDerivedCategory_upperStar
      X₀.ι).mapDerivedCategory_upperStar q
  have hX' := HasDirectImageBaseChangeOnPlus.of_surjective_closedImmersion j' r hK
    (hP.of_iso e.symm)
  -- descent along `π` and passage from `U₀` to `S`
  have hπo : IsOpen (π '' (W' : Set S')) := π.isHomeomorph.isOpenMap _ W'.2
  have hU₀' := HasDirectImageBaseChangeOnPlus.of_isFinite_of_surjective π fY₀ j₀ g fY' hY q j'
    hX K₀ (U := π '' (W' : Set S'))
    (hX'.mono (Set.preimage_image_eq _ π.isHomeomorph.injective).subset)
  have hS := HasDirectImageBaseChangeOnPlus.of_restrict_base (fY := fY) j U₀ hU₀'
  refine ⟨U₀.ι ''ᵁ ⟨_, hπo⟩, ?_, hS⟩
  obtain ⟨x, hx⟩ := hW'
  exact ⟨U₀.ι (π x), π x, ⟨x, hx, rfl⟩, rfl⟩

/-- **Deligne's generic constructibility from the smooth case**: granting
`lemma-smooth-morphisms-locally-constant-sheaves`
(`AlgebraicGeometry.Etale.SmoothGenericDirectImage`),
`theorem-generic-constructibility-base-change-rj` holds. -/
theorem exists_hasConstructibleDirectImageBaseChangeOn_of_smoothGenericDirectImage
    (hsm : SmoothGenericDirectImage Λ) {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (fY : Y ⟶ S) [LocallyOfFiniteType fY]
    [QuasiCompact fY] (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      HasConstructibleDirectImageBaseChangeOn Λ fY j F U := by
  refine exists_hasConstructibleDirectImageBaseChangeOn_of_forall (fun n ↦ ?_) aS fY j F
  induction n with
  | zero => exact deligneStatement_zero
  | succ n ih => exact deligneStatement_succ hsm ih

end Etale

end AlgebraicGeometry
