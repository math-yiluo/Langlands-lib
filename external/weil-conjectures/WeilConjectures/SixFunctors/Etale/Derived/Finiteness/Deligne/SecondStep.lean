/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.FiniteBoundary
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.FirstStep
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Transport

/-!
# The second step of Deligne's generic constructibility: smooth source, locally constant sheaf

Let `j : X ⟶ Y` be an immersion of finite type `S`-schemes with `X` smooth over `S`, and
`F` a finite locally constant sheaf on `X`, with generic fibre of dimension `≤ n`. Granting
the generic constructibility theorem in generic dimension `< n` and the smooth case
`lemma-smooth-morphisms-locally-constant-sheaves`, there is a nonempty open of `S` over which
`Rj_* F` is bounded constructible and commutes with every base change from a noetherian scheme
(`AlgebraicGeometry.Etale.exists_hasDirectImageBaseChangeOnPlus_of_smooth`).

The question being local on `Y`, cover `Y` by finitely many affine opens, embed each into a
projective space over `S` and pass to the scheme-theoretic closure `Ȳ` of `X`. By the first step,
over an open `G ⊆ Ȳ` whose complement is finite over a nonempty open of `S`, the direct image
is bounded constructible and commutes with base change; and so is the direct image to `S`, by the
smooth case. The finite boundary argument
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_finite_boundary`) concludes over `Ȳ`
(`AlgebraicGeometry.Etale.exists_hasDirectImageBaseChangeOnPlus_of_isClosedImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- A finite locally constant sheaf is constructible, for the trivial stratification. -/
lemma Scheme.IsConstructibleSheaf.of_isFiniteLocallyConstantSheaf {X : Scheme.{u}}
    {Λ : Type (u + 1)} [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] : IsConstructibleSheaf F :=
  ⟨Stratification.trivial X, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) F⟩

/-- Two nonempty opens of an irreducible space meet. -/
lemma Scheme.Opens.nonempty_inf {S : Scheme.{u}} [IrreducibleSpace S] {U V : S.Opens}
    (hU : (U : Set S).Nonempty) (hV : (V : Set S).Nonempty) :
    ((U ⊓ V : S.Opens) : Set S).Nonempty := by
  have := (IrreducibleSpace.isIrreducible_univ S).2 U V U.isOpen V.isOpen (by simpa using hU)
    (by simpa using hV)
  simpa using this

/-- The restriction of a finite morphism over an open is finite over every smaller open. -/
lemma isFinite_morphismRestrict_of_le {X S : Scheme.{u}} (f : X ⟶ S) {U W : S.Opens}
    (hUW : U ≤ W) [IsFinite (f ∣_ W)] : IsFinite (f ∣_ U) := by
  let φ : (U : Scheme.{u}) ⟶ W := IsOpenImmersion.lift W.ι U.ι (by
    rw [Opens.range_ι, Opens.range_ι]; exact hUW)
  have hφ : φ ≫ W.ι = U.ι := IsOpenImmersion.lift_fac _ _ _
  have hbig : IsPullback (f ⁻¹ᵁ U).ι (f ∣_ U) f (φ ≫ W.ι) := by
    rw [hφ]; exact (isPullback_morphismRestrict f U).flip
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right' hbig (isPullback_morphismRestrict f W).flip).flip.flip inferInstance

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **The second step over a closed subscheme of projective space**: let `cl : Ȳ ⟶ ℙ^N_S` be a
closed immersion and `j : X ⟶ Ȳ` an immersion with `X` smooth and of finite type over `S`
(hence separated), and generic fibre of dimension `< n + 1`. Granting the theorem in generic
dimension `< n` and the smooth case, for a finite locally constant sheaf `F` on `X` there is a
nonempty open of `S` over which `Rj_* F` is bounded constructible and commutes with base change.
-/
theorem exists_hasDirectImageBaseChangeOnPlus_of_isClosedImmersion {n : ℕ}
    (hQ : DeligneStatement Λ n) (hsm : SmoothGenericDirectImage Λ) {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] {N : Type u} [Finite N]
    (cl : Y ⟶ ℙ(N; S)) [IsClosedImmersion cl] (j : X ⟶ Y) [IsImmersion j]
    [Smooth (j ≫ cl ≫ ℙ(N; S) ↘ S)] [QuasiCompact (j ≫ cl ≫ ℙ(N; S) ↘ S)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    (hdim : genericFiberDim (j ≫ cl ≫ ℙ(N; S) ↘ S) < (n + 1 : ℕ)) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ HasDirectImageBaseChangeOnPlus Λ
      (cl ≫ ℙ(N; S) ↘ S) j ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U := by
  have := Scheme.IsConstructibleSheaf.of_isFiniteLocallyConstantSheaf F
  have : IsSeparated (j ≫ cl ≫ ℙ(N; S) ↘ S) := inferInstance
  -- the standard affine charts
  let Uα (i : N) : Y.Opens := cl ⁻¹ᵁ ProjectiveSpace.standardOpen N S i
  have hU : ⨆ i, Uα i = ⊤ := by
    simp only [Uα, ← Scheme.Hom.preimage_iSup, ProjectiveSpace.iSup_standardOpen,
      Scheme.Hom.preimage_top]
  let e (i : N) : (Uα i).toScheme ⟶ 𝔸({j : N // j ≠ i}; S) :=
    (cl ∣_ ProjectiveSpace.standardOpen N S i) ≫ (ProjectiveSpace.standardOpenIso N S i).hom
  have he (i : N) : e i ≫ 𝔸({j : N // j ≠ i}; S) ↘ S = (Uα i).ι ≫ cl ≫ ℙ(N; S) ↘ S := by
    simp only [e, Category.assoc, ProjectiveSpace.standardOpenIso_hom_over]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  obtain ⟨G, W, hWne, hG, hfin⟩ := exists_hasDirectImageBaseChangeOnPlus_of_coordinates hQ aS
    (cl ≫ ℙ(N; S) ↘ S) j F hdim Uα hU (fun i ↦ {j : N // j ≠ i}) e he
  obtain ⟨U₃, hU₃ne, ha⟩ := hsm aS (j ≫ cl ≫ ℙ(N; S) ↘ S) F
  refine ⟨W ⊓ U₃, Scheme.Opens.nonempty_inf hWne hU₃ne, ?_⟩
  have := hfin _ G.closedComplement (by rw [Opens.range_closedComplement])
  have := isFinite_morphismRestrict_of_le (G.closedComplement ≫ cl ≫ ℙ(N; S) ↘ S)
    (inf_le_left : W ⊓ U₃ ≤ W)
  exact HasDirectImageBaseChangeOnPlus.of_finite_boundary aS (cl ≫ ℙ(N; S) ↘ S) j G
    G.closedComplement (Opens.range_closedComplement G) (W ⊓ U₃)
    (hG.mono (Set.subset_univ _)) (ha.mono fun _ h ↦ h.2)

/-- **The second step for an affine target**: as
`AlgebraicGeometry.Etale.exists_hasDirectImageBaseChangeOnPlus_of_isClosedImmersion`, for an
immersion `j : X ⟶ Y` into an affine `S`-scheme `Y` of finite type: embed `Y` into a projective
space over `S`, apply the second step to the scheme-theoretic closure of `X`, then compose with
the closed immersion into the closure of `Y`, and restrict to the open `Y` of that closure. -/
theorem exists_hasDirectImageBaseChangeOnPlus_of_smooth_of_isAffine {n : ℕ}
    (hQ : DeligneStatement Λ n) (hsm : SmoothGenericDirectImage Λ) {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] [IsAffine Y] (fY : Y ⟶ S)
    [LocallyOfFiniteType fY] [QuasiCompact fY] (j : X ⟶ Y) [IsImmersion j] [Smooth (j ≫ fY)]
    [QuasiCompact (j ≫ fY)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    (hdim : genericFiberDim (j ≫ fY) < (n + 1 : ℕ)) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ HasDirectImageBaseChangeOnPlus Λ fY j
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U := by
  obtain ⟨N, _, ιY, hιY, hιYover⟩ := exists_isImmersion_projectiveSpace fY
  have : QuasiCompact ιY := by
    have : QuasiCompact (ιY ≫ ℙ(N; S) ↘ S) := by rw [hιYover]; infer_instance
    exact QuasiCompact.of_comp ιY (ℙ(N; S) ↘ S)
  -- the scheme-theoretic closure of `X` in `ℙ^N_S`
  let f₀ := j ≫ ιY
  have hf₀ : f₀ ≫ ℙ(N; S) ↘ S = j ≫ fY := by simp [f₀, hιYover]
  have : QuasiCompact f₀ := by
    have : QuasiCompact (f₀ ≫ ℙ(N; S) ↘ S) := by rw [hf₀]; infer_instance
    exact QuasiCompact.of_comp f₀ (ℙ(N; S) ↘ S)
  have hjb : f₀.toImage ≫ f₀.imageι ≫ ℙ(N; S) ↘ S = j ≫ fY := by
    rw [Scheme.Hom.toImage_imageι_assoc, hf₀]
  have : Smooth (f₀.toImage ≫ f₀.imageι ≫ ℙ(N; S) ↘ S) := by rw [hjb]; infer_instance
  have : QuasiCompact (f₀.toImage ≫ f₀.imageι ≫ ℙ(N; S) ↘ S) := by rw [hjb]; infer_instance
  obtain ⟨U, hU, hP⟩ := exists_hasDirectImageBaseChangeOnPlus_of_isClosedImmersion hQ hsm aS
    f₀.imageι f₀.toImage F (hjb ▸ hdim)
  refine ⟨U, hU, ?_⟩
  -- the scheme-theoretic closure of `Y`, containing that of `X`
  let ιY' := ιY.toImage
  have hm : (j ≫ ιY') ≫ ιY.imageι = f₀ := by simp [ιY', f₀]
  have H : ιY.imageι.ker ≤ f₀.imageι.ker := hm ▸ Scheme.Hom.ker_le_ker_imageι_comp _ _
  let m := IsClosedImmersion.lift ιY.imageι f₀.imageι H
  have hm₁ : m ≫ ιY.imageι = f₀.imageι := IsClosedImmersion.lift_fac _ _ _
  have hm₂ : f₀.toImage ≫ m = j ≫ ιY' := Scheme.Hom.toImage_lift _ _ hm H
  have hP' : HasDirectImageBaseChangeOnPlus Λ (ιY.imageι ≫ ℙ(N; S) ↘ S) (j ≫ ιY')
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U := by
    rw [← hm₂]
    refine HasDirectImageBaseChangeOnPlus.comp_isClosedImmersion f₀.toImage m ?_
    rw [← Category.assoc, hm₁]
    exact hP
  -- restriction to the open `Y` of the closure of `Y`
  let O := ιY'.opensRange
  have hR := hP'.restrict (j ≫ ιY') O
  have hTop : (⊤ : X.Opens) = (j ≫ ιY') ⁻¹ᵁ O := by
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, true_iff]
    exact ⟨j x, rfl⟩
  let eX : X ⟶ ((j ≫ ιY') ⁻¹ᵁ O).toScheme := X.topIso.inv ≫ (X.isoOfEq hTop).hom
  have heX : eX ≫ ((j ≫ ιY') ⁻¹ᵁ O).ι = 𝟙 X := by simp [eX]
  have : IsIso eX := by dsimp [eX]; infer_instance
  refine hR.of_iso_data ιY'.isoOpensRange.hom eX ?_ ?_ ?_
  · rw [Scheme.Hom.isoOpensRange_hom_ι_assoc, Scheme.Hom.toImage_imageι_assoc, hιYover]
  · rw [← cancel_mono O.ι, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, heX, Category.id_comp]
  · exact ((upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).app _).symm ≪≫
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) eX ((j ≫ ιY') ⁻¹ᵁ O).ι (𝟙 X)
        heX.symm).app _

/-- A finite family of nonempty opens of an irreducible space has nonempty intersection. -/
lemma _root_.AlgebraicGeometry.Scheme.Opens.nonempty_finset_inf {S : Scheme.{u}}
    [IrreducibleSpace S] {ι : Type*} (s : Finset ι) (V : ι → S.Opens)
    (h : ∀ i ∈ s, ((V i : S.Opens) : Set S).Nonempty) : ((s.inf V : S.Opens) : Set S).Nonempty := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨x⟩ := (inferInstance : Nonempty S)
    exact ⟨x, by simp⟩
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    exact Scheme.Opens.nonempty_inf (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- **The second step of Deligne's generic constructibility**: let `S` be integral of finite type
over a field, `j : X ⟶ Y` an immersion of finite type `S`-schemes with `X` smooth over `S`
and generic fibre of dimension `< n + 1`, and `F` a finite locally constant sheaf on `X`.
Granting the theorem in generic dimension `< n` and the smooth case, there is a nonempty open of
`S` over which `Rj_* F` is bounded constructible and commutes with every base change from a
noetherian scheme. -/
theorem exists_hasDirectImageBaseChangeOnPlus_of_smooth {n : ℕ}
    (hQ : DeligneStatement Λ n) (hsm : SmoothGenericDirectImage Λ) {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (fY : Y ⟶ S) [LocallyOfFiniteType fY]
    [QuasiCompact fY] (j : X ⟶ Y) [IsImmersion j] [Smooth (j ≫ fY)] [QuasiCompact (j ≫ fY)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    (hdim : genericFiberDim (j ≫ fY) < (n + 1 : ℕ)) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ HasDirectImageBaseChangeOnPlus Λ fY j
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (fY ≫ aS)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (j ≫ fY ≫ aS)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (fY ≫ aS)
  -- a finite cover of `Y` by affine opens
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : Y.affineOpens ↦ (U : Set Y))
    (fun U ↦ U.1.isOpen) fun y _ ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hyU⟩
  let ι := {U // U ∈ t}
  let V (i : ι) : Y.Opens := i.1.1
  have hV : ⨆ i, V i = ⊤ := by
    refine eq_top_iff.2 fun y _ ↦ ?_
    obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨⟨U, hU⟩, hyU⟩
  have hloc (i : ι) : ∃ W : S.Opens, (W : Set S).Nonempty ∧
      HasDirectImageBaseChangeOnPlus Λ ((V i).ι ≫ fY) (j ∣_ V i)
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (j ⁻¹ᵁ V i).ι).obj F)) W := by
    have : IsAffine (V i) := i.1.2
    have : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (j ⁻¹ᵁ V i).ι).obj F) :=
      IsFiniteLocallyConstantSheaf.upperStar _ F
    have he : (j ∣_ V i) ≫ (V i).ι ≫ fY = (j ⁻¹ᵁ V i).ι ≫ j ≫ fY := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    have : Smooth ((j ∣_ V i) ≫ (V i).ι ≫ fY) := by rw [he]; infer_instance
    have : QuasiCompact ((j ∣_ V i) ≫ (V i).ι ≫ fY) := by rw [he]; infer_instance
    exact exists_hasDirectImageBaseChangeOnPlus_of_smooth_of_isAffine hQ hsm aS ((V i).ι ≫ fY)
      (j ∣_ V i) _ (by rw [he]; exact (genericFiberDim_comp_le _ _).trans_lt hdim)
  choose W hWne hW using hloc
  have : Fintype ι := Fintype.ofFinite ι
  refine ⟨Finset.univ.inf W,
    Scheme.Opens.nonempty_finset_inf _ W fun i _ ↦ hWne i, ?_⟩
  refine HasDirectImageBaseChangeOnPlus.of_openCover j V hV fun i ↦ ?_
  refine ((hW i).mono fun x hx ↦ (Finset.inf_le (f := W) (Finset.mem_univ i)) hx).of_iso ?_
  exact ((((j ⁻¹ᵁ V i).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F
    |>.symm

end Etale

end AlgebraicGeometry
