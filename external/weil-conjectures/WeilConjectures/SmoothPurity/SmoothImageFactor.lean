/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import WeilConjectures.AlgebraicGeometry.AffineSpaceEmbedding

/-!
# The image factorization of a smooth morphism

Let `f : X ⟶ Y` be a morphism of `k`-schemes (objects of `Over (Spec (.of k))`) which is smooth
of pure relative dimension `d`. Its image is open, and `f` factors as a surjective morphism
`g : X ⟶ U`, smooth of pure relative dimension `d`, followed by an open immersion `ι : U ⟶ Y`.
This file records the property `AlgebraicGeometry.IsSmoothImageFactor f d p` of a pair
`p = (U, g)` of being such a factorization (with `U` separated, quasi-compact and of finite type
over `k`), and proves:

* `AlgebraicGeometry.exists_isSmoothImageFactor`: such a factorization exists;
* `AlgebraicGeometry.IsSmoothImageFactor.epi`: the surjective smooth part `g` is an epimorphism,
  so that the open immersion `ι` is unique (`AlgebraicGeometry.IsSmoothImageFactor.ι_eq`);
* `AlgebraicGeometry.isSmoothImageFactor_comp_openImmersion`: the factorizations of `f ≫ j` for
  an open immersion `j` are those of `f`;
* `AlgebraicGeometry.smoothImageFactor`: a choice of an image factorization, which is the same
  for `f` and for `f ≫ j` (`AlgebraicGeometry.smoothImageFactor_comp_openImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))}

/-- A pair `p = (U, g)` of a separated `k`-scheme `U` of finite type and a morphism `g : X ⟶ U`
is an **image factorization** of `f : X ⟶ Y` in relative dimension `d` if `g` is surjective and
smooth of pure relative dimension `d`, and `f = g ≫ ι` for an open immersion `ι : U ⟶ Y`. The
property only depends on `f` up to composition with open immersions on the target
(`isSmoothImageFactor_comp_openImmersion`). -/
def IsSmoothImageFactor (f : X ⟶ Y) (d : ℕ) (p : Σ U : Over (Spec (.of k)), X ⟶ U) : Prop :=
  LocallyOfFiniteType p.1.hom ∧ QuasiCompact p.1.hom ∧ IsSeparated p.1.hom ∧
    SmoothOfRelativeDimension d p.2.left ∧ Surjective p.2.left ∧
    ∃ ι : p.1 ⟶ Y, IsOpenImmersion ι.left ∧ p.2 ≫ ι = f

namespace IsSmoothImageFactor

variable {f : X ⟶ Y} {d : ℕ} {p : Σ U : Over (Spec (.of k)), X ⟶ U}

/-- The surjective smooth part of an image factorization is an epimorphism. -/
lemma epi (hp : IsSmoothImageFactor f d p) : Epi p.2 := by
  obtain ⟨-, -, -, h, h', -⟩ := hp
  have : Smooth p.2.left := SmoothOfRelativeDimension.smooth (n := d) _
  have : Epi p.2.left := Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left _

/-- The open immersion of an image factorization is unique. -/
lemma ι_eq (hp : IsSmoothImageFactor f d p) {ι ι' : p.1 ⟶ Y} (h : p.2 ≫ ι = f)
    (h' : p.2 ≫ ι' = f) : ι = ι' := by
  have := hp.epi
  exact (cancel_epi p.2).1 (h.trans h'.symm)

end IsSmoothImageFactor

/-- A morphism smooth of pure relative dimension `d` admits an image factorization: the
corestriction to its image, which is open as smooth morphisms are open. -/
lemma exists_isSmoothImageFactor [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    ∃ p, IsSmoothImageFactor f d p := by
  have : Smooth f.left := SmoothOfRelativeDimension.smooth (n := d) _
  let W : Y.left.Opens := ⟨Set.range f.left.base, f.left.isOpenMap.isOpen_range⟩
  have hW : Set.range f.left.base ⊆ Set.range (overRestrictι Y W).left.base := by
    rw [range_overRestrictι]
    exact subset_rfl
  let g₀ : X.left ⟶ (overRestrict Y W).left := IsOpenImmersion.lift _ f.left hW
  have hg₀ : g₀ ≫ (overRestrictι Y W).left = f.left := IsOpenImmersion.lift_fac _ _ _
  let g : X ⟶ overRestrict Y W := Over.homMk g₀
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.hom) hg₀).trans (Over.w f)))
  have hP : MorphismProperty.HasOfPostcompProperty (@SmoothOfRelativeDimension d)
      @IsOpenImmersion :=
    hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict _
      (fun f U hf ↦ IsZariskiLocalAtTarget.restrict hf U)
  refine ⟨⟨overRestrict Y W, g⟩, inferInstance, inferInstance, inferInstance,
    MorphismProperty.of_postcomp _ (W' := @IsOpenImmersion) _ (overRestrictι Y W).left
      inferInstance (hg₀.symm ▸ inferInstance), ⟨fun x ↦ ?_⟩, overRestrictι Y W, inferInstance,
    Over.OverMorphism.ext hg₀⟩
  obtain ⟨y, hy⟩ : (overRestrictι Y W).left.base x ∈ Set.range f.left.base :=
    (range_overRestrictι Y W).le ⟨x, rfl⟩
  refine ⟨y, (overRestrictι Y W).left.isOpenEmbedding.injective ?_⟩
  rw [← hy, ← Scheme.Hom.comp_apply]
  exact congrArg (fun φ ↦ φ.base y) hg₀

/-- The image factorizations of `f ≫ j`, for an open immersion `j`, are those of `f`. -/
lemma isSmoothImageFactor_comp_openImmersion {Z : Over (Spec (.of k))} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j.left] (d : ℕ) :
    IsSmoothImageFactor (f ≫ j) d = IsSmoothImageFactor f d := by
  funext p
  refine propext ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, ι, hι, h⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, ?_⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, ι, hι, h⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, ι ≫ j, ?_,
      by rw [← h, Category.assoc]⟩⟩
  · have hr : Set.range ι.left.base ⊆ Set.range j.left.base := by
      rintro _ ⟨u, rfl⟩
      obtain ⟨x, rfl⟩ := h₅.surj u
      refine ⟨f.left.base x, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, h]
    let ι₀ : p.1.left ⟶ Y.left := IsOpenImmersion.lift _ _ hr
    have hι₀ : ι₀ ≫ j.left = ι.left := IsOpenImmersion.lift_fac _ _ _
    let ι' : p.1 ⟶ Y := Over.homMk ι₀ (by
      rw [← Over.w j, ← Category.assoc, hι₀]
      exact Over.w ι)
    refine ⟨ι', MorphismProperty.of_postcomp _ (W' := @IsOpenImmersion) _ j.left
      inferInstance (hι₀.symm ▸ hι), ?_⟩
    have : Mono j := Over.mono_of_mono_left _
    refine (cancel_mono j).1 ?_
    rw [Category.assoc, ← h]
    congr 1
    exact Over.OverMorphism.ext hι₀
  · rw [Over.comp_left]
    infer_instance

/-- The **chosen image factorization** of `f` in relative dimension `d`: a pair `(U, g)` which is
an image factorization of `f` (`IsSmoothImageFactor`) when one exists, chosen by
`Classical.epsilon` on the property, so that it only depends on `f` up to composition with open
immersions on the target (`smoothImageFactor_comp_openImmersion`). -/
noncomputable def smoothImageFactor (f : X ⟶ Y) (d : ℕ) : Σ U : Over (Spec (.of k)), X ⟶ U :=
  haveI : Nonempty (Σ U : Over (Spec (.of k)), X ⟶ U) := ⟨⟨X, 𝟙 X⟩⟩
  Classical.epsilon (IsSmoothImageFactor f d)

/-- The chosen image factorization of a morphism smooth of pure relative dimension `d` is an
image factorization. -/
lemma isSmoothImageFactor_smoothImageFactor [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    IsSmoothImageFactor f d (smoothImageFactor f d) :=
  haveI : Nonempty (Σ U : Over (Spec (.of k)), X ⟶ U) := ⟨⟨X, 𝟙 X⟩⟩
  Classical.epsilon_spec (exists_isSmoothImageFactor f d)

/-- The chosen image factorization of `f ≫ j`, for an open immersion `j`, is that of `f`. -/
lemma smoothImageFactor_comp_openImmersion {Z : Over (Spec (.of k))} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j.left] (d : ℕ) :
    smoothImageFactor (f ≫ j) d = smoothImageFactor f d := by
  rw [smoothImageFactor, smoothImageFactor, isSmoothImageFactor_comp_openImmersion]

end AlgebraicGeometry
