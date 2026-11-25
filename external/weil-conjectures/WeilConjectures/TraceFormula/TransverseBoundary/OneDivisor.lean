/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.EtaleDerivedUnbounded
public import WeilConjectures.TraceFormula.TransverseBoundary.Basic

/-!
# Reduction to one divisor

Let `C` be a transverse corner (`AlgebraicGeometry.Scheme.TransverseCorner`). On the open
subscheme `W = Z - X`, which contains `Y - z`, the immersion `i : Z - (X ∪ Y) ⟶ Z - Y` restricts
to the identity of `W - Y`, so `i_! E` restricts to `E` and `M|_W = R j_{W*} E` for the open
immersion `j_W : Z - (X ∪ Y) = W - Y ⟶ W`: only the regular divisor `Y` remains (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`, *Reduction to one divisor*).

## Main definitions

- `AlgebraicGeometry.Scheme.TransverseCorner.W`: the open subscheme `Z - X`.
- `AlgebraicGeometry.Scheme.TransverseCorner.jW`: the open immersion `Z - (X ∪ Y) ⟶ Z - X`.
- `AlgebraicGeometry.Scheme.TransverseCorner.leftDerivedUpperStarBoundaryComplexIso`:
  `M|_W ≅ R j_{W*} E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

/-- A commutative square of open immersions `a ≫ f = b ≫ g` into `X` is cartesian when the
range of `a ≫ f` is the intersection of the ranges of `f` and `g`. -/
lemma Scheme.isPullback_of_isOpenImmersion_of_range_eq {A B C X : Scheme.{u}} {f : A ⟶ X}
    {g : B ⟶ X} {a : C ⟶ A} {b : C ⟶ B} [IsOpenImmersion f] [IsOpenImmersion g]
    [IsOpenImmersion a] (h : a ≫ f = b ≫ g)
    (hr : Set.range (a ≫ f) = Set.range f ∩ Set.range g) : IsPullback a b f g := by
  have hs (s : PullbackCone f g) : Set.range (s.fst ≫ f) ⊆ Set.range (a ≫ f) := by
    rw [hr]
    rintro _ ⟨w, rfl⟩
    refine ⟨⟨s.fst w, rfl⟩, ⟨s.snd w, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]
  refine ⟨⟨h⟩, ⟨PullbackCone.IsLimit.mk h
    (fun s ↦ IsOpenImmersion.lift (a ≫ f) (s.fst ≫ f) (hs s)) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m h₁ _ ↦ ?_)⟩⟩
  · rw [← cancel_mono f, Category.assoc, IsOpenImmersion.lift_fac]
  · rw [← cancel_mono g, Category.assoc, ← h, IsOpenImmersion.lift_fac,
      s.condition]
  · rw [← cancel_mono (a ≫ f), IsOpenImmersion.lift_fac, ← Category.assoc, h₁]

namespace Scheme.TransverseCorner

variable {k : Type u} [Field k] (C : TransverseCorner k)

/-- The open subscheme `W = Z - X` of the surface. -/
def W : C.Z.Opens :=
  ⟨(Set.range C.iX)ᶜ, C.iX.isClosedEmbedding.isClosed_range.isOpen_compl⟩

lemma range_i_j_subset_W : Set.range (C.i ≫ C.j) ⊆ (C.W : Set C.Z) := by
  rw [C.range_i_j]
  exact fun x hx h ↦ hx (Or.inl h)

/-- The open immersion `j_W : Z - (X ∪ Y) ⟶ Z - X`. -/
noncomputable def jW : C.V ⟶ C.W :=
  IsOpenImmersion.lift C.W.ι (C.i ≫ C.j) (by rw [Scheme.Opens.range_ι]; exact C.range_i_j_subset_W)

@[reassoc (attr := simp)]
lemma jW_ι : C.jW ≫ C.W.ι = C.i ≫ C.j :=
  IsOpenImmersion.lift_fac _ _ _

instance : IsOpenImmersion C.jW := by
  have : IsOpenImmersion (C.jW ≫ C.W.ι) := by rw [jW_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ C.W.ι

/-- The square `i ≫ j = j_W ≫ (W ⟶ Z)` is cartesian: `Z - (X ∪ Y) = (Z - Y) ∩ (Z - X)`. -/
lemma isPullback_i_jW : IsPullback C.i C.jW C.j C.W.ι := by
  refine Scheme.isPullback_of_isOpenImmersion_of_range_eq (C.jW_ι).symm ?_
  rw [C.range_i_j, Scheme.Opens.range_ι, C.range_j]
  ext x
  simp [W, and_comm]

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The restriction of `M = Rj_* i_! E` to `W = Z - X` is `R j_{W*} E`, for a bounded below `E`:
étale base change along the open immersion `W ⟶ Z`
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`) for the cartesian square
`AlgebraicGeometry.Scheme.TransverseCorner.isPullback_i_jW`, and `i^* i_! E ≅ E`. -/
noncomputable def leftDerivedUpperStarBoundaryComplexIso
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ)
    [E.IsGE a] :
    (L((C.W.ι)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E) ≅
      (R((C.jW)_*[ModuleCat.{u + 1} Λ])).obj E := by
  let K := ((C.i)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E
  have : K.IsGE a := ((C.i)_!open[ModuleCat.{u + 1} Λ]).isGE_mapDerivedCategory_obj E a
  exact Etale.leftDerivedUpperStarRightDerivedLowerStarIsoOfEtale Λ C.isPullback_i_jW K a ≪≫
    (R((C.jW)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ C.i).app K ≪≫
        (asIso ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction _ C.i).unit.app
          E)).symm)

lemma range_puncturedY_subset_W :
    Set.range (C.puncturedY.ι ≫ C.iY) ⊆ (C.W : Set C.Z) := by
  rintro _ ⟨y, rfl⟩ ⟨x, hx⟩
  have hy : (C.puncturedY.ι ≫ C.iY) y ∈ Set.range C.iX ∩ Set.range C.iY :=
    ⟨⟨x, hx⟩, ⟨_, rfl⟩⟩
  rw [C.range_inter] at hy
  exact y.2 (by simpa using hy)

/-- The closed immersion `Y - z ⟶ Z - X`. -/
noncomputable def puncturedYι : C.puncturedY.toScheme ⟶ C.W :=
  IsOpenImmersion.lift C.W.ι (C.puncturedY.ι ≫ C.iY)
    (by rw [Scheme.Opens.range_ι]; exact C.range_puncturedY_subset_W)

@[reassoc (attr := simp)]
lemma puncturedYι_ι : C.puncturedYι ≫ C.W.ι = C.puncturedY.ι ≫ C.iY :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restriction of `M = Rj_* i_! E` to `Y - z` is the restriction of `R j_{W*} E`. -/
noncomputable def leftDerivedUpperStarPuncturedYBoundaryComplexIso
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ)
    [E.IsGE a] :
    (L((C.puncturedY.ι ≫ C.iY)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E) ≅
      (L((C.puncturedYι)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((C.jW)_*[ModuleCat.{u + 1} Λ])).obj E) :=
  (Etale.leftDerivedUpperStarComp _ C.puncturedYι C.W.ι _ C.puncturedYι_ι.symm).app _ ≪≫
    (L((C.puncturedYι)^*[ModuleCat.{u + 1} Λ])).mapIso
      (C.leftDerivedUpperStarBoundaryComplexIso Λ E a)

end Scheme.TransverseCorner

end AlgebraicGeometry
