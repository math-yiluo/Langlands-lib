/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance

/-!

# Pullbacks along morphisms with image in a closed subscheme

Let `e : P ⟶ X` be a closed immersion of schemes over `Spec k` (for instance a rational point
`point k ⟶ X`, which is a closed immersion since `X` is separated) and `f : Y ⟶ X` a morphism
whose image lies set-theoretically in the image of `e`. If `Le^* M = 0` for some
`M : Dᵇc(X)⟦Λ⟧`, then `Lf^* M = 0`.

The morphism `f` itself need not factor through `e`, but its restriction `r ≫ f` to the reduction
`r : Y_red ⟶ Y` does, so `Lr^* Lf^* M ≅ Lg^* Le^* M = 0`. The reduction `r` is a finite
universal homeomorphism, so `Lr^*` is an equivalence by topological invariance
(`ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction`), whence
`Lf^* M = 0`.

## Main statements

- `ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_of_range_subset`: for `e` a
  closed immersion and `range f ⊆ range e`, `Le^* M = 0` implies `Lf^* M = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

/-- The reduction `Y_red` of a scheme `Y` over `Spec k`, the closed subscheme cut out by the
nilradical, as a scheme over `Spec k`. -/
noncomputable def overReduction (Y : Over (Spec (.of k))) : Over (Spec (.of k)) :=
  Over.mk (Y.left.nilradical.subschemeι ≫ Y.hom)

/-- The closed immersion `Y_red ⟶ Y` of the reduction of a scheme over `Spec k`. -/
noncomputable def overReductionι (Y : Over (Spec (.of k))) : overReduction Y ⟶ Y :=
  Over.homMk Y.left.nilradical.subschemeι

instance (Y : Over (Spec (.of k))) : IsReduced (overReduction Y).left :=
  inferInstanceAs (IsReduced Y.left.nilradical.subscheme)

instance (Y : Over (Spec (.of k))) : IsClosedImmersion (overReductionι Y).left :=
  inferInstanceAs (IsClosedImmersion Y.left.nilradical.subschemeι)

instance (Y : Over (Spec (.of k))) : IsFinite (overReductionι Y).left :=
  inferInstanceAs (IsFinite Y.left.nilradical.subschemeι)

instance (Y : Over (Spec (.of k))) : Surjective (overReductionι Y).left := ⟨by
  change Function.Surjective Y.left.nilradical.subschemeι
  rw [← Set.range_eq_univ, IdealSheafData.range_subschemeι, Scheme.support_nilradical]
  rfl⟩

instance (Y : Over (Spec (.of k))) : IsUniversalHomeomorphism (overReductionι Y).left where

instance (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (overReduction Y).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y.left.nilradical.subschemeι ≫ Y.hom))

instance (Y : Over (Spec (.of k))) [QuasiCompact Y.hom] : QuasiCompact (overReduction Y).hom :=
  inferInstanceAs (QuasiCompact (Y.left.nilradical.subschemeι ≫ Y.hom))

instance (Y : Over (Spec (.of k))) [IsSeparated Y.hom] : IsSeparated (overReduction Y).hom :=
  inferInstanceAs (IsSeparated (Y.left.nilradical.subschemeι ≫ Y.hom))

/-- A morphism `f : Y ⟶ X` over `Spec k` whose image lies in the image of a closed immersion
`e : P ⟶ X` factors through `e` after restriction to the reduction `Y_red ⟶ Y`. -/
lemma exists_overReductionι_comp_eq_of_range_subset {X Y P : Over (Spec (.of k))} (f : Y ⟶ X)
    (e : P ⟶ X) [IsClosedImmersion e.left]
    (hf : Set.range f.left.base ⊆ Set.range e.left.base) :
    ∃ g : overReduction Y ⟶ P, g ≫ e = overReductionι Y ≫ f := by
  set t := (overReductionι Y).left ≫ f.left
  have : Surjective (pullback.snd e.left t) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, Set.preimage_eq_univ_iff]
    exact (Set.range_comp_subset_range (overReductionι Y).left.base f.left.base).trans hf⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd e.left t)
  have hl : (inv (pullback.snd e.left t) ≫ pullback.fst e.left t) ≫ e.left = t := by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  refine ⟨Over.homMk (inv (pullback.snd e.left t) ≫ pullback.fst e.left t) ?_,
    Over.OverMorphism.ext hl⟩
  rw [← Over.w e, ← Category.assoc, hl]
  simp [t, overReduction, overReductionι]

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- Let `e : P ⟶ X` be a closed immersion (for instance a rational point) and `f : Y ⟶ X` a
morphism with image in the image of `e`. If `Le^* M = 0`, then `Lf^* M = 0`: the restriction of
`f` to the reduction `r : Y_red ⟶ Y` factors through `e`, and `Lr^*` is an equivalence by
topological invariance. -/
theorem isZero_boundedConstructibleUpperStar_obj_of_range_subset {X Y P : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (f : Y ⟶ X) (e : P ⟶ X) [IsClosedImmersion e.left]
    (hf : Set.range f.left.base ⊆ Set.range e.left.base) (M :
        Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e).obj M)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M) := by
  obtain ⟨g, hg⟩ := exists_overReductionι_comp_eq_of_range_subset f e hf
  set r := overReductionι Y
  have hr : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)) :=
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map_isZero hM).of_iso
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r f).symm.app M ≪≫
          eqToIso (by rw [hg]) ≪≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g e).app M)
  have := isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction ℓ r
  exact ((boundedConstructibleLowerStar ℓ r).map_isZero hr).of_iso
    (asIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ r).unit.app _))

end AlgebraicGeometry.ProEtale.CondensedRing
