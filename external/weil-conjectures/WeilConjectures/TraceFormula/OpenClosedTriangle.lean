/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated

/-!
# The open–closed triangle in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`

For an open immersion `j : U ⟶ X` and a closed immersion `i : Z ⟶ X` onto its complement, the
open–closed triangle `Rj_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶ Rj_! Lj^* K[1]` of the ambient derived
category (`ProEtale.CondensedRing.exists_distTriang_openClosed`, blueprint
`proposition-extension-zero-restriction-closed-subscheme--8`) is a distinguished triangle of the
pretriangulated category `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`
(`ProEtale.CondensedRing.exists_distTriang_openClosed_boundedConstructible`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.ObjectProperty

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] (P : ObjectProperty D)
  [P.IsTriangulated]

/-- A triangle of a triangulated subcategory whose image in the ambient category is
distinguished for some connecting morphism `δ` is distinguished for the preimage of `δ`. -/
lemma exists_distTriang_of_ι {A B C : P.FullSubcategory} (a : A ⟶ B) (b : B ⟶ C)
    (δ : P.ι.obj C ⟶ (shiftFunctor D (1 : ℤ)).obj (P.ι.obj A))
    (h : Pretriangulated.Triangle.mk (P.ι.map a) (P.ι.map b) δ ∈ distTriang D) :
    ∃ δ' : C ⟶ (shiftFunctor P.FullSubcategory (1 : ℤ)).obj A,
      Pretriangulated.Triangle.mk a b δ' ∈ distTriang P.FullSubcategory := by
  refine ⟨P.fullyFaithfulι.preimage (δ ≫ ((P.ι.commShiftIso (1 : ℤ)).app A).inv), ?_⟩
  refine Pretriangulated.isomorphic_distinguished _ h (P.ι.mapTriangle.obj _)
    (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) ?_)
  simp only [Iso.refl_hom, Functor.map_id, Category.comp_id, Category.id_comp]
  change P.ι.map (P.fullyFaithfulι.preimage _) ≫ _ = δ
  rw [Functor.FullyFaithful.map_preimage]
  exact (Category.assoc _ _ _).trans ((congrArg (δ ≫ ·)
    (Iso.inv_hom_id_app (P.ι.commShiftIso (1 : ℤ)) A)).trans (Category.comp_id _))

end CategoryTheory.ObjectProperty

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Z U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  {j : U ⟶ X} {i : Z ⟶ X} [IsOpenImmersion j.left] [IsClosedImmersion i.left]

/-- **The open–closed triangle in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`**: the counit `Rj_! Lj^* K ⟶ K` and the unit
`K ⟶ Ri_* Li^* K` extend to a distinguished triangle of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
theorem exists_distTriang_openClosed_boundedConstructible
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ : (boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructibleLowerShriek ℓ j).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)),
      Triangle.mk ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K)
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K) δ ∈ distTriang _ := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed ℓ j i hcompl K
  exact ObjectProperty.exists_distTriang_of_ι _ _ _ δ hδ

end AlgebraicGeometry.ProEtale.CondensedRing
