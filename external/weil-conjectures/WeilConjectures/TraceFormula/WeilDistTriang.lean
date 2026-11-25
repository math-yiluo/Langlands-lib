/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Additivity

/-!

# Distinguished triangles of Weil objects

A triangle `A ⟶ B ⟶ C` of Weil objects of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an endomorphism `Φ` is
*distinguished* (`ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang`) if it extends to a
distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of the ambient derived category whose connecting
morphism commutes with the Frobenius structures. The image under `LΦ^*` of the connecting
morphism is formed through the ambient derived pullback, which commutes with the shifts
(`ProEtale.CondensedRing.connectingOfIso`).

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang`: distinguished triangles of Weil
  objects.

## Main results

- `ProEtale.CondensedRing.connectingOfIso_comp`,
  `ProEtale.CondensedRing.connectingOfIso_comp_shift`:
  the transported connecting morphism is natural in its source and its target.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Naturality of the transported connecting morphisms -/

section ConnectingNaturality

variable {Cx Cs Dx Ds : Type*} [Category Cx] [Category Cs] [Category Dx] [Category Ds]
  [HasShift Dx ℤ] [HasShift Ds ℤ] (A : Cx ⥤ Cs) (ιs : Cs ⥤ Ds) (ι : Cx ⥤ Dx) (R : Dx ⥤ Ds)
  [R.CommShift ℤ] (e : A ⋙ ιs ≅ ι ⋙ R)

/-- The connecting morphism of `connectingOfIso` is natural in its source. -/
lemma connectingOfIso_comp {a c c' : Cx} (g : c' ⟶ c)
    (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    connectingOfIso A ιs ι R e (ι.map g ≫ δ) =
      ιs.map (A.map g) ≫ connectingOfIso A ιs ι R e δ := by
  have h := e.hom.naturality g
  simp only [Functor.comp_map] at h
  simp only [connectingOfIso, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h]



/-- The connecting morphism of `connectingOfIso` is natural in its target. -/
lemma connectingOfIso_comp_shift {a a' c : Cx} (g : a ⟶ a')
    (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    connectingOfIso A ιs ι R e (δ ≫ (shiftFunctor Dx (1 : ℤ)).map (ι.map g)) =
      connectingOfIso A ιs ι R e δ ≫ (shiftFunctor Ds (1 : ℤ)).map (ιs.map (A.map g)) := by
  have h := e.inv.naturality g
  simp only [Functor.comp_map] at h
  have h' := (R.commShiftIso (1 : ℤ)).hom.naturality (ι.map g)
  simp only [Functor.comp_map] at h'
  simp only [connectingOfIso, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h', ← Functor.map_comp, h, Functor.map_comp]

end ConnectingNaturality

/-! ### Distinguished triangles of Weil objects -/

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Triangle

/-- A triangle `A ⟶ B ⟶ C` of Weil objects for `Φ` is *distinguished* if it extends to a
distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of the ambient derived category `D(Mod_{ℚ̲̄_ℓ,X})`
whose connecting morphism `δ` commutes with the Frobenius structures: `δ ∘ φ_C = φ_A[1] ∘ LΦ^* δ`,
where `LΦ^* δ` is formed through the ambient derived pullback, which commutes with the
shifts. -/
def WeilBoundedConstructible.IsDistTriang {V : Over (Spec (.of k))} [LocallyOfFiniteType V.hom]
    [QuasiCompact V.hom] [IsSeparated V.hom] {Φ : V ⟶ V} {A B C : WeilBoundedConstructible ℓ Φ}
    (a : A ⟶ B) (b : B ⟶ C) : Prop :=
  ∃ δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.obj
      C.carrier ⟶ (shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.obj
          A.carrier),
    Pretriangulated.Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.map
          a.hom.f)
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.map
          b.hom.f) δ ∈ Pretriangulated.distinguishedTriangles ∧
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.map
          C.str.hom ≫ δ =
        connectingOfIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι
            L((Φ.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
            (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ Φ) δ ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.map
              A.str.hom)

end Triangle

end AlgebraicGeometry.ProEtale.CondensedRing
