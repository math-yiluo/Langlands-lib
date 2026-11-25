/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.HomologyWeilLowerStar
public import WeilConjectures.TraceFormula.TraceClass
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityLaxMonoidal

/-!

# The restriction of an external product to the diagonal, ambiently

The identification `LΔ^*(K ⊠ N) ≅ K ⊗ N` of bounded constructible complexes
(`ProEtale.CondensedRing.diagUpperStarExternalProductIso`) is, on the ambient derived category,
the comparison `δ` of the derived pullback `LΔ^*` followed by the identifications
`LΔ^* Lp_i^* ≅ L(Δ ≫ p_i)^* = L(𝟙)^* ≅ 𝟭`
(`ProEtale.CondensedRing.diagUpperStarExternalProductIso_hom_hom`). This is the form in which the
compatibilities of nearby cycles with external products are stated.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The ambient form of the restriction `LΔ^*(K ⊠ N) ≅ K ⊗ N` of an external product to the
diagonal: the comparison `δ` of `LΔ^*` and the identifications `LΔ^* Lp_i^* ≅ L(𝟙)^* ≅ 𝟭`. -/
lemma diagUpperStarExternalProductIso_hom_hom (K N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h₁ : (diag X).left ≫ (prod.fst : X ⨯ X ⟶ X).left = 𝟙 X.left)
    (h₂ : (diag X).left ≫ (prod.snd : X ⨯ X ⟶ X).left = 𝟙 X.left) :
    (diagUpperStarExternalProductIso ℓ K N).hom.hom =
      Functor.OplaxMonoidal.δ L(((diag X).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
          ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj K).obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj N).obj ≫
        (((leftDerivedUpperStarComp _ (diag X).left (prod.fst : X ⨯ X ⟶ X).left).inv.app K.obj ≫
            eqToHom (by rw [h₁]) ≫
            (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app K.obj) ⊗ₘ
          ((leftDerivedUpperStarComp _ (diag X).left (prod.snd : X ⨯ X ⟶ X).left).inv.app N.obj ≫
            eqToHom (by rw [h₂]) ≫
            (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app N.obj)) := by
  simp only [diagUpperStarExternalProductIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.app_hom, Iso.app_inv, eqToIso.hom, Functor.Monoidal.μIso_inv,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.tensorHom_hom',
    boundedConstructibleUpperStar_δ_hom, ObjectProperty.eqToHom_hom,
    boundedConstructibleUpperStarComp_inv_app_hom,
    boundedConstructibleUpperStarId_hom_app_hom]

end AlgebraicGeometry.ProEtale.CondensedRing
