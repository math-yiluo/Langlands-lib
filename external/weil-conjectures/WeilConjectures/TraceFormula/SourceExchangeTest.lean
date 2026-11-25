/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ProperCompatibilitySupport
public import WeilConjectures.TraceFormula.SupportedClass

/-!

# Test maps for classes on products

A morphism `φ : Z ⟶ RHom(Lp₂^* M, Rp₁^! M)` on `S ⨯ S` is determined by its *test map*
`Rp₁_! (Lp₂^* M ⊗ Z) ⟶ M` (`ProEtale.CondensedRing.classTest`), its uncurried
`Rp₁_! ⊣ Rp₁^!`-adjoint. The test map of the class of a correspondence is the projection formula
followed by the exceptional adjoint of the coefficient map
(`ProEtale.CondensedRing.classTest_correspondenceClassEquiv_symm`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (M : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- The *test map* of a morphism `φ : Z ⟶ RHom(Lp₂^* M, Rp₁^! M)`: its `Rp₁_! ⊣ Rp₁^!`-adjoint
uncurried form `Rp₁_! (Lp₂^* M ⊗ Z) ⟶ M`. -/
noncomputable def classTest {Z : Dᵇc((S ⨯ S).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : Z ⟶ (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M)).obj
      ((boundedConstructibleUpperShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj M)) :
    (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M ⊗ Z) ⟶ M :=
  ((boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : S ⨯ S ⟶ S)).homEquiv _ _).symm
    (uncurry φ)

variable {M}

lemma classTest_injective {Z : Dᵇc((S ⨯ S).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {φ φ' : Z ⟶ (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M)).obj
      ((boundedConstructibleUpperShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj M)}
    (h : classTest ℓ M φ = classTest ℓ M φ') : φ = φ' :=
  uncurry_injective (Equiv.injective _ h)

lemma classTest_comp {Z Z' : Dᵇc((S ⨯ S).left)⟦Profinite.padicAlgClRingObj ℓ⟧} (ψ : Z' ⟶ Z)
    (φ : Z ⟶ (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M)).obj
      ((boundedConstructibleUpperShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj M)) :
    classTest ℓ M (ψ ≫ φ) =
      (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).map (_ ◁ ψ) ≫
        classTest ℓ M φ := by
  rw [classTest, classTest, uncurry_natural_left, Adjunction.homEquiv_naturality_left_symm]

lemma classTest_curry {Z : Dᵇc((S ⨯ S).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M ⊗ Z) ⟶ M) :
    classTest ℓ M (curry (((boundedConstructibleUpperShriekAdjunction ℓ
      (prod.fst : S ⨯ S ⟶ S)).homEquiv _ _) ψ)) = ψ := by
  rw [classTest, uncurry_curry, Equiv.symm_apply_apply]

-- the compactly supported direct images are unfolded in the defeq checks
/-- The test map of a class: the left projection morphism of the support, the composition law
and the exceptional adjoint of the coefficient map. -/
lemma classTest_correspondenceClassEquiv_symm {C : Over (Spec (.of k))} [LocallyOfFiniteType C.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom] (s : C ⟶ S ⨯ S)
    (w : (boundedConstructibleUpperStar _ ℓ (s ≫ prod.snd)).obj M ⟶
      (boundedConstructibleUpperShriek ℓ (s ≫ prod.fst)).obj M) :
    classTest ℓ M ((correspondenceClassEquiv ℓ s M M).symm w) =
      (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).map
          (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ s) _ (𝟙_ _) ≫
            (boundedConstructibleLowerShriek ℓ s).map
              ((ρ_ _).hom ≫ (boundedConstructibleUpperStarComp _ ℓ s prod.snd).inv.app M)) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ s prod.fst).inv.app _ ≫
        (boundedConstructibleLowerShriek ℓ (s ≫ prod.fst)).map w ≫
        (boundedConstructibleUpperShriekAdjunction ℓ (s ≫ prod.fst)).counit.app M := by
  have hP :
      (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).map
          ((boundedConstructibleLowerShriek ℓ s).map
            ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ s prod.fst).hom.app M)) ≫
        (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).map
          ((boundedConstructibleUpperShriekAdjunction ℓ s).counit.app _) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : S ⨯ S ⟶ S)).counit.app M =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ s prod.fst).inv.app _ ≫
        (boundedConstructibleUpperShriekAdjunction ℓ (s ≫ prod.fst)).counit.app M := by
    have h := conjugateEquiv_counit (boundedConstructibleUpperShriekAdjunction ℓ (s ≫ prod.fst))
      ((boundedConstructibleUpperShriekAdjunction ℓ s).comp
        (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : S ⨯ S ⟶ S)))
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ s prod.fst).symm.hom M
    simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj, Iso.symm_hom] at h
    exact h
  simp only [classTest, correspondenceClassEquiv, Equiv.coe_fn_symm_mk,
    Verdier.uncurry_correspondenceClassEquiv_symm, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc] at ⊢
  have hn := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ s prod.fst).inv.naturality w
  simp only [Functor.comp_map] at hn
  simp only [hP]
  simp only [← Category.assoc, hn]

end AlgebraicGeometry.ProEtale.CondensedRing
