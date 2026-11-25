/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionAdjoint
public import WeilConjectures.PoincareDuality.Biduality.EtaleReadingHomAdjunction
public import WeilConjectures.PoincareDuality.Biduality.EtaleReadingHomTensor

/-!
# The étale reading of finite-coefficient complexes commutes with internal homs

Let `Λ = 𝒪_E ⧸ ℓⁿ` and write `ρ_X = Rν_* ∘ Φ : D(Mod_{Λ_X}) ⥤ D(X_ét, Λ)` for the étale reading
of condensed `Λ`-module objects: the comparison `Φ` of the two finite-coefficient models
(`ProEtale.finiteCoefficientDerivedEquivalence`) followed by `Rν_*`. On bounded constructible
complexes it is `ProEtale.CondensedRing.finiteEtaleReading`.

This file proves that `ρ_X` commutes with internal homs out of bounded constructible complexes
(blueprint `theorem-verdier-biduality`, proof of (i): the comparison is an equivalence
compatible with tensor products, hence with internal homs):
```
ρ_X RHom(A, B) ≅ RHom(ρ_X A, ρ_X B),
```
naturally in `A`. Indeed `Φ` is an equivalence commuting with the derived tensor products, hence
with their right adjoints; `Φ A ≅ ν^* ρ_X A` since `Φ A` is of étale origin
(`ProEtale.CondensedRing.etaleOriginReading`); and `Rν_* RHom(ν^* M, N) ≅ RHom(M, Rν_* N)`, the
right adjoint `Rν_*` of the monoidal `ν^*` satisfying the internal adjunction.

## Main definitions

- `ProEtale.CondensedRing.ambientEtaleReading`: `ρ_X` on the ambient derived category.
- `ProEtale.CondensedRing.finiteEtaleReadingIhomIso`: `ρ_X RHom(A, B) ≅ RHom(ρ_X A, ρ_X B)`,
  naturally in the bounded constructible `A`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The étale reading `ρ_X = Rν_* ∘ Φ` of condensed `𝒪_E ⧸ ℓⁿ`-module objects, on the ambient
derived category. -/
noncomputable def ambientEtaleReading :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X.left)) ⥤
      DerivedCategory (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :=
  (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
    R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])

/-- The left adjoint `Φ⁻¹ ∘ ν^*` of the étale reading `ρ_X = Rν_* ∘ Φ`: the composite of the
adjunction `ν^* ⊣ Rν_*` (`AlgebraicGeometry.ProEtale.derivedComparisonAdjunction`) and of the
equivalence `Φ`. -/
noncomputable def ambientEtaleReadingAdjunction :
    D(ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]) ⋙
        (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).inverse ⊣
      ambientEtaleReading ℓ E n X :=
  (derivedComparisonAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) X.left).comp
    (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).symm.toAdjunction

/-- The tensor isomorphism of the left adjoint `Φ⁻¹ ∘ ν^*` of the étale reading: the tensor
comparison of `D(ν^*)` (`CategoryTheory.Functor.mapDerivedCategoryTensorComparison`) followed by
the one of `Φ⁻¹`, deduced from the compatibility of `Φ` with the tensor products
(`ProEtale.finiteCoefficientModEquivalenceTensorIso`,
`CategoryTheory.Functor.mapDerivedCategoryTensorIsoOfTensorIso`). -/
noncomputable def ambientEtaleReadingLeftAdjointTensorIso :
    (D(ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]) ⋙
      (finiteCoefficientDerivedEquivalence X.left
        (PadicAlgCl.integersModPow ℓ E n)).inverse).TensorIso :=
  Functor.TensorIso.comp
    (asIso (ν^*(X.left)[ModuleCat.{u + 1}
      (integersModPowCoeff.{u} ℓ E n)]).mapDerivedCategoryTensorComparison)
    (Functor.TensorIso.inverse _
      ((finiteCoefficientModEquivalence X.left
        (PadicAlgCl.integersModPow ℓ E n)).functor.mapDerivedCategoryTensorIsoOfTensorIso
          (finiteCoefficientModEquivalenceTensorIso X.left (PadicAlgCl.integersModPow ℓ E n))))

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- On bounded constructible complexes, the counit of the adjunction `Φ⁻¹ ∘ ν^* ⊣ ρ_X` is an
isomorphism: `Φ(M)` is of étale origin (`ProEtale.CondensedRing.etaleOriginReading`). -/
lemma isIso_ambientEtaleReadingAdjunction_counit_app
    (A : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    IsIso ((ambientEtaleReadingAdjunction ℓ E n X).counit.app A.obj) := by
  have := isIso_derivedComparisonAdjunction_counit_app_of_boundedConstructible ℓ E n X.left
    (etaleOriginReading ℓ E n X A)
  rw [ambientEtaleReadingAdjunction, Adjunction.comp_counit_app]
  infer_instance

/-- **The étale reading commutes with internal homs** out of bounded constructible complexes:
`ρ_X RHom(A, B) ≅ RHom(ρ_X A, ρ_X B)` (natural in `A`, see
`ProEtale.CondensedRing.finiteEtaleReadingIhomIso_hom_naturality`). -/
noncomputable def finiteEtaleReadingIhomIso
    (A B : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    (ambientEtaleReading ℓ E n X).obj ((ihom A.obj).obj B.obj) ≅
      (ihom ((finiteEtaleReading ℓ E n X).obj A)).obj ((finiteEtaleReading ℓ E n X).obj B) :=
  (ambientEtaleReadingAdjunction ℓ E n X).ihomComparisonIsoOfCompEq
    (ambientEtaleReadingLeftAdjointTensorIso ℓ E n X)
    (C' := Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) (ObjectProperty.ι _)
    (finiteEtaleReading ℓ E n X) rfl A B
    (hA := isIso_ambientEtaleReadingAdjunction_counit_app ℓ E n X A)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- Naturality of `finiteEtaleReadingIhomIso` in the first variable. -/
lemma finiteEtaleReadingIhomIso_hom_naturality
    {A A' : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧} (f : A ⟶ A')
    (B : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    (ambientEtaleReading ℓ E n X).map ((pre f.hom).app B.obj) ≫
        (finiteEtaleReadingIhomIso ℓ E n X A B).hom =
      (finiteEtaleReadingIhomIso ℓ E n X A' B).hom ≫
        (pre ((finiteEtaleReading ℓ E n X).map f)).app ((finiteEtaleReading ℓ E n X).obj B) :=
  -- `C'` is given as `Dᵇc(X)⟦Λ⟧`, the spelling used in the statement: with the full subcategory
  -- of `boundedConstructible` instead, the kernel has to unfold `finiteEtaleReading` deeply.
  (ambientEtaleReadingAdjunction ℓ E n X).map_pre_app_comp_ihomComparisonIsoOfCompEq_hom
    (ambientEtaleReadingLeftAdjointTensorIso ℓ E n X)
    (C' := Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) (ObjectProperty.ι _)
    (finiteEtaleReading ℓ E n X) rfl f B
    (hA := isIso_ambientEtaleReadingAdjunction_counit_app ℓ E n X A)
    (hA' := isIso_ambientEtaleReadingAdjunction_counit_app ℓ E n X A')

end AlgebraicGeometry.ProEtale.CondensedRing
