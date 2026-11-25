/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorUnderivedNaturality
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorTotalComparison

/-! # Termwise transport of an evaluation-normalized binary comparison

Source: Stacks 03EO and 0FPQ, tensor-Hom naturality and sum-total complexes.
(blueprint: new-sf-ordinary-ringed-tensor-termwise-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
attribute [local instance] Mod.monoidalCategoryCochainComplex

-- Elaborating the concrete tensor instances requires large definitional comparisons.
-- The native and ringed tensor instances have separate coefficient and site universes.
/-- Transport a normalized tensor comparison termwise, without asserting associativity.
Source: Stacks 03EO and 0FPQ.
(blueprint: new-sf-ordinary-ringed-tensor-termwise-comparison).

Proof: the quotient equation for b implies its naturality in both variables, since
precomposition by the quotient projection detects equality. Transport d across b.
The tensor--Hom mate equation and naturality of the Hom comparison prove naturality
in both factors, by transposing and then specializing to the adjunct of an identity.
Thus the resulting components form the natural isomorphism nu. Apply the total
map-bifunctor comparison to nu. The equivalence preserves the coproducts indexed by
p+q=n, so this comparison is invertible in every degree and hence is an isomorphism
of complexes. Its defining coproduct equation gives the displayed summand formula.
No associativity or unit compatibility of the Hom comparison is used.
-/
theorem ordinary_ringed_tensor_termwise_comparison
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u + 1})
    (E : ProEtale.AdicSheaf l Y ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R)
    [E.functor.Additive]
    (H : Functor.uncurry.obj (ordinaryIhomBifunctor l Y) ⋙ E.functor ≅
      E.functor.op.prod E.functor ⋙
        Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)))
    (d : OrdinaryRingedTensorUnderivedData l Y J R E H)
    (b : ∀ P Q : ProEtale.AdicSheaf l Y,
      ((ordinaryTensorBifunctor l Y).obj P).obj Q ≅ Q ⊗ P)
    (hb : ∀ P Q, Mod.tensorπ Q P ≫ (b P Q).hom.hom = Mod.tensorObjπ Q P) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    ∃ (ν : MonoidalCategory.tensor (ProEtale.AdicSheaf l Y) ⋙ E.functor ≅
        E.functor.prod E.functor ⋙ MonoidalCategory.tensor _)
      (τ : MonoidalCategory.tensor (CochainComplex (ProEtale.AdicSheaf l Y) ℤ) ⋙
          E.functor.mapHomologicalComplex (.up ℤ) ≅
        (E.functor.mapHomologicalComplex (.up ℤ)).prod
          (E.functor.mapHomologicalComplex (.up ℤ)) ⋙ MonoidalCategory.tensor _),
      (∀ P Q, E.functor.map (b P Q).hom ≫ ν.hom.app (Q, P) =
        (d.underived P Q).hom) ∧
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (p q n : ℤ) (h : p + q = n),
        E.functor.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
            (τ.hom.app (P, Q)).f n =
          ν.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιTensorObj
            ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)
            ((E.functor.mapHomologicalComplex (.up ℤ)).obj Q) p q n h) := by
  classical
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  obtain ⟨ν, hd⟩ := ordinary_ringed_tensor_underived_naturality l Y J R E H d b hb
  obtain ⟨τ, ht⟩ := ordinary_ringed_tensor_total_comparison l Y J R E ν
  exact ⟨ν, τ, hd, ht⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
