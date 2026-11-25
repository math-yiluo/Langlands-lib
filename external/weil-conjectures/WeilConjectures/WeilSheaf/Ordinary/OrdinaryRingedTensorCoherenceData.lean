/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Evaluation-normalized ordinary tensor coherence data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] Mod.monoidalCategoryCochainComplex

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u + 1})
  (E : ProEtale.AdicSheaf l Y ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R)
  [E.functor.Additive]
  (H : Functor.uncurry.obj (ordinaryIhomBifunctor l Y) ⋙ E.functor ≅
    E.functor.op.prod E.functor ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)))

/-- A binary comparison fixed uniquely by its tensor--Hom mate.
Source: Stacks 06YS, 06YU (blueprint: new-sf-ordinary-ringed-tensor-coherence-data). -/
structure OrdinaryRingedTensorUnderivedData where
  underived (P Q : ProEtale.AdicSheaf l Y) :
    E.functor.obj (((ordinaryTensorBifunctor l
      Y).obj P).obj Q) ≅
      (SheafOfModules.monoidalCategory R).tensorObj (E.functor.obj Q) (E.functor.obj P)
  uncurry (P Q I : ProEtale.AdicSheaf l Y)
      (f : Q ⟶ ((ordinaryIhomBifunctor l
      Y).obj (op P)).obj I) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    (underived P Q).inv ≫
        E.functor.map (((Mod.ihomAdjunction P).homEquiv Q I).symm f) =
      (β_ (E.functor.obj Q) (E.functor.obj P)).hom ≫
        ((SheafOfModules.tensorHomAdjunction R (E.functor.obj P)).homEquiv
          (E.functor.obj Q) (E.functor.obj I)).symm
            (E.functor.map f ≫ H.hom.app (op P, I))

set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the concrete tensor instances requires large definitional comparisons.
set_option maxHeartbeats 1200000 in
-- Elaborating the concrete tensor instances requires large definitional comparisons.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A normalized comparison on the existing ordinary and ringed cochain tensors.
Source: Stacks 0FPT (blueprint: new-sf-ordinary-ringed-tensor-coherence-data). -/
structure OrdinaryRingedTensorChainComparison
    (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        Y) ℤ,
      ordinaryTensorTotal l Y P Q ≅ Q ⊗ P)
    (d : OrdinaryRingedTensorUnderivedData l Y J R E H) where
  tensor : MonoidalCategory.tensor (CochainComplex (ProEtale.AdicSheaf l
      Y) ℤ) ⋙
        E.functor.mapHomologicalComplex (.up ℤ) ≅
    (E.functor.mapHomologicalComplex (.up ℤ)).prod
      (E.functor.mapHomologicalComplex (.up ℤ)) ⋙
        MonoidalCategory.tensor
          (CochainComplex (RingedTensorModules.{u + 1, u + 1, u + 1} J R) ℤ)
  summand (P Q : CochainComplex (ProEtale.AdicSheaf l
      Y) ℤ)
      (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n) :
    E.functor.map (HomologicalComplex.ιMapBifunctor P Q
        (ordinaryTensorBifunctor l Y)
        (.up ℤ) p q n hpq) ≫
      E.functor.map ((κ P Q).hom.f n) ≫
        (tensor.hom.app (Q, P)).f n =
      (p * q).negOnePow • ((d.underived (P.X p) (Q.X q)).hom ≫
        RingedForgetTensorTransposition.tensorSummand J R
          ((E.functor.mapHomologicalComplex (.up ℤ)).obj Q)
          ((E.functor.mapHomologicalComplex (.up ℤ)).obj P) q p n hqp)
  associativity (P Q N : CochainComplex (ProEtale.AdicSheaf l
      Y) ℤ) :
    let G := E.functor.mapHomologicalComplex (.up ℤ)
    G.map (α_ P Q N).hom ≫ tensor.hom.app (P, Q ⊗ N) ≫
        (G.obj P ◁ tensor.hom.app (Q, N)) =
      tensor.hom.app (P ⊗ Q, N) ≫ (tensor.hom.app (P, Q) ▷ G.obj N) ≫
        (α_ (G.obj P) (G.obj Q) (G.obj N)).hom

/-- The Hom comparison is the one arising from a coherent ordinary tensor comparison.
The normalization equations fix every tensorator uniquely. The first clause retains
symmetry relative to the actual ordinary balanced tensor. This is a property of
specified data, not a choice of an unrelated monoidal structure.
Source: Stacks 06YS, 06YU, 0FPT
(blueprint: new-sf-ordinary-ringed-tensor-coherence-data). -/
def OrdinaryRingedTensorCoherence : Prop :=
  (∀ (d : OrdinaryRingedTensorUnderivedData l Y J R E H)
    (P Q : ProEtale.AdicSheaf l Y),
    ∃ s : ((ordinaryTensorBifunctor l Y).obj Q).obj P ⟶
        ((ordinaryTensorBifunctor l Y).obj P).obj Q,
      (letI := SheafOfModules.isMonoidal_W_independentCoefficients R
       letI := SheafOfModules.monoidalCategory R
       letI := SheafOfModules.symmetricCategory R
       E.functor.map s ≫ (d.underived P Q).hom =
         (d.underived Q P).hom ≫ (β_ (E.functor.obj P) (E.functor.obj Q)).hom) ∧
      Mod.tensorπ P Q ≫ s.hom = (β_ P.X Q.X).hom ≫ Mod.tensorπ Q P) ∧
  ∀ (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
      ordinaryTensorTotal l Y P Q ≅ Q ⊗ P),
    (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
      Mod.tensorπ (Q.X q) (P.X p) ≫
          (HomologicalComplex.ιMapBifunctor P Q (ordinaryTensorBifunctor l Y)
            (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
        (p * q).negOnePow • (Mod.tensorObjπ (Q.X q) (P.X p) ≫
          (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)) →
    ∀ d : OrdinaryRingedTensorUnderivedData l Y J R E H,
      Nonempty (OrdinaryRingedTensorChainComparison l Y J R E H κ d)

end AlgebraicGeometry.ProEtaleWeilSheaf
