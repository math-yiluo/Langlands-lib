/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTripleComplex

/-! Shared data and component notation for the explicit associator chain step. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] Mod.monoidalCategoryCochainComplex

-- Elaborating the cochain tensor fields of this structure unfolds deep instance terms.
structure NativeWeilTensorRingedAssociatorChainData
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    where
  adj : T ⊣₂ ihomBifunctor k₀ l X
  e : Functor.uncurry.obj T ⋙
      Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
        Functor.uncurry.obj
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  he : ∀ (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I),
    e.inv.app (P, Q) ≫
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (((adj.adj P).homEquiv Q I).symm f) =
      ((Mod.ihomAdjunction P.carrier).homEquiv Q.carrier I.carrier).symm f.hom.f
  chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
    ((Endofunctor.IsoAlgebra.forget
      (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q T) ≅
      ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        (((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
  hchain : ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (h : p + q = n),
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
        (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n h) ≫
          (chain P Q).hom.f n =
      e.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιMapBifunctor
        (((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
        (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (.up ℤ) p q n h
  b : NativeWeilTensorRingedBridge k₀ l X
  A : NativeWeilRingedTensorComplexes b T adj
  κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
    ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅ Q ⊗ P
  hκ : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
      (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
    Mod.tensorπ (Q.X q) (P.X p) ≫
        (HomologicalComplex.ιMapBifunctor P Q
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
      (p * q).negOnePow •
        (Mod.tensorObjπ (Q.X q) (P.X p) ≫
          (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)

abbrev nativeChainForgetU
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T] :=
  (Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)

def nativeChainForgetC
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T) (P Q : CochainComplex
      (ProEtaleWeilSheaf k₀ l X) ℤ) :
    nativeChainForgetU (T := T).obj (CochainComplex.mapBifunctor Q P T) ≅
      nativeChainForgetU (T := T).obj P ⊗ nativeChainForgetU (T := T).obj Q :=
  D.chain Q P ≪≫ D.κ (nativeChainForgetU (T := T).obj Q) (nativeChainForgetU (T := T).obj P)

def nativeChainForgetComponent
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (n p q : ℤ) (h : p + q = n) :
    letI _mC : MonoidalCategory (CochainComplex
      (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
      Mod.monoidalCategoryCochainComplex
    letI := _mC.toMonoidalCategoryStruct
    Prop :=
  letI _mC : MonoidalCategory (CochainComplex
      (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
      Mod.monoidalCategoryCochainComplex
  letI := _mC.toMonoidalCategoryStruct
  let U := nativeChainForgetU (T := T)
  let V := Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback k₀ l X)
  let c := nativeChainForgetC (T := T) D
  V.map (HomologicalComplex.ιMapBifunctor N (Q.mapBifunctor P T) T
      (.up ℤ) p q n h) ≫
      (U.map (nativeRingedAssociatorComplex D.b T D.adj D.A P Q N).hom ≫
        (c P (nativeTensorComplex T Q N)).hom ≫
        (U.obj P ◁ (c Q N).hom)).f n =
    V.map (HomologicalComplex.ιMapBifunctor N (Q.mapBifunctor P T) T
      (.up ℤ) p q n h) ≫
      ((c (nativeTensorComplex T P Q) N).hom ≫
        ((c P Q).hom ▷ U.obj N) ≫
        (α_ (U.obj P) (U.obj Q) (U.obj N)).hom).f n

def nativeChainForgetAssociator
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T) :
    letI _mC : MonoidalCategory (CochainComplex
      (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
      Mod.monoidalCategoryCochainComplex
    letI := _mC.toMonoidalCategoryStruct
    Prop :=
  letI _mC : MonoidalCategory (CochainComplex
      (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
      Mod.monoidalCategoryCochainComplex
  letI := _mC.toMonoidalCategoryStruct
  let U := nativeChainForgetU (T := T)
  let c := nativeChainForgetC (T := T) D
  ∀ P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
    U.map (nativeRingedAssociatorComplex D.b T D.adj D.A P Q N).hom ≫
        (c P (nativeTensorComplex T Q N)).hom ≫
        (U.obj P ◁ (c Q N).hom) =
      (c (nativeTensorComplex T P Q) N).hom ≫
        ((c P Q).hom ▷ U.obj N) ≫
        (α_ (U.obj P) (U.obj Q) (U.obj N)).hom

-- The ringed cochain monoidal structure needs a deep search for its graded tensor instances.
def nativeRingedAssociatorComponent
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (n : ℤ) : Prop :=
  letI _mB := SheafOfModules.isMonoidal_W_independentCoefficients D.b.R
  letI _mC := SheafOfModules.monoidalCategory D.b.R
  let Ec := D.b.native.functor.mapHomologicalComplex (.up ℤ)
  (Ec.map (nativeRingedAssociatorComplex D.b T D.adj D.A P Q N).hom ≫
      (nativeRingedTripleRight D.b T D.adj D.A P Q N).hom).f n =
    ((nativeRingedTripleLeft D.b T D.adj D.A P Q N).hom ≫
      (α_ (Ec.obj P) (Ec.obj Q) (Ec.obj N)).hom).f n

end AlgebraicGeometry.ProEtaleWeilSheaf
