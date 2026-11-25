/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChain
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedStructure
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison

/-! # Localization of the signed native forgetting associator square

Source: Stacks 0FPQ, 06YU, 0FPT; naturality of localization factors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local implicit_reducible] Mod.monoidalCategoryCochainComplex Monoidal.induced

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory DerivedCategory.Q instCategoryDerivedCategory
  nativeRingedAssociatorComplex nativeRingedTripleLeft nativeRingedTripleRight
  SheafOfModules.monoidalCategory

-- Keep the concrete total and localization constructions folded when applying naturality.
/-- The signed chain associator square commutes after exact forgetting and localization.
Source: Stacks 0FPQ, 06YU, 0FPT
(blueprint: lem-sf-native-weil-ringed-forget-localization).

Proof: apply naturality of the exact-forgetting localization factor to the
native chain associator, then map the signed chain equality into the ordinary
derived category. Functoriality gives precisely the displayed square. -/
theorem nativeRingedAssociatorComplex_forget_localization
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : T ⊣₂ ihomBifunctor k₀ l X)
    (e : Functor.uncurry.obj T ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (he : ∀ (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I),
      e.inv.app (P, Q) ≫
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
            (((adj.adj P).homEquiv Q I).symm f) =
        ((Mod.ihomAdjunction P.carrier).homEquiv Q.carrier I.carrier).symm f.hom.f)
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hchain : ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
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
          (.up ℤ) p q n h)
    (b : NativeWeilTensorRingedBridge k₀ l X)
    (A : NativeWeilRingedTensorComplexes b T adj) :
    letI mC : MonoidalCategory (CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
      Mod.monoidalCategoryCochainComplex
    letI := mC.toMonoidalCategoryStruct
    ∀ (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅ Q ⊗ P)
    (_hκ : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
        Mod.tensorπ (Q.X q) (P.X p) ≫
            (HomologicalComplex.ιMapBifunctor P Q
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
          (p * q).negOnePow •
            (Mod.tensorObjπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιTensorObj Q P q p n hqp).hom))
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
    let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
    let V := U.mapHomologicalComplex (.up ℤ)
    let F := nativeForget k₀ l X
    let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
    let qA := DerivedCategory.Q (C := ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    let ε := U.mapDerivedCategoryFactors
    let c (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
        V.obj (nativeTensorComplex T P Q) ≅ V.obj P ⊗ V.obj Q :=
      chain Q P ≪≫ κ (V.obj Q) (V.obj P)
    let pq := nativeTensorComplex T P Q
    let qn := nativeTensorComplex T Q N
    let leftTotal := c pq N ≪≫ whiskerRightIso (c P Q) (V.obj N)
    let rightTotal := c P qn ≪≫ whiskerLeftIso (V.obj P) (c Q N)
    F.map (q.map (nativeRingedAssociatorComplex b T adj A P Q N).hom) ≫
        ε.hom.app (nativeTensorComplex T P qn) ≫ qA.map rightTotal.hom =
      (ε.hom.app (nativeTensorComplex T pq N) ≫ qA.map leftTotal.hom) ≫
        qA.map (mC.associator (V.obj P) (V.obj Q) (V.obj N)).hom := by
  classical
  letI mC : MonoidalCategory (CochainComplex (ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
    Mod.monoidalCategoryCochainComplex
  letI := mC.toMonoidalCategoryStruct
  intro κ hκ P Q N
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let V := U.mapHomologicalComplex (.up ℤ)
  let F := nativeForget k₀ l X
  let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
  let qA := DerivedCategory.Q (C := ProEtale.AdicSheaf l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  let ε := U.mapDerivedCategoryFactors
  let c (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
      V.obj (nativeTensorComplex T P Q) ≅ V.obj P ⊗ V.obj Q :=
    chain Q P ≪≫ κ (V.obj Q) (V.obj P)
  let pq := nativeTensorComplex T P Q
  let qn := nativeTensorComplex T Q N
  let leftTotal := c pq N ≪≫ whiskerRightIso (c P Q) (V.obj N)
  let rightTotal := c P qn ≪≫ whiskerLeftIso (V.obj P) (c Q N)
  have hc := nativeRingedAssociatorComplex_forget k₀ l X T adj e he chain hchain b A κ hκ
    P Q N
  exact localizationModel_square q qA F V ε
    (L := nativeTensorComplex T pq N) (R := nativeTensorComplex T P qn)
    (L' := (V.obj P ⊗ V.obj Q) ⊗ V.obj N)
    (R' := V.obj P ⊗ (V.obj Q ⊗ V.obj N))
    (nativeRingedAssociatorComplex b T adj A P Q N).hom leftTotal.hom rightTotal.hom
    (mC.associator (V.obj P) (V.obj Q) (V.obj N)).hom
    (by simpa only [leftTotal, rightTotal, c, pq, qn, U, V, mC, Iso.trans_hom,
      whiskerRightIso_hom, whiskerLeftIso_hom, Category.assoc] using hc)

end AlgebraicGeometry.ProEtaleWeilSheaf
