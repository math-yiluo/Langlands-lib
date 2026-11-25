/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorForgetKFlat
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorDescent
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareNativeComparison
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareNativeCoherence

/-! # Native comparison part of the native ringed derived square

Source: Stacks 06YU, 0FPT; blueprint steps 2--3 of
`lem-sf-native-weil-tensor-ringed-derived-square`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilRingedMonoidal
  DerivedCategory DerivedCategory.Q instCategoryDerivedCategory
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilRingedTensorModel
  Functor.mapDerivedCategoryFactors HomologicalComplex.mapBifunctorMap
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeOrdinaryKFlat
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeTensorKFlat
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Given the ordinary representative data, the native comparison, its representative
square, and its coherence are the remaining native part of the derived-square argument.

Source: Stacks 06YU, 0FPT; blueprint:
`lem-sf-native-weil-tensor-ringed-derived-square-native-data`.

Proof: `native_weil_tensor_ringed_derived_square_comparison` (blueprint:
lem-sf-native-weil-tensor-ringed-derived-square-comparison) gives a comparison `t`
with the full representative square, by descent along the product of the derived
localization and the native K-flat localization `A.localization`. The coherence
component `native_weil_tensor_ringed_derived_square_native_coherence` (blueprint:
lem-sf-native-weil-tensor-ringed-derived-square-native-coherence), applied to `t` and
its square, gives `TensorCoherence`. The transport of the associator, unit and
symmetry equations is the content of that component.
-/
theorem native_weil_tensor_ringed_derived_square_native_data
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
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.K b.Q)]
    (A : NativeWeilRingedTensorComplexes b T adj)
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β)
    (SB : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)
    (SA : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.K b.Q))
    (TA : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.K b.Q SA)
    (βA : @SymmetricCategory _ _ SA.monoidal)
    (cA : RingedDerivedTensorCoherence b.K b.Q SA TA βA)
    (d : RingedForgetTensorTransposition.TensorComparison
      b.J b.R b.K b.Q b.forget b.underived SB TB βB cB SA TA βA cA)
    (ordinaryModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (_ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P),
          S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj
              (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q))
    (_hordinary : NativeAdjunctionNormalization
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (fun P ↦ Mod.ihomAdjunction P) M.ordinaryHom M.ordinaryRepresentatives S
        (NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ordinaryModel)
    (_hnaturality : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
          (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
          (hP' : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P')
          (f : P ⟶ P') (g : Q ⟶ Q'),
        S.tensor.map
            (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
            (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
            (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
            (ordinaryModel P' Q' hP').hom =
          (ordinaryModel P Q hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ))) :
    ∃ t : @MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB) ⋙
        nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P),
    (nativeForget k₀ l X).map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app
            (CochainComplex.mapBifunctor P Q T)) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        S.tensor.map
          (X := ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj Q),
            (nativeForget k₀ l X).obj (DerivedCategory.Q.obj P)))
          (Y := (DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q),
            DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)))
          (Prod.mkHom
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app Q)
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app P)) ≫
        (ordinaryModel
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (native_weil_tensor_forget_kflat k₀ l X T chain P hP)).hom) ∧
      Nonempty (RingedForgetTensorTransposition.TensorCoherence
        (nativeWeilRingedMonoidal b SB) S.monoidal
        (nativeWeilRingedSymmetric b SB βB) β (nativeForget k₀ l X) t) := by
  obtain ⟨t, ht, -⟩ := native_weil_tensor_ringed_derived_square_comparison k₀ l X T adj e
    chain hchain b A M S SB TB βB cB ordinaryModel _hnaturality
  exact ⟨t, ht, native_weil_tensor_ringed_derived_square_native_coherence k₀ l X T adj e he
    chain hchain b A M S β hmonoidal hS SB TB βB cB SA TA βA cA d ordinaryModel _hordinary
    _hnaturality t ht⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
