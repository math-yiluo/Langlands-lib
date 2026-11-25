/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorChain
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnderivedTensor
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTransport

/-! # Action-site geometry of the native derived tensor

Source: Stacks 06YS and 0FPT; native ringed tensor model, geometric steps.
-/

@[expose] public section
set_option autoImplicit false
universe u a v b w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
private theorem unitNormalization {C : Type a} [Category.{v} C]
    {D : Type b} [Category.{w} D] (F : C ⥤ D)
    {I U : C} {J V : D} (c : F.obj I ≅ J) (δ : I ≅ U) (ζ : F.obj U ≅ V) :
    ∃ ε : J ≅ V, c = F.mapIso δ ≪≫ ζ ≪≫ ε.symm := by
  refine ⟨c.symm ≪≫ F.mapIso δ ≪≫ ζ, ?_⟩
  apply Iso.ext
  simp

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q

namespace AlgebraicGeometry.ProEtaleWeilSheaf
private theorem geometry_from_comparison
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
      b.J b.R b.K b.Q b.forget b.underived SB TB βB cB SA TA βA cA) :
    ∃ m : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X)),
    ∃ γ : @SymmetricCategory _ _ m,
    ∃ δ : m.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X),
    ∃ ε : S.monoidal.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    ∃ t : @MonoidalCategory.tensor _ _ m ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    ∃ _P : NativeWeilTensorPresentation k₀ l X M S m t,
    ∃ c : RingedForgetTensorTransposition.TensorCoherence m S.monoidal
      γ β (nativeForget k₀ l X) t,
      c.unit = (nativeForget k₀ l X).mapIso δ ≪≫
        ((Functor.mapDerivedCategorySingleFunctor
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
            (adicConstant k₀ l X)) ≪≫ ε.symm := by
  let m := nativeWeilRingedMonoidal b SB
  let γ := nativeWeilRingedSymmetric b SB βB
  let δ := nativeWeilRingedUnit b SB TB βB cB
  obtain ⟨t, P, ⟨c⟩⟩ := native_weil_tensor_ringed_transport k₀ l X
    T adj e he chain hchain b M S β hmonoidal hS SB TB βB cB SA TA βA cA d
  obtain ⟨ε, hε⟩ := unitNormalization (nativeForget k₀ l X) c.unit δ
    ((Functor.mapDerivedCategorySingleFunctor
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
        (adicConstant k₀ l X))
  exact ⟨m, γ, δ, ε, t, P, c, hε⟩

private theorem geometry_from_bridge
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
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β) :
    ∃ m : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X)),
    ∃ γ : @SymmetricCategory _ _ m,
    ∃ δ : m.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X),
    ∃ ε : S.monoidal.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    ∃ t : @MonoidalCategory.tensor _ _ m ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    ∃ _P : NativeWeilTensorPresentation k₀ l X M S m t,
    ∃ c : RingedForgetTensorTransposition.TensorCoherence m S.monoidal
      γ β (nativeForget k₀ l X) t,
      c.unit = (nativeForget k₀ l X).mapIso δ ≪≫
        ((Functor.mapDerivedCategorySingleFunctor
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
            (adicConstant k₀ l X)) ≪≫ ε.symm := by
  obtain ⟨SB, TB, βB, ⟨cB⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u + 1, u + 1, u + 2} b.J b.R
  obtain ⟨SA, TA, βA, ⟨cA⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u + 1, u + 1, u + 2} b.K b.Q
  obtain ⟨d, _⟩ := RingedForgetTensorTransposition.ringed_forget_tensor_descent
    b.J b.R b.K b.Q b.forget b.underived SB TB βB cB SA TA βA cA b.preserves_flat_models
  exact geometry_from_comparison k₀ l X T adj e he chain hchain b M S β hmonoidal hS
    SB TB βB cB SA TA βA cA d

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The action-site construction supplies a symmetric monoidal native tensor,
its total-complex models, and coherent ordinary forgetting. No native derived
closed adjunction or derived Hom comparison is asserted.

Source: Stacks 06YS, 06YU and 0FPT; native ringed tensor model, steps 1 and 3.
(blueprint: lem-sf-native-weil-tensor-geometry).

Proof: take the Frobenius action-site realization and its resolution assertions
from frobenius_action_resolutions. The restriction equivalence on module sheaves
intertwines Frobenius pullback: on the generating locally finite-subextension
functions both operations are the same precomposition. Lift the equivalence
to fixed pairs and then termwise to their complex localizations. Transport
the ringed derived symmetric monoidal tensor and its coefficient unit through
this equivalence. Keep its native underived tensor bifunctor, the ordinary
module tensor--Hom adjunction, and their evaluation-normalized forgetting
comparison. The transported total tensor has exactly the stated acyclic-test
K-flats; the resolution theorem and the universal property of localization
give the restricted localization field. Its one-K-flat model and naturality
are the transported ringed tensor models. For preservation of K-flatness,
induce an ordinary acyclic complex to the direct sum of its Frobenius translates.
This is an acyclic native test complex, and the original ordinary tensor is a
retract of the forgotten tensor with this test. Its acyclicity follows. Extract
the ordinary model and its adjunction normalization from hS. Uniqueness
of left adjoints identifies the transported ordinary model with this specified
model, and its signed swap with beta. The fixed monoidal equality hmonoidal
identifies the ordinary associator and unitors. Apply ringed_forget_tensor_descent
to the action-site forgetting functor and transport its comparison. Its summand
formula gives chain_summand, and its representative formula gives model_forget.
Its four coherence equations give c. The coefficient-unit isomorphisms give
delta and epsilon. Exact forgetting of single complexes gives the displayed
unit equality, including precisely the two single-functor factors. All
constructions use unbounded complexes; the same universal properties handle
zero objects and the empty site. Derived tensor--Hom currying is left to the
separate representative-currying step. -/
theorem native_weil_tensor_geometry
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β) :
    ∃ m : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X)),
    ∃ γ : @SymmetricCategory _ _ m,
    ∃ δ : m.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X),
    ∃ ε : S.monoidal.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    ∃ t : @MonoidalCategory.tensor _ _ m ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    ∃ _P : NativeWeilTensorPresentation k₀ l X M S m t,
    ∃ c : RingedForgetTensorTransposition.TensorCoherence m S.monoidal
      γ β (nativeForget k₀ l X) t,
      c.unit = (nativeForget k₀ l X).mapIso δ ≪≫
        ((Functor.mapDerivedCategorySingleFunctor
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
            (adicConstant k₀ l X)) ≪≫ ε.symm := by
  obtain ⟨T, hT, hTobj, adj, e, he⟩ := native_weil_underived_tensor k₀ l X
  let := hT
  let := hTobj
  obtain ⟨chain, hchain⟩ := native_weil_tensor_chain k₀ l X T e
  obtain ⟨b⟩ := native_weil_tensor_ringed_bridge k₀ l X
  let : HasDerivedCategory.{u + 2}
      (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2}
      (RingedTensorModules.{u + 1, u + 1, u + 1} b.K b.Q) :=
    HasDerivedCategory.standard _
  exact geometry_from_bridge k₀ l X T adj e he chain hchain b M S β hmonoidal hS

end AlgebraicGeometry.ProEtaleWeilSheaf
