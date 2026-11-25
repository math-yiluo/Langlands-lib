/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedStructure
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorDescent
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquare
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModelNaturality

/-! # Transport of already descended ringed tensor comparisons to native modules

Source: Stacks 06YS, 06YU and 0FPT; change of additive ringed presentation.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Transfer a supplied, normalized ringed tensor comparison across the two underived
module equivalences. This assertion performs no construction of an action site and
no descent of a chain comparison to a derived comparison: that comparison is an input.
The coefficient-unit normalization of the final theorem is a separate groupoid calculation.

Source: native tensor geometry, transport clauses of steps 1--3; Stacks 06YS,
06YU and 0FPT; the normalized tensor comparison of ringed_forget_tensor_descent.
(blueprint: lem-sf-native-weil-tensor-ringed-transport).

Proof: lift the two additive equivalences termwise and localize. Their quasi-inverse
functors and unit and counit isomorphisms remain inverse after localization, so these
are equivalences of the actual derived categories of complexes of fixed pairs.
The already constructed nativeWeilRingedMonoidal and nativeWeilRingedSymmetric
are fixed; no native monoidal structure or symmetry is chosen here. Transport the underived
ringed tensor through the same equivalence. Uniqueness of left adjoints to the
native sheaf Hom identifies it with the native underived tensor; the Hom-square
in b fixes this identification by evaluation. Apply the total-complex comparison
in each variable. Equivalences preserve coproducts and acyclicity, so K-flatness
and K-flat localization transport; for ordinary forgetting use the exact orbit-sum
left adjoint, whose identity summand makes an ordinary acyclic tensor test a retract
of a forgotten native test. Thus every native K-flat complex has ordinary K-flat
image, without requiring flat terms. The one-K-flat ringed model gives the native
model and its naturality; the supplied native chain comparison gives chain_summand directly.
For the ordinary internal Hom, the underived equivalence preserves the products
in its Hom complexes, and it and its inverse preserve K-injectives because their
left adjoints are exact. Thus ordinaryHom and the specified ordinary representative
factors identify the two ordinary derived Hom functors, naturally on every resolution.
Identify the transported ordinary tensor with S.tensor using the two tensor--Hom
adjunctions and hS's componentwise uncurrying. Their counit equations identify the
ordinary model, and the signed-swap equations in hS identify betaA with beta under
this tensor comparison; hmonoidal fixes the associator and unitors. Conjugate
d.derived by the two equivalences, the localized square of b, and this ordinary
tensor identification to get t. Its representative equation is exactly the
model_forget equation with both exact-forgetting factors. Transport the four
coherence equations of d.coherence to get c. These constructions give the seven
fields of NativeWeilTensorPresentation; no native derived closed adjunction is
used. All operations are on unbounded complexes, and apply to zero and empty sites. -/
theorem native_weil_tensor_ringed_transport
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
    ∃ t : @MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB) ⋙
        nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    ∃ _P : NativeWeilTensorPresentation k₀ l X M S (nativeWeilRingedMonoidal b SB) t,
      Nonempty (RingedForgetTensorTransposition.TensorCoherence
        (nativeWeilRingedMonoidal b SB) S.monoidal
        (nativeWeilRingedSymmetric b SB βB) β (nativeForget k₀ l X) t) := by
  obtain ⟨A⟩ := native_weil_tensor_ringed_complexes b T adj
  obtain ⟨t, ordinaryModel, hordinary, _hnaturality, hforget, hcoherence⟩ :=
    native_weil_tensor_ringed_derived_square k₀ l X T adj e he chain hchain b A M S β
      hmonoidal hS SB TB βB cB SA TA βA cA d
  let D : NativeWeilTensorComplexData k₀ l X M S (nativeWeilRingedMonoidal b SB) :=
    { tensor := T
      tensor_additive := inferInstance
      tensor_obj_additive := inferInstance
      total_exists := inferInstance
      adjunction := adj
      underived := e
      model := nativeWeilRingedTensorModel b T adj A SB TB βB cB
      ordinaryModel := ordinaryModel
      chain := chain }
  refine ⟨t, { toNativeWeilTensorComplexData := D, axioms := ?_ }, hcoherence⟩
  exact
    { underived_uncurry := he
      localization := A.localization
      preserves_flat := native_weil_tensor_forget_kflat k₀ l X T chain
      model_naturality := nativeWeilRingedTensorModel_naturality b T adj A SB TB βB cB
      ordinaryNormalization := hordinary
      chain_summand := hchain
      model_forget := hforget }

end AlgebraicGeometry.ProEtaleWeilSheaf
