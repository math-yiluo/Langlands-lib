/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorForgetKFlat
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorDescent
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorNormalized

/-! # Coherence component of the native ringed derived square

Source: Stacks 06YU, 0FPT; blueprint step 3 of
`lem-sf-native-weil-tensor-ringed-derived-square-native-data`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- Applying the normalized case unfolds the concrete monoidal and localization structures.
/-- Associativity of the native comparison on three K-flat representatives.

Source: Stacks 06YU, 0FPT; native tensor transport, associator part of step 3.
(blueprint: lem-sf-native-weil-tensor-ringed-associator-representatives).

Proof: first replace each native K-flat complex by a flat-term K-flat model via
b.native. The total comparisons A.chain and chain identify the two total tensor
calculations, with A.summand and hchain fixing every summand. On the ordinary
side, the canonical clause of hS fixes its tensor model to the localization
lax tensorator followed by the signed balanced total comparison.
The supplied hcanonical fixes ordinaryModel itself on pairs of K-flat
inputs.
Naturality and a K-flat replacement extend the equations to other inputs.
Apply the representative equation hforget to both inner and both outer pairs.
The equations cB.associator_model and the canonical localization associativity
then reduce the desired square to the underived square b.underived.coherence
across b.square. The normalized adjunction equations he and A.uncurry and
b.hom_square identify its comparison maps. On a triple summand the signed
interchanges have the same total sign, since pq+(p+q)r=qr+p(q+r).
The coproduct and balanced tensor universal properties prove equality of chain
maps. Localize this equality and cancel the four model isomorphisms.
Finally naturality under the chosen flat-term replacements gives the displayed
equation for the original K-flat P,Q,N. This statement concerns only K-flat
representatives and asserts neither units nor symmetry nor arbitrary objects. -/
theorem native_weil_tensor_ringed_associator_representatives
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
    (hcanonical : ∃ κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅ Q ⊗ P,
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
        Mod.tensorπ (Q.X q) (P.X p) ≫
            (HomologicalComplex.ιMapBifunctor P Q
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
          (p * q).negOnePow •
            (Mod.tensorObjπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)) ∧
      ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
        (_hQ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q),
        HEq (ordinaryModel P Q hP).hom
          (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
            DerivedCategory.Q.map (κ P Q).inv))
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
              (.up ℤ)))
    (t : @MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB) ⋙
        nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    (hforget : (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
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
          (native_weil_tensor_forget_kflat k₀ l X T chain P hP)).hom)) :
    ∀ (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
      NativeTensorKFlat k₀ l X T P → NativeTensorKFlat k₀ l X T Q →
      NativeTensorKFlat k₀ l X T N →
      let m := nativeWeilRingedMonoidal b SB
      let F := nativeForget k₀ l X
      F.map (m.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom ≫
          t.hom.app (DerivedCategory.Q.obj P,
            m.tensorObj (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj N)) ≫
          S.tensor.map
            (X := (F.obj (DerivedCategory.Q.obj P),
              F.obj (m.tensorObj (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj N))))
            (Y := (F.obj (DerivedCategory.Q.obj P),
              S.tensor.obj (F.obj (DerivedCategory.Q.obj Q), F.obj (DerivedCategory.Q.obj N))))
            (𝟙 _, t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) =
        t.hom.app (m.tensorObj (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q),
            DerivedCategory.Q.obj N) ≫
          S.tensor.map
            (X := (F.obj (m.tensorObj (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)),
              F.obj (DerivedCategory.Q.obj N)))
            (Y := (S.tensor.obj (F.obj (DerivedCategory.Q.obj P), F.obj (DerivedCategory.Q.obj Q)),
              F.obj (DerivedCategory.Q.obj N)))
            (t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q), 𝟙 _) ≫
          (S.monoidal.associator (F.obj (DerivedCategory.Q.obj P))
            (F.obj (DerivedCategory.Q.obj Q)) (F.obj (DerivedCategory.Q.obj N))).hom := by
  -- The options act on the proof only, so the published statement elaborates as before.
  set_option synthInstance.maxSize 4096 in
  · have _usedH := hS
    have _usedD := d
    clear _usedH _usedD _hnaturality hS β d cA βA TA SA
    rcases S with ⟨mS, adjS, evS⟩
    change mS = _ at hmonoidal
    subst mS
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj,
      MonoidalCategory.tensor_map, id_tensorHom, tensorHom_id] using
      nativeRingedAssociatorRepresentatives_normalized k₀ l X T adj e he chain hchain
        b A SB TB βB cB ordinaryModel hcanonical t hforget

end AlgebraicGeometry.ProEtaleWeilSheaf
