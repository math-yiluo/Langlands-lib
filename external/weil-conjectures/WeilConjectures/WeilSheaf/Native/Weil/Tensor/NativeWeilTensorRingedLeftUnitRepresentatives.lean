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
import WeilConjectures.CategoryTheory.SixFunctors.SemigroupalUnit
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # The left-unit representative calculation

Source: Stacks 06YU, 0FPT; blueprint step 3 of
`lem-sf-native-weil-tensor-ringed-derived-square-native-data`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
section Transport

variable {B : Type*} [Category B] {A : Type*} [Category A]
  (mB : MonoidalCategory B) (mA : MonoidalCategory A)
  (F : B ⥤ A) (μ : @MonoidalCategory.tensor B _ mB ⋙ F ≅
    (F.prod F) ⋙ @MonoidalCategory.tensor A _ mA)

private def rho (X Y : B) :
    F.obj ((@MonoidalCategory.tensor B _ mB).obj (X, Y)) ≅
      (@MonoidalCategory.tensor A _ mA).obj (F.obj X, F.obj Y) :=
  μ.app (X, Y)

private theorem rho_naturality (X Y X' Y' : B) (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map ((@MonoidalCategory.tensor B _ mB).map (f, g)) ≫ (rho mB mA F μ X' Y').hom =
      (rho mB mA F μ X Y).hom ≫ (@MonoidalCategory.tensor A _ mA).map (F.map f, F.map g) :=
  μ.hom.naturality (X := (X, Y)) (Y := (X', Y')) (f, g)

private theorem associator_of_iso
    {P Q N L M V : B} (e : P ≅ L) (e' : Q ≅ M) (e'' : N ≅ V)
    (h : F.map (mB.associator P Q N).hom ≫
      (rho mB mA F μ P ((@MonoidalCategory.tensor B _ mB).obj (Q, N))).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj P, F.obj ((@MonoidalCategory.tensor B _ mB).obj (Q, N))))
        (Y := (F.obj P, (@MonoidalCategory.tensor A _ mA).obj (F.obj Q, F.obj N)))
        (𝟙 (F.obj P), (rho mB mA F μ Q N).hom) =
      (rho mB mA F μ ((@MonoidalCategory.tensor B _ mB).obj (P, Q)) N).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj ((@MonoidalCategory.tensor B _ mB).obj (P, Q)), F.obj N))
        (Y := ((@MonoidalCategory.tensor A _ mA).obj (F.obj P, F.obj Q), F.obj N))
        ((rho mB mA F μ P Q).hom, 𝟙 (F.obj N)) ≫
      (mA.associator (F.obj P) (F.obj Q) (F.obj N)).hom) :
    F.map (mB.associator L M V).hom ≫
      (rho mB mA F μ L ((@MonoidalCategory.tensor B _ mB).obj (M, V))).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj L, F.obj ((@MonoidalCategory.tensor B _ mB).obj (M, V))))
        (Y := (F.obj L, (@MonoidalCategory.tensor A _ mA).obj (F.obj M, F.obj V)))
        (𝟙 (F.obj L), (rho mB mA F μ M V).hom) =
      (rho mB mA F μ ((@MonoidalCategory.tensor B _ mB).obj (L, M)) V).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj ((@MonoidalCategory.tensor B _ mB).obj (L, M)), F.obj V))
        (Y := ((@MonoidalCategory.tensor A _ mA).obj (F.obj L, F.obj M), F.obj V))
        ((rho mB mA F μ L M).hom, 𝟙 (F.obj V)) ≫
      (mA.associator (F.obj L) (F.obj M) (F.obj V)).hom := by
  let := mB
  let := mA
  let F₁ := (leftAssocTensor B) ⋙ F
  let F₂ := (rightAssocTensor B) ⋙ F
  let G₁ := (F.prod (F.prod F)) ⋙ leftAssocTensor A
  let G₂ := (F.prod (F.prod F)) ⋙ rightAssocTensor A
  let α : F₁ ⟶ F₂ := Functor.whiskerRight (associatorNatIso B).hom F
  let β : G₁ ⟶ G₂ := Functor.whiskerLeft (F.prod (F.prod F)) (associatorNatIso A).hom
  let c₁ : F₁ ⟶ G₁ :=
    { app := fun X ↦ (rho mB mA F μ (X.1 ⊗ X.2.1) X.2.2).hom ≫
        (rho mB mA F μ X.1 X.2.1).hom ▷ F.obj X.2.2
      naturality := by
        intro X Y f
        have h₁ := rho_naturality mB mA F μ (X.1 ⊗ X.2.1) X.2.2
          (Y.1 ⊗ Y.2.1) Y.2.2 (f.1 ⊗ₘ f.2.1) f.2.2
        have h₂ := rho_naturality mB mA F μ X.1 X.2.1 Y.1 Y.2.1 f.1 f.2.1
        simp only [tensor_map] at h₁ h₂
        change F.map ((f.1 ⊗ₘ f.2.1) ⊗ₘ f.2.2) ≫ _ = _
        rw [reassoc_of% h₁]
        change (rho mB mA F μ (X.1 ⊗ X.2.1) X.2.2).hom ≫
            (F.map (f.1 ⊗ₘ f.2.1) ⊗ₘ F.map f.2.2) ≫
              (rho mB mA F μ Y.1 Y.2.1).hom ▷ F.obj Y.2.2 = _
        simp only [← tensorHom_id, Category.assoc,
          tensorHom_comp_tensorHom,
          Category.comp_id]
        erw [h₂]
        simp only [G₁, Functor.comp_map, Functor.prod_map,
          leftAssocTensor_map,
          tensorHom_comp_tensorHom,
          Category.id_comp] }
  let c₂ : F₂ ⟶ G₂ :=
    { app := fun X ↦ (rho mB mA F μ X.1 (X.2.1 ⊗ X.2.2)).hom ≫
        F.obj X.1 ◁ (rho mB mA F μ X.2.1 X.2.2).hom
      naturality := by
        intro X Y f
        have h₁ := rho_naturality mB mA F μ X.1 (X.2.1 ⊗ X.2.2)
          Y.1 (Y.2.1 ⊗ Y.2.2) f.1 (f.2.1 ⊗ₘ f.2.2)
        have h₂ := rho_naturality mB mA F μ X.2.1 X.2.2 Y.2.1 Y.2.2 f.2.1 f.2.2
        simp only [tensor_map] at h₁ h₂
        change F.map (f.1 ⊗ₘ (f.2.1 ⊗ₘ f.2.2)) ≫ _ = _
        rw [reassoc_of% h₁]
        change (rho mB mA F μ X.1 (X.2.1 ⊗ X.2.2)).hom ≫
            (F.map f.1 ⊗ₘ F.map (f.2.1 ⊗ₘ f.2.2)) ≫
              F.obj Y.1 ◁ (rho mB mA F μ Y.2.1 Y.2.2).hom = _
        simp only [← id_tensorHom, Category.assoc,
          tensorHom_comp_tensorHom,
          Category.comp_id]
        erw [h₂]
        simp only [G₂, Functor.comp_map, Functor.prod_map,
          rightAssocTensor_map,
          tensorHom_comp_tensorHom,
          Category.id_comp] }
  let z : (P, Q, N) ≅ (L, M, V) := e.prod (e'.prod e'')
  have hz : IsIso (F₁.map z.hom) := inferInstance
  apply (cancel_epi (F₁.map z.hom)).mp
  have hh : (α ≫ c₂).app (P, Q, N) = (c₁ ≫ β).app (P, Q, N) := by
    simpa only [α, β, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
      F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
      tensor_map,
      id_tensorHom, tensorHom_id, Category.assoc] using h
  have hh' := congrArg (fun f ↦ f ≫ G₂.map z.hom) hh
  rw [← (α ≫ c₂).naturality, ← (c₁ ≫ β).naturality] at hh'
  simpa only [α, β, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
      F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
      tensor_map,
    id_tensorHom, tensorHom_id, Category.assoc] using hh'

end Transport

namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- The unchanged signature keeps d, which the shorter categorical proof does not use.
set_option linter.unusedVariables false in
/-- The degree-zero calculation for the left unit of the native tensor comparison.

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 0FPT; the left-unit
part of step 2 of lem-sf-native-weil-tensor-ringed-unit-symmetry-representatives.
(blueprint: lem-sf-native-weil-tensor-ringed-left-unit-representatives).

Proof: use the unit comparison of d.coherence, the native and ordinary derived
equivalences, and the degree-zero coefficient identifications to define epsilon.
Represent a native K-flat input by a flat-term K-flat complex using b.native.
The unit is represented by the coefficient ring in degree zero. Expand hforget
for this unit and the chosen input, and use cB.leftUnitor_model and the left-unit
law of the canonical ordinary localization tensorator. The normalized formula
hcanonical fixes ordinaryModel on two K-flat inputs. Its naturality and a
K-flat replacement of the second input extend that formula to the one-K-flat
pairs occurring here. After cancellation of the model isomorphisms, the desired
identity is the localization of the underived left-unit square. Test it on total
summands: all summands with unit degree different from zero vanish; on the
(0,n) summand the sign is one. The single-complex comparison and
d.unit_normalization identify the unit arrow, and b.underived.coherence.left_unit
is the remaining equality. The balanced tensor and coproduct universal properties
give equality of chain maps. Naturality under the replacement returns the equation
to the original input. The constructed epsilon is fixed independently of that
input. No right-unit or braiding equation is asserted. -/
theorem native_weil_tensor_ringed_left_unit_representatives
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
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
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
    let m := nativeWeilRingedMonoidal b SB
    let F := nativeForget k₀ l X
    ∃ ε : F.obj m.tensorUnit ≅ S.monoidal.tensorUnit,
      ∀ (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
        NativeTensorKFlat k₀ l X T P →
        t.hom.app (m.tensorUnit, DerivedCategory.Q.obj P) ≫
            S.tensor.map
              (X := (F.obj m.tensorUnit, F.obj (DerivedCategory.Q.obj P)))
              (Y := (S.monoidal.tensorUnit, F.obj (DerivedCategory.Q.obj P)))
              (ε.hom, 𝟙 _) ≫ (S.monoidal.leftUnitor (F.obj (DerivedCategory.Q.obj P))).hom =
          F.map (m.leftUnitor (DerivedCategory.Q.obj P)).hom := by
  classical
  set_option synthInstance.maxSize 4096 in
  · clear _hnaturality d cA βA TA SA
    rcases S with ⟨mS, adjS, evS⟩
    change mS = _ at hmonoidal
    subst mS
    let := nativeWeilRingedMonoidal b SB
    let F := nativeForget k₀ l X
    let K : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
      NativeTensorKFlat k₀ l X T
    let q := K.ι ⋙ DerivedCategory.Q
    let W := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage K.ι
    let : q.IsLocalization W := A.localization
    let : q.EssSurj := Localization.essSurj q W
    have ha := nativeRingedAssociatorRepresentatives_normalized k₀ l X T adj e he
      chain hchain b A SB TB βB cB ordinaryModel hcanonical t hforget
    let v : F.obj (𝟙_ (DerivedCategory (ProEtaleWeilSheaf k₀ l X))) ≅
        𝟙_ (DerivedCategory (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :=
      F.mapIso (nativeWeilRingedUnit b SB TB βB cB) ≪≫
        (Functor.mapDerivedCategorySingleFunctor
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
            (adicConstant k₀ l X) ≪≫ Iso.refl _
    obtain ⟨ε, hε⟩ := exists_leftUnit_of_associative_tensor F t v (by
      intro Y Z N
      simpa only [rho, Iso.app_hom, tensor_obj, tensor_map, id_tensorHom,
        tensorHom_id] using
        (associator_of_iso (nativeWeilRingedMonoidal b SB) _ F t
          (q.objObjPreimageIso Y) (q.objObjPreimageIso Z) (q.objObjPreimageIso N) (by
            simpa only [rho, Iso.app_hom, tensor_obj, tensor_map, id_tensorHom,
              tensorHom_id, F, q, Functor.comp_obj, Functor.prod_obj,
              ObjectProperty.ι_obj] using
              (ha (q.objPreimage Y).obj (q.objPreimage Z).obj (q.objPreimage N).obj
                (q.objPreimage Y).property (q.objPreimage Z).property
                  (q.objPreimage N).property))))
    refine ⟨ε, fun P _hP ↦ ?_⟩
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      tensorHom_id] using hε (DerivedCategory.Q.obj P)

end AlgebraicGeometry.ProEtaleWeilSheaf
