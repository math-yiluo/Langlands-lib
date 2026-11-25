/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomTensorChainSquare
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomTensorAssociatorModel

/-! # Composition of the intrinsic finite scalar tensorators
Source: blueprint lemma-change-coefficients-internal-hom--1, successive quotient paragraph
(blueprint: lem-coef-finite-hom-intrinsic-tensor-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u a₁ b₁ v₁ v₂ w₁ w₂
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

open CategoryTheory.Functor CategoryTheory.Limits Opposite

attribute [local irreducible] constantSheaf
attribute [local irreducible] CoefficientClosedStructure.tensor
  SheafOfModules.monoidalCategory coefficientTotalTensor coefficientTensorGenerator
  coefficientFiniteQuotientExistence coefficientFiniteQuotientDerivedExistence
  coefficientFiniteQuotientExtension coefficientFiniteQuotientDerived
  DerivedCategory _root_.instCategoryDerivedCategory DerivedCategory.Q DerivedCategory.Qh
  HasDerivedCategory.standard SheafOfModules.instPreadditive

attribute [local irreducible] finiteHomTensorRepresentativeComparison
  coefficientLocalizedCounitModel
  finiteHomTensorComplexAssociator scalarUnitSection

private theorem map_three_eq_three
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y Z N P Q : A} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ N}
    {a : X ⟶ P} {b : P ⟶ Q} {c : Q ⟶ N} (w : f ≫ g ≫ h = a ≫ b ≫ c) :
    F.map f ≫ F.map g ≫ F.map h = F.map a ≫ F.map b ≫ F.map c := by
  simpa only [Functor.map_comp] using congrArg F.map w

attribute [local instance 2000] finiteHomTensorSiteSmall

section Representatives
attribute [local instance 2000] HasDerivedCategory.standard
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private abbrev ordinaryUnitSection {n m : ℕ} (h : m ≤ n)
    (M : normalizedDVRModules.{u, u} l E X n) (V : X.ProEtᵒᵖ) (x : M.val.obj V) :
    ((coefficientFiniteQuotientExtension.{u, u} l E X h).obj M).val.obj V :=
  scalarUnitSection (normalizedDVRQuotient.{u, u} l E X h)
    ((calculus l E X).quotientCalculus.ordinaryAdjunction h) M V x

attribute [local semireducible] scalarUnitSection

private theorem ordinaryUnitSection_eq {n m : ℕ} (h : m ≤ n)
    (M : normalizedDVRModules.{u, u} l E X n) (V : X.ProEtᵒᵖ) (x : M.val.obj V) :
    ordinaryUnitSection l E X h M V x = coefficientFiniteQuotientUnitSection.{u, u} l E X h M V x :=
  (calculus l E X).quotientCalculus.ordinary_unit h M V x

private def tensorChain {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) Q) :=
  ((calculus l E X).quotientCalculus.tensor_model h P Q hp hq).choose

private theorem tensorChain_generators {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) Q)
    (p q i : ℤ) (hi : p + q = i) (V : X.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((tensorChain l E X h P Q hp hq).hom.f i).val.app V)
        (ordinaryUnitSection l E X h _ V
          (coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X)
            (integralCoefficientCommRingSheaf.{u, u} l E X n) P Q p q i hi V x y)) =
      coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X m)
        ((finiteHomTensorExtensionComplex l E X h).obj P)
        ((finiteHomTensorExtensionComplex l E X h).obj Q) p q i hi V
        (ordinaryUnitSection l E X h _ V x) (ordinaryUnitSection l E X h _ V y) := by
  simp only [ordinaryUnitSection_eq]
  exact ((calculus l E X).quotientCalculus.tensor_model h P Q hp hq).choose_spec.1
    p q i hi V x y

private theorem chainAssoc_unit {n m r : ℕ} (h : m ≤ n) (k : r ≤ m)
    (P : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ)
    (i : ℤ) (V : X.ProEtᵒᵖ) (x : (P.X i).val.obj V) :
    (((finiteHomTensorChainAssoc l E X h k).hom.app P).f i).val.app V
        (ordinaryUnitSection l E X k _ V (ordinaryUnitSection l E X h _ V x)) =
      ordinaryUnitSection l E X (k.trans h) _ V x := by
  exact complexAssoc_unit_section (normalizedDVRQuotient.{u, u} l E X h)
    (normalizedDVRQuotient.{u, u} l E X k)
    (normalizedDVRQuotient.{u, u} l E X (k.trans h))
    ((integralCoefficientSheafSystem.{u, u} l E X).map_comp
      (homOfLE h).op (homOfLE k).op).symm
    ((calculus l E X).quotientCalculus.ordinaryAdjunction h)
    ((calculus l E X).quotientCalculus.ordinaryAdjunction k)
    ((calculus l E X).quotientCalculus.ordinaryAdjunction (k.trans h)) P i V x

private theorem chain_tensor_coherence {n m r : ℕ} (h : m ≤ n) (k : r ≤ m)
    (P Q : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) Q) :
    (finiteHomTensorExtensionComplex l E X k).map (tensorChain l E X h P Q hp hq).hom ≫
      (tensorChain l E X k _ _
        ((calculus l E X).quotientCalculus.preservesKFlat h P hp)
        ((calculus l E X).quotientCalculus.preservesKFlat h Q hq)).hom ≫
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X r)).map
          (Prod.mkHom ((finiteHomTensorChainAssoc l E X h k).hom.app P)
            ((finiteHomTensorChainAssoc l E X h k).hom.app Q)) =
    (finiteHomTensorChainAssoc l E X h k).hom.app
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X n)).obj (P, Q)) ≫
      (tensorChain l E X (k.trans h) P Q hp hq).hom := by
  let _ := coefficientFiniteQuotientExtensionAdditive.{u, u} l E X h
  let _ := coefficientFiniteQuotientExtensionAdditive.{u, u} l E X k
  let _ := coefficientFiniteQuotientExtensionAdditive.{u, u} l E X (k.trans h)
  apply finiteHomTensor_chainSquare.{u, u + 1, u}
    (hFadd := coefficientFiniteQuotientExtensionAdditive.{u, u} l E X h)
    (hGadd := coefficientFiniteQuotientExtensionAdditive.{u, u} l E X k)
    (hHadd := coefficientFiniteQuotientExtensionAdditive.{u, u} l E X (k.trans h))
    (A := integralCoefficientCommRingSheaf.{u, u} l E X n)
    (B := integralCoefficientCommRingSheaf.{u, u} l E X m)
    (T := integralCoefficientCommRingSheaf.{u, u} l E X r)
    (normalizedDVRQuotient.{u, u} l E X h) (normalizedDVRQuotient.{u, u} l E X k)
    (normalizedDVRQuotient.{u, u} l E X (k.trans h))
    ((calculus l E X).quotientCalculus.ordinaryAdjunction h)
    ((calculus l E X).quotientCalculus.ordinaryAdjunction k)
    ((calculus l E X).quotientCalculus.ordinaryAdjunction (k.trans h))
    (finiteHomTensorChainAssoc l E X h k).hom (chainAssoc_unit l E X h k) P Q
    (tensorChain l E X h P Q hp hq)
    (tensorChain l E X k _ _
      ((calculus l E X).quotientCalculus.preservesKFlat h P hp)
      ((calculus l E X).quotientCalculus.preservesKFlat h Q hq))
    (tensorChain l E X (k.trans h) P Q hp hq)
  · exact tensorChain_generators l E X h P Q hp hq
  · exact tensorChain_generators l E X k _ _ _ _
  · exact tensorChain_generators l E X (k.trans h) P Q hp hq

private theorem tensorChain_model {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) Q) :
    (coefficientFiniteQuotientDerived.{u, u} l E X h).map
        (coefficientFiniteTensorModelIso.{u, u} l E X
          (calculus l E X).toCoefficientDerivedSystemTensors
          n P Q hp hq).hom ≫
      ((calculus l E X).quotientCalculus.tensor h).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      ((calculus l E X).finiteClosed m).tensor.map
        (Prod.mkHom ((finiteHomTensorComparison l E X h).app P)
          ((finiteHomTensorComparison l E X h).app Q)) =
    (finiteHomTensorComparison l E X h).app _ ≫
      DerivedCategory.Q.map (tensorChain l E X h P Q hp hq).hom ≫
      (coefficientFiniteTensorModelIso.{u, u} l E X
          (calculus l E X).toCoefficientDerivedSystemTensors
        m _ _ ((calculus l E X).quotientCalculus.preservesKFlat h P hp)
        ((calculus l E X).quotientCalculus.preservesKFlat h Q hq)).hom := by
  rw [comparison_model l E X h P hp, comparison_model l E X h Q hq,
    comparison_model l E X h _
      (coefficientTotalTensor_isKFlat.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X n) P Q hp hq)]
  exact ((calculus l E X).quotientCalculus.tensor_model h P Q hp hq).choose_spec.2

private theorem representative_tensor_coherence {n m r : ℕ} (h : m ≤ n) (k : r ≤ m)
    (P Q : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) Q) :
    (coefficientFiniteQuotientDerived.{u, u} l E X k).map
        (((calculus l E X).quotientCalculus.tensor h).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      ((calculus l E X).quotientCalculus.tensor k).hom.app
        ((coefficientFiniteQuotientDerived.{u, u} l E X h).obj (DerivedCategory.Q.obj P),
          (coefficientFiniteQuotientDerived.{u, u} l E X h).obj (DerivedCategory.Q.obj Q)) ≫
      ((calculus l E X).finiteClosed r).tensor.map (Prod.mkHom
        ((finiteHomIntrinsicAssoc l E X h k).hom.app (DerivedCategory.Q.obj P))
        ((finiteHomIntrinsicAssoc l E X h k).hom.app (DerivedCategory.Q.obj Q))) =
    (finiteHomIntrinsicAssoc l E X h k).hom.app
      (((calculus l E X).finiteClosed n).tensor.obj (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) ≫
      ((calculus l E X).quotientCalculus.tensor (k.trans h)).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
  let Fa := finiteHomTensorExtensionComplex l E X h
  let Fb := finiteHomTensorExtensionComplex l E X k
  let Fc := finiteHomTensorExtensionComplex l E X (k.trans h)
  let F := coefficientFiniteQuotientDerived.{u, u} l E X h
  let G := coefficientFiniteQuotientDerived.{u, u} l E X k
  let H := coefficientFiniteQuotientDerived.{u, u} l E X (k.trans h)
  let U := ((calculus l E X).finiteClosed m).tensor
  let V := ((calculus l E X).finiteClosed r).tensor
  let cc := finiteHomIntrinsicAssoc l E X h k
  let rR := (coefficientFiniteTensorModelIso.{u, u} l E X
    (calculus l E X).toCoefficientDerivedSystemTensors n P Q hp hq).hom
  let _ : IsIso (G.map (F.map rR)) := Iso.isIso_hom
    ((F ⋙ G).mapIso (coefficientFiniteTensorModelIso.{u, u} l E X
      (calculus l E X).toCoefficientDerivedSystemTensors n P Q hp hq))
  let rS := (coefficientFiniteTensorModelIso.{u, u} l E X
    (calculus l E X).toCoefficientDerivedSystemTensors m (Fa.obj P) (Fa.obj Q)
    ((calculus l E X).quotientCalculus.preservesKFlat h P hp)
    ((calculus l E X).quotientCalculus.preservesKFlat h Q hq)).hom
  let rT := (coefficientFiniteTensorModelIso.{u, u} l E X
    (calculus l E X).toCoefficientDerivedSystemTensors r (Fb.obj (Fa.obj P)) (Fb.obj (Fa.obj Q))
    ((calculus l E X).quotientCalculus.preservesKFlat k _
      ((calculus l E X).quotientCalculus.preservesKFlat h P hp))
    ((calculus l E X).quotientCalculus.preservesKFlat k _
      ((calculus l E X).quotientCalculus.preservesKFlat h Q hq))).hom
  let rC := (coefficientFiniteTensorModelIso.{u, u} l E X
    (calculus l E X).toCoefficientDerivedSystemTensors r (Fc.obj P) (Fc.obj Q)
    ((calculus l E X).quotientCalculus.preservesKFlat (k.trans h) P hp)
    ((calculus l E X).quotientCalculus.preservesKFlat (k.trans h) Q hq)).hom
  let e (Y : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ) :=
    (finiteHomTensorComparison l E X h).app Y
  let f (Y : CochainComplex (normalizedDVRModules.{u, u} l E X m) ℤ) :=
    (finiteHomTensorComparison l E X k).app Y
  let g (Y : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ) :=
    (finiteHomTensorComparison l E X (k.trans h)).app Y
  let z (Y : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ) :=
    DerivedCategory.Q.map ((finiteHomTensorChainAssoc l E X h k).hom.app Y)
  have he (Y : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ)
      (hy : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) Y) :
      IsIso (g Y) := by
    dsimp only [g]
    rw [comparison_model l E X (k.trans h) Y hy]
    infer_instance
  have := he P hp
  have := he Q hq
  have : IsIso (Prod.mkHom (g P) (g Q)) := by
    change IsIso ((asIso (g P)).prod (asIso (g Q))).hom
    infer_instance
  have ha := tensorChain_model l E X h P Q hp hq
  have hb := tensorChain_model l E X k (Fa.obj P) (Fa.obj Q)
    ((calculus l E X).quotientCalculus.preservesKFlat h P hp)
    ((calculus l E X).quotientCalculus.preservesKFlat h Q hq)
  have hc := tensorChain_model l E X (k.trans h) P Q hp hq
  have hs : V.map (Prod.mkHom (cc.hom.app (DerivedCategory.Q.obj P))
        (cc.hom.app (DerivedCategory.Q.obj Q))) ≫ V.map (Prod.mkHom (g P) (g Q)) =
      V.map (Prod.mkHom (G.map (e P)) (G.map (e Q))) ≫
        V.map (Prod.mkHom (f (Fa.obj P)) (f (Fa.obj Q))) ≫
          V.map (Prod.mkHom (z P) (z Q)) := by
    rw [← V.map_comp, ← V.map_comp, ← V.map_comp]
    congr 1
    exact Prod.ext (finiteHomTensor_associatorModel l E X h k P)
      (finiteHomTensor_associatorModel l E X h k Q)
  have hr : DerivedCategory.Q.map
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X r)).map
        (Prod.mkHom ((finiteHomTensorChainAssoc l E X h k).hom.app P)
          ((finiteHomTensorChainAssoc l E X h k).hom.app Q))) ≫
        rC = rT ≫ V.map (Prod.mkHom (z P) (z Q)) := by
    exact ((calculus l E X).finiteTensorModel r).comparison.hom.naturality
      (Prod.mkHom (ObjectProperty.homMk
        (X := ⟨Fb.obj (Fa.obj P), (calculus l E X).quotientCalculus.preservesKFlat k _
          ((calculus l E X).quotientCalculus.preservesKFlat h P hp)⟩)
        (Y := ⟨Fc.obj P, (calculus l E X).quotientCalculus.preservesKFlat (k.trans h) P hp⟩)
        ((finiteHomTensorChainAssoc l E X h k).hom.app P))
      (ObjectProperty.homMk
        (X := ⟨Fb.obj (Fa.obj Q), (calculus l E X).quotientCalculus.preservesKFlat k _
          ((calculus l E X).quotientCalculus.preservesKFlat h Q hq)⟩)
        (Y := ⟨Fc.obj Q, (calculus l E X).quotientCalculus.preservesKFlat (k.trans h) Q hq⟩)
        ((finiteHomTensorChainAssoc l E X h k).hom.app Q)))
  have hnat := ((calculus l E X).quotientCalculus.tensor k).hom.naturality
    (Prod.mkHom (e P) (e Q))
  change G.map (U.map (Prod.mkHom (e P) (e Q))) ≫ _ =
    _ ≫ V.map (Prod.mkHom (G.map (e P)) (G.map (e Q))) at hnat
  have hf := (finiteHomTensorComparison l E X k).naturality (tensorChain l E X h P Q hp hq).hom
  have hga := map_three_eq_three G ha
  have ht := map_three_comp_eq DerivedCategory.Q
    (chain_tensor_coherence l E X h k P Q hp hq)
  have hcc := finiteHomTensor_associatorModel l E X h k
    ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
      (integralCoefficientCommRingSheaf.{u, u} l E X n)).obj (P, Q))
  have hn := cc.hom.naturality rR
  apply (cancel_epi (G.map (F.map rR))).mp
  apply (cancel_mono (V.map (Prod.mkHom (g P) (g Q)))).mp
  simp only [Category.assoc]
  exact CategoryTheory.ScalarHomTensor.diagram_paste
    hs hnat.symm hga hb hf hr.symm ht hcc.symm hc.symm hn.symm

private theorem intrinsic_representatives (n : ℕ) (Y : normalizedDVRDerived l E X n) :
    ∃ P : CochainComplex (normalizedDVRModules.{u, u} l E X n) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ Y) := by
  apply representatives_of_resolution
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n))
    ?_ Y
  intro P
  obtain ⟨P', p, hp, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n) P
  exact ⟨P', p, hp, hq⟩

end Representatives

/-- The normalized tensorators commute with the prescribed scalar associator.
Source: blueprint lemma-change-coefficients-internal-hom--1, proof of the successive-quotient tensor
square (blueprint: lem-coef-finite-hom-intrinsic-tensor-composition).

Proof: the quotient calculus supplies normalized ordinary and derived adjunctions.
Extend its unit equation from K-flat representatives to every complex by naturality
along a K-flat resolution. Transpose twice to identify the prescribed derived
associator with the localization of the ordinary adjunction composition map.
The ordinary unit sends successive scalar generators to the direct generator,
since restriction composition is the identity on underlying sections. Thus the
chain tensor square follows by the composite adjunction bijection and equality
on total pure generators. Paste the three specified tensor-model squares with
this chain square and the associator comparison. Cancel the invertible K-flat
comparisons, resolve both arbitrary derived inputs, and use naturality. -/
theorem finiteHomIntrinsic_tensorComposition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) (K M : normalizedDVRDerived l E X n) :
    let S := (coefficientDerivedSystemEvaluationCalculus l E X).choose
    let μ := S.quotientCalculus.tensor h
    let ν := S.quotientCalculus.tensor k
    let ξ := S.quotientCalculus.tensor (k.trans h)
    let α := finiteHomIntrinsicAssoc l E X h k
    let F := coefficientFiniteQuotientDerived l E X h
    let G := coefficientFiniteQuotientDerived l E X k
    G.map (μ.hom.app (K, M)) ≫ ν.hom.app (F.obj K, F.obj M) ≫
        (finiteIntrinsicClosed l E X r).tensor.map
          (Prod.mkHom (α.hom.app K) (α.hom.app M)) =
      α.hom.app ((finiteIntrinsicClosed l E X n).tensor.obj (K, M)) ≫
        ξ.hom.app (K, M) := by
  exact tensor_square_descent
    ((calculus l E X).finiteClosed n).tensor ((calculus l E X).finiteClosed m).tensor
    ((calculus l E X).finiteClosed r).tensor
    (coefficientFiniteQuotientDerived.{u, u} l E X h)
    (coefficientFiniteQuotientDerived.{u, u} l E X k)
    (coefficientFiniteQuotientDerived.{u, u} l E X (k.trans h))
    ((calculus l E X).quotientCalculus.tensor h) ((calculus l E X).quotientCalculus.tensor k)
    ((calculus l E X).quotientCalculus.tensor (k.trans h)) (finiteHomIntrinsicAssoc l E X h k)
    DerivedCategory.Q.obj
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf.{u, u} l E X n))
    (intrinsic_representatives l E X n) (representative_tensor_coherence l E X h k) K M

end WeilConjectures
