/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorComponents
import WeilConjectures.SixFunctors.IntegralHom.Reduction.ReductionTensorResolutionComparison
import WeilConjectures.SixFunctors.IntegralHom.PerfectCoefficientSignedHomAction
import WeilConjectures.SixFunctors.IntegralHom.Scalar.IntegralHomScalarEvaluationInvertible
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralReductionTwoTermResolution

/-! # Completed-ring representatives of reduced evaluation

Source: the finite-free calculation and evaluation sentence of
`lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

private theorem exists_iso_with_transpose
    {C : Type*} [Category C] {W : Type*} {X Y Z A B : C}
    (e : W ≃ (X ⟶ Y)) (w : W) (f : Z ⟶ A) (g : A ⟶ B) (h : B ⟶ Y)
    (ht : IsIso ((f ≫ g) ≫ h)) (hw : IsIso (e w)) :
    ∃ s : X ≅ Z, e.symm (s.hom ≫ f ≫ g ≫ h) = w := by
  let s := asIso (e w) ≪≫ (asIso ((f ≫ g) ≫ h)).symm
  refine ⟨s, ?_⟩
  have hst : s.hom ≫ f ≫ g ≫ h = e w := calc
    _ = s.hom ≫ ((f ≫ g) ≫ h) := by simp only [Category.assoc]
    _ = e w := by
      dsimp only [s, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (congrArg e.symm hst).trans (e.symm_apply_apply w)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local irreducible] totalTensor homComplexFunctor homModelMap
  derivedInternalHomOfUniverses scalarReductionDerivedExtension scalarReductionDerivedRestriction
  scalarReductionExistence scalarReductionDerivedExistence

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The completed-ring reduction of evaluation is computed by signed chain evaluation.
This holds for an arbitrary K-flat coefficient resolution, with no boundedness
assumption on it. It contains no finite-coefficient internal Hom or comparison map.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2,
finite-free construction and compatibility with actual evaluation; Stacks 06YY,
07A4, 07A6, 08J7, 08J9 and 0A8X
(blueprint: lem-sf-integral-hom-reduced-evaluation-representative).

Proof: use the scalar tensor-resolution comparison and eI to obtain r.
Choose the proved two-term free resolution of the restricted quotient. Its
augmentation and epsilon give a derived isomorphism between Q and that
resolution. The perfect-coefficient signed-action theorem shows that the
composite of the localized f and homModelMap is invertible. Transport it by
eP and r to an isomorphism t into Hom(K, U(F(L))). Independently, the scalar
finite-coefficient argument shows that the completed-ring transpose g of the
right-hand side is invertible. Set s = g followed by the inverse of t.
Then s.hom followed by t is g, by inverse cancellation, and applying the inverse
Hom-tensor adjunction gives the required equality. The statement only asks
for the existence of s; it does not prescribe a canonical coefficient-model
isomorphism. No additional naturality of the family a.adjunction in K is used.
This reduces the theorem to separate scalar-model and invertibility assertions;
these three assertions are the remaining named proof obligations. Zero complexes,
the empty site, n=0 and a zero quotient require no nonvanishing premise. -/
theorem reduced_evaluation_representative
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl)
    (P I Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hP : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P) (hI : I.IsKInjective)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L)
    (hQ : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q)
    (epsilon : Q ⟶
      ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (scalarReductionTarget l E Y n) 0).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n))))
    (hepsilon : QuasiIso epsilon)
    (f : ((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
          (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := completedIntegralCommRingSheaf l E Y D hl) P I)).obj Q ⟶
        homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := completedIntegralCommRingSheaf l E Y D hl) P
          (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj I).obj Q))
    (hf : IsSignedHomTensor Y (completedIntegralCommRingSheaf l E Y D hl) P I Q f) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let U := scalarReductionDerivedRestriction l E Y n
    let F := integralDerivedReduction l E Y D hl n
    let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
    let H := (hom.{t, u} Y R).obj (op K, L)
    let X := U.obj (F.obj H)
    let J := ((totalTensor.{t, u} Y R).obj I).obj Q
    ∃ (r : U.obj (F.obj L) ≅ DerivedCategory.Q.obj J)
      (s : X ≅ DerivedCategory.Q.obj (((totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q)),
      ((a.adjunction K).homEquiv X (U.obj (F.obj L))).symm
          (s.hom ≫ DerivedCategory.Q.map f ≫ homModelMap.{t, u} Y R P J ≫
            (hom.{t, u} Y R).map (Prod.mkHom eP.inv.op r.inv)) =
        adj.homEquiv (a.tensor.obj (K, X)) (F.obj L)
          (m.mu.hom.app (K, X) ≫
            m.target.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj H))) ≫
            m.mu.inv.app (K, H) ≫ F.map ((a.adjunction K).counit.app L)) := by
  classical
  dsimp only
  let U := scalarReductionDerivedRestriction l E Y n
  let F := integralDerivedReduction l E Y D hl n
  let V := F ⋙ U
  let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
  let H := (hom.{t, u} Y
    (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)
  let X := U.obj (F.obj H)
  let J := ((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj I).obj Q
  let b := (reduction_tensor_resolution_comparison l E Y D hl n Q hQ
    epsilon hepsilon).some
  let r : U.obj (F.obj L) ≅ DerivedCategory.Q.obj J :=
    (V.mapIso eI).symm ≪≫ b.app I
  let hres := integralReduction_twoTerm_resolution l E Y D hl n
  let Q0 := hres.choose
  let hQ0 := hres.choose_spec.choose
  let hzero := hres.choose_spec.choose_spec.choose
  let eNeg := hres.choose_spec.choose_spec.choose_spec.choose
  let eZero := hres.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let epsilon0 := hres.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hepsilon0 := hres.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have : IsIso (DerivedCategory.Q.map epsilon) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hepsilon
  have : IsIso (DerivedCategory.Q.map epsilon0) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hepsilon0
  let eQ : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj Q0 :=
    asIso (DerivedCategory.Q.map epsilon) ≪≫ (asIso (DerivedCategory.Q.map epsilon0)).symm
  have ht := perfectCoefficient_signedHomAction_isIso Y
    (completedIntegralCommRingSheaf l E Y D hl) P I Q Q0
    hP hI hQ hQ0 hzero eNeg eZero eQ f hf
  let t : DerivedCategory.Q.obj (((totalTensor.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)).obj
      (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := completedIntegralCommRingSheaf l E Y D hl) P I)).obj Q) ⟶
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, U.obj (F.obj L)) :=
    (DerivedCategory.Q.map f ≫
      homModelMap.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P J) ≫
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).map (Prod.mkHom eP.inv.op r.inv)
  have : IsIso t := by
    dsimp only [t]
    have hprod : IsIso (Prod.mkHom eP.inv.op r.inv) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    exact IsIso.comp_isIso' ht
      (@Functor.map_isIso _ _ _ _ _ _
        (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
        (Prod.mkHom eP.inv.op r.inv) hprod)
  let g : X ⟶ (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
      (op K, U.obj (F.obj L)) :=
    (a.adjunction K).homEquiv X (U.obj (F.obj L))
      (adj.homEquiv (a.tensor.obj (K, X)) (F.obj L)
        (m.mu.hom.app (K, X) ≫
          m.target.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj H))) ≫
          m.mu.inv.app (K, H) ≫ F.map ((a.adjunction K).counit.app L)))
  have : IsIso g := scalar_reduced_evaluation_transpose_isIso l E Y D hl a n m K L
  refine ⟨r, ?_⟩
  exact exists_iso_with_transpose
    ((a.adjunction K).homEquiv X (U.obj (F.obj L))) _
    (DerivedCategory.Q.map f)
    (homModelMap.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P J)
    ((hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).map
      (Prod.mkHom eP.inv.op r.inv))
    (inferInstance : IsIso t) (inferInstance : IsIso g)

end WeilConjectures.IntegralHom
