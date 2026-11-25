/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatNormalization
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorOrdinaryQuotientSquareComponent

/-! # The ordinary total-tensor quotient and pullback square

Source: Stacks Tags 03EL, 06YY and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-ordinary-quotient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  coefficientFiniteQuotientDerived coefficientFiniteQuotientModel
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] sfIntrinsicPullback_additive
  coefficientFiniteQuotientExtensionAdditive

/-- Coefficient change commutes with the ordinary total pullback tensor comparisons.
Source: Stacks 03EL, 07A4 and 06YY, the ordinary generator calculation
(blueprint: lem-pur-finite-pullback-tensor-ordinary-quotient-square).
Proof: equality of chain maps is checked in every total degree. Apply scalar-extension
adjunction, then inverse-image adjunction, and the tensor sheafification adjunction.
The direct-sum total inclusions reduce the comparison to pure tensors x tensor y
in one bidegree. Naturality of the adjunction units moves km and ay through the two
units. Their generator equations, and those of ax and kn, send this generator on
both paths to the tensor of the inverse-image units of the quotient units of x
and y. The equation hc identifies the two iterated units; hcc identifies each
component of cc with c. Balancing and linearity extend from pure tensors;
sheafification and the coproduct universal property give equality. The maps
already commute with the signed total differential, since all four comparisons
are chain isomorphisms. No derived object, K-flatness, flatness of terms or
flatness of the coefficient quotient is used. -/
theorem finitePullbackTensor_ordinary_quotient_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    {m n : ℕ} (h : n ≤ m)
    (c : sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f ⋙
        coefficientFiniteQuotientExtension l E X h ≅
      coefficientFiniteQuotientExtension l E Y h ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (M : normalizedDVRModules l E Y m) (U : Y.ProEt)
        (x : M.val.obj (Opposite.op U)),
        (c.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (coefficientFiniteQuotientUnitSection l E X h
            ((sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f).obj M)
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((sfIntrinsicConstantModuleAdjunction f
              (finiteCoefficientRing l E (m + 1))).unit.app M).val.app (Opposite.op U) x)) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app
            ((coefficientFiniteQuotientExtension l E Y h).obj M)).val.app (Opposite.op U)
          (coefficientFiniteQuotientUnitSection l E Y h M (Opposite.op U) x))
    (cc : (sfIntrinsicPullback
        (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ) ⋙
        (coefficientFiniteQuotientExtension l E X h).mapHomologicalComplex (.up ℤ) ≅
      (coefficientFiniteQuotientExtension l E Y h).mapHomologicalComplex (.up ℤ) ⋙
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ))
    (hcc : ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ) (i : ℤ),
      (cc.hom.app P).f i = c.hom.app (P.X i))
    (P Q : CochainComplex (normalizedDVRModules l E Y m) ℤ) :
    let Fm := (sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex
      (.up ℤ)
    let Fn := (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
      (.up ℤ)
    let GX := (coefficientFiniteQuotientExtension l E X h).mapHomologicalComplex (.up ℤ)
    let GY := (coefficientFiniteQuotientExtension l E Y h).mapHomologicalComplex (.up ℤ)
    let TYm := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y m)
    let TXm := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X m)
    let TYn := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)
    let TXn := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)
    ∀ (km : Fm.obj (TYm.obj (P, Q)) ≅ TXm.obj (Fm.obj P, Fm.obj Q))
      (kn : Fn.obj (TYn.obj (GY.obj P, GY.obj Q)) ≅
        TXn.obj (Fn.obj (GY.obj P), Fn.obj (GY.obj Q)))
      (ax : GX.obj (TXm.obj (Fm.obj P, Fm.obj Q)) ≅
        TXn.obj (GX.obj (Fm.obj P), GX.obj (Fm.obj Q)))
      (ay : GY.obj (TYm.obj (P, Q)) ≅ TYn.obj (GY.obj P, GY.obj Q)),
      FinitePullbackTensorGenerators l E f m P Q km →
      FinitePullbackTensorGenerators l E f n (GY.obj P) (GY.obj Q) kn →
      CoefficientScalarTensorGenerators.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m)
        (integralCoefficientCommRingSheaf l E X n)
        (coefficientFiniteQuotientExtension l E X h)
        (hF := coefficientFiniteQuotientExtensionAdditive l E X h)
        (coefficientFiniteQuotientUnitSection l E X h) (Fm.obj P) (Fm.obj Q) ax →
      CoefficientScalarTensorGenerators.{u, u + 1, u} (ProEt.topology Y)
        (integralCoefficientCommRingSheaf l E Y m)
        (integralCoefficientCommRingSheaf l E Y n)
        (coefficientFiniteQuotientExtension l E Y h)
        (hF := coefficientFiniteQuotientExtensionAdditive l E Y h)
        (coefficientFiniteQuotientUnitSection l E Y h) P Q ay →
      GX.map km.hom ≫ ax.hom ≫ TXn.map
          (Prod.mkHom (cc.hom.app P) (cc.hom.app Q)) =
        cc.hom.app (TYm.obj (P, Q)) ≫ Fn.map ay.hom ≫ kn.hom := by
  dsimp
  intro km kn ax ay hkm hkn hax hay
  apply HomologicalComplex.Hom.ext
  funext i
  exact finitePullbackTensor_ordinary_quotient_square_component l E f h c hc cc hcc P Q i
    km kn ax ay hkm hkn hax hay

end WeilConjectures
