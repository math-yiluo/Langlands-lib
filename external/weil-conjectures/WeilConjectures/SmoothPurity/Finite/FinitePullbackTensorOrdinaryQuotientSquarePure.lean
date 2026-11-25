/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatNormalization
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTotalTensorMapGenerators

/-! Pure-generator component calculation for the ordinary quotient/pullback tensor square.
Source: Stacks Tags 03EL, 06YY and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-ordinary-quotient-square-pure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
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

attribute [local irreducible] constantSheaf Functor.leftAdjoint presheafToSheaf
  pullbackTensorCalculus coefficientFiniteQuotientExtension
  coefficientFiniteQuotientUnitSection sfIntrinsicPullback sfIntrinsicConstantModuleAdjunction
  coefficientTotalTensor coefficientTensorGenerator SheafOfModules.monoidalCategory
attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

private theorem quotient_unit (W : Scheme.{u})
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    (M : normalizedDVRModules l E W m) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    coefficientRestrictionSection (normalizedDVRQuotient l E W h)
      ((coefficientFiniteQuotientExtension l E W h).obj M) V
      (((D.ordinaryAdjunction h).unit.app
        M).val.app V x) = coefficientFiniteQuotientUnitSection l E W h M V x := by
  exact D.ordinary_unit h M V x

private theorem quotient_unit_naturality (W : Scheme.{u})
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    {M N : normalizedDVRModules l E W m} (a : M ⟶ N) (V : W.ProEtᵒᵖ)
    (x : M.val.obj V) :
    ((coefficientFiniteQuotientExtension l E W h).map a).val.app V
        (coefficientFiniteQuotientUnitSection l E W h M V x) =
      coefficientFiniteQuotientUnitSection l E W h N V (a.val.app V x) := by
  have hn := congrArg (fun t ↦ coefficientRestrictionSection
    (normalizedDVRQuotient l E W h) ((coefficientFiniteQuotientExtension l E W h).obj N)
    V (t.val.app V x))
    ((D.ordinaryAdjunction h).unit.naturality a)
  change coefficientRestrictionSection (normalizedDVRQuotient l E W h) _ V
    (((D.ordinaryAdjunction h).unit.app
      N).val.app V (a.val.app V x)) =
    ((coefficientFiniteQuotientExtension l E W h).map a).val.app V
      (coefficientRestrictionSection (normalizedDVRQuotient l E W h) _ V
        (((D.ordinaryAdjunction h).unit.app
          M).val.app V x)) at hn
  rw [quotient_unit, quotient_unit] at hn
  exact hn.symm

private theorem pullback_unit_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    {M N : normalizedDVRModules l E Y n} (a : M ⟶ N) (U : Y.ProEt)
    (x : M.val.obj (op U)) :
    ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).map a).val.app
        (op ((proEtaleBaseChange f).obj U))
        (((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app N).val.app (op U)
          (a.val.app (op U) x) := by
  exact (congrArg (fun t ↦ t.val.app (op U) x)
    ((sfIntrinsicConstantModuleAdjunction f
      (finiteCoefficientRing l E (n + 1))).unit.naturality a)).symm

private abbrev direct_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (N : proEtaleRingModules X (proEtaleConstantRing X A))
    (U : Y.ProEt)
    (x : ((proEtaleConstantModuleDirectImage f A).obj N).val.obj (op U)) :
    N.val.obj (op ((proEtaleBaseChange f).obj U)) := x

private theorem direct_section_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (N : proEtaleRingModules X (proEtaleConstantRing X A))
    (U : Y.ProEt) : Function.Injective (direct_section f A N U) := fun _ _ h ↦ h

-- Abstract rings prevent kernel unfolding of both concrete quotient-ring constructions.
private theorem restriction_section_injective {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) RingCat.{u + 1}} (φ : R ⟶ S)
    (N : SheafOfModules.{u + 1} S) (V : W.ProEtᵒᵖ) :
    Function.Injective (coefficientRestrictionSection φ N V) := fun _ _ h ↦ h

private theorem transpose_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemTensors l E X)
    (D : CoefficientFiniteQuotientCalculus l E X S)
    {m n : ℕ} (h : n ≤ m) (M : normalizedDVRModules l E Y m)
    (N : normalizedDVRModules l E X n)
    (a : (coefficientFiniteQuotientExtension l E X h).obj
      ((sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f).obj M) ⟶ N)
    (U : Y.ProEt) (x : M.val.obj (op U)) :
    coefficientRestrictionSection (normalizedDVRQuotient l E X h) N
      (op ((proEtaleBaseChange f).obj U))
      (direct_section f (finiteCoefficientRing l E (m + 1))
        ((normalizedDVRModuleRes l E X h).obj N) U
        ((((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (m + 1))).homEquiv _ _)
          (((D.ordinaryAdjunction h).homEquiv _ _) a)).val.app (op U) x)) =
    a.val.app (op ((proEtaleBaseChange f).obj U))
      (coefficientFiniteQuotientUnitSection l E X h _
        (op ((proEtaleBaseChange f).obj U))
        (((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (m + 1))).unit.app M).val.app (op U) x)) := by
  simp only [Adjunction.homEquiv_unit]
  change a.val.app _ (coefficientRestrictionSection (normalizedDVRQuotient l E X h)
    _ _ (((D.ordinaryAdjunction h).unit.app _).val.app _ _)) = _
  exact congrArg (a.val.app _) (quotient_unit l E X S D h _ _ _)

private abbrev pullback_unit_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (U : Y.ProEt) (x : M.val.obj (op U)) :
    ((sfIntrinsicPullback A f).obj M).val.obj (op ((proEtaleBaseChange f).obj U)) :=
  direct_section f A ((sfIntrinsicPullback A f).obj M) U
    (((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app (op U) x)

private theorem morphism_eq_apply {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} {a b : M ⟶ N} (h : a = b)
    (V : W.ProEtᵒᵖ) (x : M.val.obj V) : a.val.app V x = b.val.app V x :=
  congrArg (fun t ↦ t.val.app V x) h

/-- A function diagram calculation, with all section types and maps held abstract. -/
private theorem square_of_generators
    {H I J Z M A B C D L N T : Type*}
    (g : H → I) (a : I → J) (j : M → I) (t : J → Z)
    (c : H → L) (b : L → N) (k : N → Z)
    (pair : A → B → J) (pair' : C → D → Z) (cp : A → C) (cq : B → D)
    (unit : T → N) {w : H} {v₀ v₁ : M} {xa : A} {xb : B} {ya : C} {yb : D}
    {vL : L} {vT₀ vT₁ : T}
    (h₀ : g w = j v₀) (h₁ : v₀ = v₁) (h₂ : a (j v₁) = pair xa xb)
    (h₃ : t (pair xa xb) = pair' (cp xa) (cq xb))
    (h₄ : cp xa = ya) (h₅ : cq xb = yb) (h₆ : k (unit vT₁) = pair' ya yb)
    (h₇ : c w = vL) (h₈ : b vL = unit vT₀) (h₉ : vT₀ = vT₁) :
    t (a (g w)) = k (b (c w)) := by
  calc
    t (a (g w)) = t (a (j v₀)) := congrArg (fun z ↦ t (a z)) h₀
    _ = t (a (j v₁)) := congrArg (fun z ↦ t (a (j z))) h₁
    _ = t (pair xa xb) := congrArg t h₂
    _ = pair' (cp xa) (cq xb) := h₃
    _ = pair' ya yb := congrArg₂ pair' h₄ h₅
    _ = k (unit vT₁) := h₆.symm
    _ = k (unit vT₀) := congrArg (fun z ↦ k (unit z)) h₉.symm
    _ = k (b vL) := congrArg k h₈.symm
    _ = k (b (c w)) := congrArg (fun z ↦ k (b z)) h₇.symm

-- Elaborate the mapped complexes with the quotient calculus held abstract.
private theorem ordinary_quotient_square_calculus {X Y : Scheme.{u}} (f : X ⟶ Y)
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
    (P Q : CochainComplex (normalizedDVRModules l E Y m) ℤ) (i : ℤ)
    (S : CoefficientDerivedSystemTensors l E X)
    (D : CoefficientFiniteQuotientCalculus l E X S) :
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
      let adjX := D.ordinaryAdjunction h
      let adjF := sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (m + 1))
      (adjF.homEquiv _ _
        (adjX.homEquiv _ _
          ((GX.map km.hom ≫ ax.hom ≫ TXn.map
            (Prod.mkHom (cc.hom.app P) (cc.hom.app Q))).f i))) =
        (adjF.homEquiv _ _
          (adjX.homEquiv _ _
            ((cc.hom.app (TYm.obj (P, Q)) ≫ Fn.map ay.hom ≫ kn.hom).f i))) := by
  intro Fm Fn GX GY TYm TXm TYn TXn km kn ax ay hkm hkn hax hay adjX adjF
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u}
    (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y m) P Q i _
  intro p q hpq U x y
  let V := op ((proEtaleBaseChange f).obj U.unop)
  let H := (TXn.obj (Fn.obj (GY.obj P), Fn.obj (GY.obj Q))).X i
  apply direct_section_injective f (finiteCoefficientRing l E (m + 1))
    ((normalizedDVRModuleRes l E X h).obj H) U.unop
  apply restriction_section_injective (normalizedDVRQuotient l E X h) H V
  refine (transpose_apply l E f _ D h _ _ _ U.unop _).trans ?_
  refine Eq.trans ?_ (transpose_apply l E f _ D h _ _ _ U.unop _).symm
  change (((TXn.map (Prod.mkHom (cc.hom.app P) (cc.hom.app Q))).f i).val.app V
    ((ax.hom.f i).val.app V
      (((coefficientFiniteQuotientExtension l E X h).map (km.hom.f i)).val.app V
        (coefficientFiniteQuotientUnitSection l E X h _ V
            (((sfIntrinsicConstantModuleAdjunction f
              (finiteCoefficientRing l E (m + 1))).unit.app ((TYm.obj (P, Q)).X i)).val.app U
              (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
                (integralCoefficientCommRingSheaf l E Y m) P Q p q i hpq U x y)))))) =
    (kn.hom.f i).val.app V
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).map
        (ay.hom.f i)).val.app V
        (((cc.hom.app (TYm.obj (P, Q))).f i).val.app V
          (coefficientFiniteQuotientUnitSection l E X h _ V
              (((sfIntrinsicConstantModuleAdjunction f
                (finiteCoefficientRing l E (m + 1))).unit.app ((TYm.obj (P, Q)).X i)).val.app U
                (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
                  (integralCoefficientCommRingSheaf l E Y m) P Q p q i hpq U x y)))))
  let um := pullback_unit_section f (finiteCoefficientRing l E (m + 1))
  let un := pullback_unit_section f (finiteCoefficientRing l E (n + 1))
  let z := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
    (integralCoefficientCommRingSheaf l E Y m) P Q p q i hpq U x y
  let xa := coefficientFiniteQuotientUnitSection l E X h _ V (um (P.X p) U.unop x)
  let xb := coefficientFiniteQuotientUnitSection l E X h _ V (um (Q.X q) U.unop y)
  let ya := coefficientFiniteQuotientUnitSection l E Y h (P.X p) U x
  let yb := coefficientFiniteQuotientUnitSection l E Y h (Q.X q) U y
  exact square_of_generators
    (((coefficientFiniteQuotientExtension l E X h).map (km.hom.f i)).val.app V)
    ((ax.hom.f i).val.app V)
    (coefficientFiniteQuotientUnitSection l E X h _ V)
    (((TXn.map (Prod.mkHom (cc.hom.app P) (cc.hom.app Q))).f i).val.app V)
    (((cc.hom.app (TYm.obj (P, Q))).f i).val.app V)
    (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).map
      (ay.hom.f i)).val.app V)
    ((kn.hom.f i).val.app V)
    (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)
      (GX.obj (Fm.obj P)) (GX.obj (Fm.obj Q)) p q i hpq V)
    (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)
      (Fn.obj (GY.obj P)) (Fn.obj (GY.obj Q)) p q i hpq V)
    (((cc.hom.app P).f p).val.app V) (((cc.hom.app Q).f q).val.app V)
    (un ((TYn.obj (GY.obj P, GY.obj Q)).X i) U.unop)
    (quotient_unit_naturality l E X _ D h (km.hom.f i) V _)
    (hkm p q i hpq U.unop x y)
    (hax p q i hpq V (um (P.X p) U.unop x) (um (Q.X q) U.unop y))
    (coefficientTotalTensor_map_generator X (integralCoefficientCommRingSheaf l E X n)
      (cc.hom.app P) (cc.hom.app Q) p q i hpq V xa xb)
    ((morphism_eq_apply (hcc P p) V xa).trans (hc (P.X p) U.unop x))
    ((morphism_eq_apply (hcc Q q) V xb).trans (hc (Q.X q) U.unop y))
    (hkn p q i hpq U.unop ya yb)
    ((morphism_eq_apply (hcc (TYm.obj (P, Q)) i) V
      (coefficientFiniteQuotientUnitSection l E X h _ V
        (um ((TYm.obj (P, Q)).X i) U.unop z))).trans
      (hc ((TYm.obj (P, Q)).X i) U.unop z))
    (pullback_unit_naturality l E f n (ay.hom.f i) U.unop
      (coefficientFiniteQuotientUnitSection l E Y h ((TYm.obj (P, Q)).X i) U z))
    (hay p q i hpq U x y)

-- The public interface retains invertibility; the ordinary unit calculation does not need it.
set_option linter.unusedVariables false in
/-- Equality of the two comparison composites in one cochain degree.
This is the component calculation used to prove the chain-map equality; it is the
ordinary pure-tensor generator calculation after applying the stated normalizations.
Source: Stacks Tags 03EL, 06YY and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-ordinary-quotient-square-pure).
-/
theorem finitePullbackTensor_ordinary_quotient_square_pure {X Y : Scheme.{u}} (f : X ⟶ Y)
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
    (P Q : CochainComplex (normalizedDVRModules l E Y m) ℤ) (i : ℤ) :
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
      let adjX := (pullbackTensorCalculus l E X).quotientCalculus.ordinaryAdjunction h
      let adjF := sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (m + 1))
      (adjF.homEquiv _ _
        (adjX.homEquiv _ _
          ((GX.map km.hom ≫ ax.hom ≫ TXn.map
            (Prod.mkHom (cc.hom.app P) (cc.hom.app Q))).f i))) =
        (adjF.homEquiv _ _
          (adjX.homEquiv _ _
            ((cc.hom.app (TYm.obj (P, Q)) ≫ Fn.map ay.hom ≫ kn.hom).f i))) := by
  clear hX hY
  exact ordinary_quotient_square_calculus l E f h c hc cc hcc P Q i
    (pullbackTensorCalculus l E X).toCoefficientDerivedSystemTensors
    (pullbackTensorCalculus l E X).quotientCalculus

end WeilConjectures
