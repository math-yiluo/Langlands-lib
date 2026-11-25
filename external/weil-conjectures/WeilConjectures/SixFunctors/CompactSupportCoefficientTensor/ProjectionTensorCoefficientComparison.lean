/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Rational.RationalCoefficientCategoryComparison
public import WeilConjectures.SixFunctors.WfTensorCompletion.WfTensorCompletionFrobenius
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel
public import WeilConjectures.SixFunctors.ProjectionTensorCoefficient.ProjectionCoefficientTensorTotal
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorCompletionModelExistence
import all WeilConjectures.SixFunctors.ProjectionTensorNormalization.ProjectionTensorNormalization
import all WeilConjectures.SixFunctors.ProjectionTensorModelComparison.ProjectionTensorModelComparison
import WeilConjectures.SixFunctors.CompactSupportCoefficientTensor.ProjectionRationalTensorDescent

/-! # The representative-normalized tensor comparison for projection

Source: main-20261015, projection-formula proof step 13
(blueprint: def-sf-projection-tensor-coefficient-comparison).
The ordinary comparison is fixed on homogeneous local pure tensors. Derived
descent and the specified quotient-completion unit then fix its integral and
rational constructible restrictions.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.ProjectionTensorCoefficient

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted SheafOfModules.monoidalCategory
attribute [local instance 3000] integralTowerHasDerivedCategory

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

/-- Coefficient restriction preserves the precise resolving class.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: an exact equivalence preserves acyclicity and tensor flatness. The local
pure-tensor isomorphism identifies tensoring a transported complex with
transporting its tensor against the inverse-transported complex. Thus K-flatness
and termwise flatness are preserved without a boundedness restriction. -/
theorem good (P : (proEtaleFlatRepresentatives X
      (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory) :
    proEtaleFlatRepresentatives X (pbcAdicCompletion X (pbcIntegralDatum l E))
      ((complexTransport l E X).obj P.obj) := by
  exact ProjectionTensorNormalization.good l E X P

/-- The signed-total comparison is natural in both input complexes.
Source: projection-formula proof step 13
(blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: expand `totalIso` as the inverse signed total; evaluate a component on a homogeneous
summand; use `module_tensorHom_naturality` and the defining signed-total map equations. -/
private theorem totalIso_naturality
    {P P' Q Q' : CochainComplex (integralTowerModules l E X) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (complexTransport l E X).map
        ((constructibleTensorTotal l E X).map (Prod.mkHom f g)) ≫
      (totalIso l E X P' Q').hom =
    (totalIso l E X P Q).hom ≫
      (totalTarget l E X).map (Prod.mkHom f g) := by
  exact ProjectionTensorNormalization.totalIso_naturality l E X f g

private theorem normalizedTensorDescent
    {K : Type u₁} [Category.{v₁} K] {H : Type u₂} [Category.{v₂} H]
    {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]
    (q : K ⥤ D) (q' : H ⥤ E) (F : K ⥤ H) (LF : D ⥤ E)
    (eps : q ⋙ LF ≅ F ⋙ q')
    (P : ObjectProperty K) (S : ObjectProperty H)
    (hF : ∀ X, P X → S (F.obj X))
    (ff : ((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory) (D × D) E).obj
      ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful)
    (t : K × K ⥤ K) (t' : H × H ⥤ H)
    (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ q' ≅ ((S.ι ⋙ q').prod (S.ι ⋙ q')) ⋙ T')
    (b : ∀ Z : K × K, F.obj (t.obj Z) ≅ t'.obj ((F.prod F).obj Z))
    (hb : ∀ {X Y : K × K} (f : X ⟶ Y),
      F.map (t.map f) ≫ (b Y).hom = (b X).hom ≫ t'.map ((F.prod F).map f)) :
    ∃! a : T ⋙ LF ≅ (LF.prod LF) ⋙ T',
      ∀ X Y : P.FullSubcategory,
        LF.map (r.hom.app (X, Y)) ≫ a.hom.app (q.obj X.obj, q.obj Y.obj) ≫
            T'.map (Prod.mkHom (eps.hom.app X.obj) (eps.hom.app Y.obj)) ≫
            r'.inv.app (⟨F.obj X.obj, hF X.obj X.property⟩,
              ⟨F.obj Y.obj, hF Y.obj Y.property⟩) =
          eps.hom.app (t.obj (X.obj, Y.obj)) ≫ q'.map ((b (X.obj, Y.obj)).hom) := by
  exact ProjectionTensorNormalization.normalizedTensorDescent q q' F LF eps P S hF ff
    t t' T T' r r' b (fun f ↦ hb f)

/-- The signed-total representative square specifying the ordinary comparison.
Source: projection-formula proof step 13
(blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def ordinaryNormalization
    (T : ProEtaleTensorModel X (completedIntegralCommRingSheafUnrestricted l E X))
    (e : T.tensor ⋙ integralDetailedTransport X l E ≅
      ((integralDetailedTransport X l E).prod (integralDetailedTransport X l E)) ⋙
        wfOrdinaryDerivedTensor X (pbcIntegralDatum l E)) : Prop :=
  ∀ P Q : (proEtaleFlatRepresentatives X
        (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory,
        (integralDetailedTransport X l E).map (T.representative.hom.app (P, Q)) ≫
          e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (wfOrdinaryDerivedTensor X (pbcIntegralDatum l E)).map
            (Prod.mkHom
              ((fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app P.obj)
              ((fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (wfTensorModel X (pbcIntegralDatum l E)).representative.inv.app
            (⟨(complexTransport l E X).obj P.obj, good l E X P⟩,
              ⟨(complexTransport l E X).obj Q.obj, good l E X Q⟩) =
        (fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app
            ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map ((totalIso l E X P.obj Q.obj).hom)

attribute [local irreducible] ordinaryNormalization

/-- Ordinary coefficient transport is fixed by the signed-total representative square.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: compose the specified representative comparisons with total, and with the
exact transport factorization. The good theorem supplies the target resolving
objects. Double K-flat localization extends this square uniquely to a natural
isomorphism. Its inverse is obtained from the inverse total comparison. -/
theorem ordinary_existsUnique
    (T : ProEtaleTensorModel X (completedIntegralCommRingSheafUnrestricted l E X)) :
    ∃! e : T.tensor ⋙ integralDetailedTransport X l E ≅
        ((integralDetailedTransport X l E).prod (integralDetailedTransport X l E)) ⋙
          wfOrdinaryDerivedTensor X (pbcIntegralDatum l E),
      ordinaryNormalization l E X T e := by
  unfold ordinaryNormalization
  let P := proEtaleFlatRepresentatives X (completedIntegralCommRingSheafUnrestricted l E X)
  let S := proEtaleFlatRepresentatives X (pbcAdicCompletion X (pbcIntegralDatum l E))
  let q := P.ι ⋙ DerivedCategory.Q
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage P.ι
  have : q.IsLocalization V := goodComplexes_isLocalization
    (completedIntegralCommRingSheafUnrestricted l E X) P (by
      intro K
      exact and_congr
        (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).symm Iff.rfl)
  let ff := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (V.prod V)
    (DerivedCategory (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))))
  let eps : DerivedCategory.Q ⋙ integralDetailedTransport X l E ≅
      complexTransport l E X ⋙ DerivedCategory.Q :=
    (fdCoefficientTransport l E X).mapDerivedCategoryFactors
  exact normalizedTensorDescent
    (K := CochainComplex (integralTowerModules l E X) ℤ)
    (H := CochainComplex
      (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ)
    (D := DerivedCategory (integralTowerModules l E X))
    (E := DerivedCategory (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))))
    DerivedCategory.Q DerivedCategory.Q (complexTransport l E X)
    (integralDetailedTransport X l E)
    eps P S
    (fun K hK ↦ good l E X ⟨K, hK⟩) ff
    (constructibleTensorTotal l E X)
    (Functor.uncurry.obj
      ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map₂CochainComplex))
    T.tensor (wfOrdinaryDerivedTensor X (pbcIntegralDatum l E))
    T.representative (wfTensorModel X (pbcIntegralDatum l E)).representative
    (fun K ↦ totalIso l E X K.1 K.2)
    (fun f ↦ totalIso_naturality l E X f.1 f.2)

/-- Every normalized tensor-completion presentation has invertible comparison
on constructible pairs. This is the actual completion unit, not an assumption.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: the presentation's representative square and its two chain coordinates
identify chi with the quotient-map completion unit. Constructible tensor
completion makes that unit invertible, and tensor descent identifies its
ordinary tensor presentation with the presentation used there. -/
theorem completion_isIso (t : OpenFactorCoherence.Tensor l E X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [∀ x : X, Invertible (l : X.residueField x)]
    (M N : sfIntegralConstructibleCategory l E X) :
    IsIso ((t.chi l E).app (M.obj, N.obj)) := by
  exact ProjectionTensorModelComparison.completion_isIso l E X t M N

/-- The representative-normalized ordinary derived comparison.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def ordinaryComparison
    (T : ProEtaleTensorModel X (completedIntegralCommRingSheafUnrestricted l E X)) :
    T.tensor ⋙ integralDetailedTransport X l E ≅
      ((integralDetailedTransport X l E).prod (integralDetailedTransport X l E)) ⋙
        wfOrdinaryDerivedTensor X (pbcIntegralDatum l E) :=
  (ordinary_existsUnique l E X T).exists.choose

attribute [local implicit_reducible] PurCompactSupport.completed

private theorem model_transport (t s : OpenFactorCoherence.Tensor l E X)
    (e : t.ordinary.tensor ≅ s.ordinary.tensor)
    (he : ∀ P Q : (proEtaleFlatRepresentatives X
        (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory,
      t.ordinary.representative.hom.app (P, Q) ≫
        e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      s.ordinary.representative.hom.app (P, Q)) :
    Functor.isoWhiskerRight e (integralDetailedTransport X l E) ≪≫
      ordinaryComparison l E X s.ordinary = ordinaryComparison l E X t.ordinary := by
  apply (ordinary_existsUnique l E X t.ordinary).unique
  · unfold ordinaryNormalization
    intro P Q
    have h : ordinaryNormalization l E X s.ordinary (ordinaryComparison l E X s.ordinary) :=
      (ordinary_existsUnique l E X s.ordinary).exists.choose_spec
    unfold ordinaryNormalization at h
    specialize h P Q
    change (integralDetailedTransport X l E).map
      (t.ordinary.representative.hom.app (P, Q)) ≫
      ((integralDetailedTransport X l E).map
        (e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
      (ordinaryComparison l E X s.ordinary).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫ _ = _
    exact ProjectionTensorNormalization.transported_square (integralDetailedTransport X l E)
      _ _ _ _ _ _ (he P Q) h
  · exact (ordinary_existsUnique l E X t.ordinary).exists.choose_spec

end WeilConjectures.ProjectionTensorCoefficient

namespace WeilConjectures.CompactSupportCoefficientTensor
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
  (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
  (F : FdCoefficientComparisonSystem.{u} C.l C.Qbar)
  (W : FdFrobeniusComparison C.l C.Qbar D C.different F T₀)

/-- The recorded integral coefficient equivalence at this field and scheme.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def integral :=
  letI := W.noetherian
  letI := W.dimension
  letI := W.invertible
  ((F.coefficients (D.geometricFiber T₀).left).stage E₀).integral.functor

/-- The recorded rational coefficient equivalence at this field and scheme.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def rational :=
  letI := W.noetherian
  letI := W.dimension
  letI := W.invertible
  ((F.coefficients (D.geometricFiber T₀).left).stage E₀).rational.functor

/-- Integral completed tensor in the framework convention.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def integralTensor :=
  letI := sfWeilPrimeInvertible D C.l C.different T₀
  constructibleIntegralTensor C.l (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left

/-- Rational tensor in the framework convention.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def rationalTensor :=
  letI := sfWeilPrimeInvertible D C.l C.different T₀
  rationalDerivedTensor C.l (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left

/-- The coefficient tensor map on integral objects: inverse quotient-completion
unit, followed by the representative-normalized ordinary coefficient comparison.
Its underlying map is prescribed, not merely asserted to be invertible.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def integralArrow
    (t : OpenFactorCoherence.Tensor C.l (pbcFiniteField C.l C.Qbar E₀)
      (D.geometricFiber T₀).left)
    (M N : sfIntegralConstructibleCategory C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left) :=
  letI := sfWeilPrimeInvertible D C.l C.different T₀
  (integralDetailedTransport (D.geometricFiber T₀).left C.l
    (pbcFiniteField C.l C.Qbar E₀)).map
      (@asIso _ _ _ _
        ((t.chi C.l (pbcFiniteField C.l C.Qbar E₀)).app (M.obj, N.obj))
        (ProjectionTensorCoefficient.completion_isIso C.l (pbcFiniteField C.l C.Qbar E₀)
          (D.geometricFiber T₀).left t M N)).inv ≫
    (ProjectionTensorCoefficient.ordinaryComparison C.l (pbcFiniteField C.l C.Qbar E₀)
      (D.geometricFiber T₀).left t.ordinary).hom.app (M.obj, N.obj)

private theorem inverse_compare {A : Type*} [Category* A]
    {B : Type*} [Category* B] (H : A ⥤ B)
    {U V Z : A} {T : B} (f : U ≅ Z) (g : V ≅ Z)
    (e : U ≅ V) (h : e.hom ≫ g.hom = f.hom)
    (k : H.obj U ⟶ T) (m : H.obj V ⟶ T) (hk : H.map e.hom ≫ m = k) :
    H.map f.inv ≫ k = H.map g.inv ≫ m := by
  have hc : f.hom ≫ g.inv = e.hom := by rw [← h]; simp
  apply (cancel_epi (H.map f.hom)).mp
  calc
    H.map f.hom ≫ (H.map f.inv ≫ k) = k := by
      rw [← Category.assoc, ← H.map_comp, f.hom_inv_id, H.map_id, Category.id_comp]
    _ = H.map f.hom ≫ (H.map g.inv ≫ m) := by
      rw [← Category.assoc, ← H.map_comp, hc]
      exact hk.symm

private theorem integralArrow_independent
    (t s : OpenFactorCoherence.Tensor C.l (pbcFiniteField C.l C.Qbar E₀)
      (D.geometricFiber T₀).left)
    (M N : sfIntegralConstructibleCategory C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left) :
    integralArrow D C T₀ E₀ t M N = integralArrow D C T₀ E₀ s M N := by
  have := sfWeilPrimeInvertible D C.l C.different T₀
  obtain ⟨e, he, hc⟩ := ProjectionTensorModelComparison.models_comparison C.l
    (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left t s
  have h := ProjectionTensorCoefficient.model_transport C.l
    (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left t s e he
  have hk := congrArg (fun i ↦ i.hom.app (M.obj, N.obj)) h
  let ft := @asIso _ _ _ _ ((t.chi C.l _).app (M.obj, N.obj))
    (ProjectionTensorCoefficient.completion_isIso C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left t M N)
  let fs := @asIso _ _ _ _ ((s.chi C.l _).app (M.obj, N.obj))
    (ProjectionTensorCoefficient.completion_isIso C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left s M N)
  exact inverse_compare (integralDetailedTransport (D.geometricFiber T₀).left C.l
    (pbcFiniteField C.l C.Qbar E₀)) ft fs
    (e.app (M.obj, N.obj)) (congr_app hc (M.obj, N.obj)) _ _ hk

private theorem transported_hom_heq {A : Type*} [Category* A]
    {U V U' V' : A} (hu : U = U') (hv : V = V') (e : U' ≅ V') :
    HEq (eqToIso hu ≪≫ e ≪≫ (eqToIso hv).symm).hom e.hom := by
  subst U'; subst V'
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  rfl

/-- The full integral lift of the specified underlying coefficient tensor arrow.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: integral_identity fixes the underlying objects and maps of the coefficient
equivalence. Thus integralArrow has these endpoints after those equalities.
Constructible fullness lifts it and its inverse. Each normalized tensor model
gives the same arrow: the representative comparison cancels its own completion
unit, while the chain normalization fixes both Roos coordinates. Such a model
exists by the tensor-completion theorem and K-flat descent, so the universal
normalization is nonvacuous and faithfulness makes its lift unique. -/
theorem integral_existsUnique
    (M N : sfIntegralConstructibleCategory C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left) :
    ∃! e : (integral D C T₀ E₀ F W).obj ((integralTensor D C T₀ E₀).obj (M, N)) ≅
        (WfTensorCompletion.ordinary D C T₀ E₀).obj
          ((integral D C T₀ E₀ F W).obj M, (integral D C T₀ E₀ F W).obj N),
      ∀ t : OpenFactorCoherence.Tensor C.l (pbcFiniteField C.l C.Qbar E₀)
        (D.geometricFiber T₀).left,
        HEq e.hom.hom (integralArrow D C T₀ E₀ t M N) := by
  classical
  have := W.noetherian
  have := W.dimension
  have := W.invertible
  have := sfWeilPrimeInvertible D C.l C.different T₀
  obtain ⟨t⟩ := OpenFactorCoherence.tensorCompletionModel_nonempty C.l
    (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left
  let J := integralDetailedTransport (D.geometricFiber T₀).left C.l
    (pbcFiniteField C.l C.Qbar E₀)
  have ho (K : sfIntegralConstructibleCategory C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left) :
      ((integral D C T₀ E₀ F W).obj K).obj = J.obj K.obj := by
    exact congrArg (fun G ↦ G.obj K)
      (((F.coefficients (D.geometricFiber T₀).left).stage E₀).integral_identity)
  let A := (integral D C T₀ E₀ F W).obj ((integralTensor D C T₀ E₀).obj (M, N))
  let B := (WfTensorCompletion.ordinary D C T₀ E₀).obj
    ((integral D C T₀ E₀ F W).obj M, (integral D C T₀ E₀ F W).obj N)
  have ha : A.obj = J.obj ((integralCompletedTensor C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left).obj (M.obj, N.obj)) :=
    ho ((integralTensor D C T₀ E₀).obj (M, N))
  have hb : B.obj = (wfOrdinaryDerivedTensor (D.geometricFiber T₀).left
      (pbcStageDatum C.l C.Qbar E₀)).obj (J.obj M.obj, J.obj N.obj) := by
    change (wfOrdinaryDerivedTensor _ _).obj
      (((integral D C T₀ E₀ F W).obj M).obj,
        ((integral D C T₀ E₀ F W).obj N).obj) = _
    rw [ho M, ho N]
  let chiIso := @asIso _ _ _ _ ((t.chi C.l _).app (M.obj, N.obj))
    (ProjectionTensorCoefficient.completion_isIso C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left t M N)
  let a := J.mapIso chiIso.symm ≪≫
    (ProjectionTensorCoefficient.ordinaryComparison C.l (pbcFiniteField C.l C.Qbar E₀)
      (D.geometricFiber T₀).left t.ordinary).app (M.obj, N.obj)
  let e : A ≅ B := ObjectProperty.isoMk _ (eqToIso ha ≪≫ a ≪≫ (eqToIso hb).symm)
  have hn (s : OpenFactorCoherence.Tensor C.l (pbcFiniteField C.l C.Qbar E₀)
      (D.geometricFiber T₀).left) : HEq e.hom.hom (integralArrow D C T₀ E₀ s M N) := by
    exact (transported_hom_heq ha hb a).trans
      (heq_of_eq (integralArrow_independent D C T₀ E₀ t s M N))
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact eq_of_heq ((he' t).trans (hn t).symm)

/-- The integral comparison selected only from its uniquely prescribed arrow.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def integralComparison
    (M N : sfIntegralConstructibleCategory C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left) :=
  (integral_existsUnique D C T₀ E₀ F W M N).exists.choose

private theorem naturality_of_heq {A B : Type*} [Category* A] [Category* B]
    {F G F' G' : A ⥤ B} (hf : F = F') (hg : G = G')
    (a : ∀ X, F.obj X ⟶ G.obj X) (b : F' ⟶ G')
    (h : ∀ X, HEq (a X) (b.app X)) :
    ∀ {X Y} (f : X ⟶ Y), F.map f ≫ a Y = a X ≫ G.map f := by
  subst F'; subst G'
  have ha : a = b.app := funext (fun X ↦ eq_of_heq (h X))
  subst a
  exact b.naturality

private theorem integralComparison_naturality
    {M M' N N' : sfIntegralConstructibleCategory C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left}
    (f : M ⟶ M') (g : N ⟶ N') :
    (integral D C T₀ E₀ F W).map ((integralTensor D C T₀ E₀).map (Prod.mkHom f g)) ≫
        (integralComparison D C T₀ E₀ F W M' N').hom =
      (integralComparison D C T₀ E₀ F W M N).hom ≫
        (WfTensorCompletion.ordinary D C T₀ E₀).map
          (Prod.mkHom ((integral D C T₀ E₀ F W).map f)
            ((integral D C T₀ E₀ F W).map g)) := by
  have := W.noetherian
  have := W.dimension
  have := W.invertible
  let := sfWeilPrimeInvertible D C.l C.different T₀
  let X := (D.geometricFiber T₀).left
  let K := pbcFiniteField C.l C.Qbar E₀
  obtain ⟨t⟩ := OpenFactorCoherence.tensorCompletionModel_nonempty C.l K X
  let I := (sfIntegralConstructible C.l K X).ι
  let P := I.prod I
  let J := integralDetailedTransport X C.l K
  let c := Functor.whiskerLeft P (t.chi C.l K)
  have (Z : sfIntegralConstructibleCategory C.l K X ×
      sfIntegralConstructibleCategory C.l K X) : IsIso (c.app Z) :=
    ProjectionTensorCoefficient.completion_isIso C.l K X t Z.1 Z.2
  let ci := NatIso.ofComponents (fun Z ↦ asIso (c.app Z))
    (fun f ↦ c.naturality f)
  let b := Functor.isoWhiskerRight ci.symm J ≪≫
    Functor.isoWhiskerLeft P
      (ProjectionTensorCoefficient.ordinaryComparison C.l K X t.ordinary)
  let U := integralTensor D C T₀ E₀ ⋙ integral D C T₀ E₀ F W
  let V := ((integral D C T₀ E₀ F W).prod (integral D C T₀ E₀ F W)) ⋙
    WfTensorCompletion.ordinary D C T₀ E₀
  let L := pbcStageInclusion C.l C.Qbar X E₀
  have hj : integral D C T₀ E₀ F W ⋙ L = I ⋙ J :=
    ((F.coefficients X).stage E₀).integral_identity
  have hu : U ⋙ L = (P ⋙ integralCompletedTensor C.l K X) ⋙ J := by
    change integralTensor D C T₀ E₀ ⋙ (integral D C T₀ E₀ F W ⋙ L) = _
    rw [hj]
    rfl
  have hv : V ⋙ L = P ⋙ ((J.prod J) ⋙ wfOrdinaryDerivedTensor X
      (pbcIntegralDatum C.l K)) := by
    change ((integral D C T₀ E₀ F W ⋙ L).prod
      (integral D C T₀ E₀ F W ⋙ L)) ⋙ wfOrdinaryDerivedTensor X
        (pbcIntegralDatum C.l K) = _
    rw [hj]
    rfl
  have hn := naturality_of_heq hu hv
    (fun Z ↦ L.map (integralComparison D C T₀ E₀ F W Z.1 Z.2).hom) b.hom
    (fun Z ↦ (integral_existsUnique D C T₀ E₀ F W Z.1 Z.2).exists.choose_spec t)
    (Prod.mkHom f g)
  apply L.map_injective
  simp only [Functor.map_comp]
  exact hn

/-- The integral-representative square specifying the rational comparison.
Source: projection-formula proof step 13
(blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def rationalNormalization
    (R : WfTensorCompletion.RationalComparison D C T₀ E₀)
    (e : rationalTensor D C T₀ E₀ ⋙ rational D C T₀ E₀ F W ≅
      ((rational D C T₀ E₀ F W).prod (rational D C T₀ E₀ F W)) ⋙ R.ordinary) : Prop :=
  ∀ M N : sfIntegralConstructibleCategory C.l
        (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left,
        HEq (e.hom.app
          ((sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
            (D.geometricFiber T₀).left).obj M,
            (sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
              (D.geometricFiber T₀).left).obj N))
          ((pbcStageLocalization C.l C.Qbar (D.geometricFiber T₀).left E₀).map
            (integralComparison D C T₀ E₀ F W M N).hom)

attribute [local irreducible] rationalNormalization

/-- Rational tensor compatibility retains the canonical integral comparison on
every unchanged integral representative. Bilinearity fixes every denominator.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: localize integralComparison and its inverse. The integral_identity,
objects and tensors fields of the coefficient comparison identify the localized
endpoints and maps. The normalization of R.ordinary does the same for the tensor.
Naturality on integral maps extends by bilinearity to all localized maps.
All rational objects are unchanged integral representatives, giving uniqueness. -/
theorem rational_existsUnique
    (R : WfTensorCompletion.RationalComparison D C T₀ E₀)
    (hR : R.Normalized D C T₀ E₀) :
    ∃! e : rationalTensor D C T₀ E₀ ⋙ rational D C T₀ E₀ F W ≅
        ((rational D C T₀ E₀ F W).prod (rational D C T₀ E₀ F W)) ⋙ R.ordinary,
      rationalNormalization D C T₀ E₀ F W R e := by
  have := W.noetherian
  have := W.dimension
  have := W.invertible
  let := sfWeilPrimeInvertible D C.l C.different T₀
  let mu : integralTensor D C T₀ E₀ ⋙ integral D C T₀ E₀ F W ≅
      ((integral D C T₀ E₀ F W).prod (integral D C T₀ E₀ F W)) ⋙
        WfTensorCompletion.ordinary D C T₀ E₀ := NatIso.ofComponents
    (fun Z ↦ integralComparison D C T₀ E₀ F W Z.1 Z.2)
    (fun f ↦ integralComparison_naturality D C T₀ E₀ F W f.1 f.2)
  unfold rationalNormalization
  exact rationalTensorDescent D C T₀ E₀
    ((F.coefficients (D.geometricFiber T₀).left).stage E₀) R hR mu

/-- The rational coefficient tensor comparison with its integral normalization.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def comparison
    (R : WfTensorCompletion.RationalComparison D C T₀ E₀)
    (hR : R.Normalized D C T₀ E₀) :
    rationalTensor D C T₀ E₀ ⋙ rational D C T₀ E₀ F W ≅
      ((rational D C T₀ E₀ F W).prod (rational D C T₀ E₀ F W)) ⋙ R.ordinary :=
  (rational_existsUnique D C T₀ E₀ F W R hR).exists.choose

end WeilConjectures.CompactSupportCoefficientTensor
