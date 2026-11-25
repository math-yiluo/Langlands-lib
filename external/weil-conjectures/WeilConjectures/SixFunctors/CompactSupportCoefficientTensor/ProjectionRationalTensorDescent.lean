/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.SixFunctors.WfTensorCompletion.WfTensorCompletionFrobenius
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import Mathlib.CategoryTheory.Localization.Prod

/-! # Descent of integral coefficient tensor comparisons

Source: the coefficient comparison in projection-formula proof step 13.
(blueprint: lem-sf-projection-rational-tensor-descent).
An integral natural isomorphism descends through the recorded coefficient and tensor
localizations. Fully faithful precomposition fixes its action on every rational morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportCoefficientTensor

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  Padic.coefficientExtensionIntegers integralCompletedTensor constructibleIntegralTensor
  sfIntegralConstructibleLinear ObjectProperty.FullSubcategory.category
  Preadditive.fullSubcategory Linear.fullSubcategory rationalDerivedTensor
  Linear.homModule Preadditive.homGroup

private theorem transported_hom_heq {A : Type*} [Category* A]
    {U V U' V' : A} (hu : U = U') (hv : V = V') (e : U' ≅ V') :
    HEq (eqToIso hu ≪≫ e ≪≫ (eqToIso hv).symm).hom e.hom := by
  subst U'; subst V'
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  rfl

private theorem naturality_of_heq {A B : Type*} [Category* A] [Category* B]
    {F G F' G' : A ⥤ B} (hf : F = F') (hg : G = G')
    (a : ∀ X, F.obj X ⟶ G.obj X) (b : F' ⟶ G')
    (h : ∀ X, HEq (a X) (b.app X)) :
    ∀ {X Y} (f : X ⟶ Y), F.map f ≫ a Y = a X ≫ G.map f := by
  subst F'; subst G'
  have ha : a = b.app := funext (fun X ↦ eq_of_heq (h X))
  subst a
  exact b.naturality

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
  (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
  [IsNoetherian (D.geometricFiber T₀).left]
  [Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber T₀).left ≤ n)]
  [Fact (∀ x : (D.geometricFiber T₀).left,
    IsUnit (C.l : (D.geometricFiber T₀).left.presheaf.stalk x))]
  (S : FdRationalStageComparison C.l C.Qbar (D.geometricFiber T₀).left E₀)

/-- Any integral coefficient tensor natural isomorphism has a unique rational descent.
Source: projection-formula proof step 13, integral-to-rational coefficient comparison
(blueprint: lem-sf-projection-rational-tensor-descent).
Proof: the object and pure-tensor equations of S identify its restriction along source
localization with its integral functor followed by target localization. The bilinear
specification of rationalDerivedTensor gives the corresponding equality for tensor;
R.Normalized gives it for the target tensor. Transport the localization of mu along
these equalities. Source localization is a categorical localization, and its product
has fully faithful precomposition, so this integral natural isomorphism lifts to a
rational natural isomorphism. The preimage equation gives the prescribed components.
Every rational object is an unchanged integral object; their prescribed components
therefore determine the natural isomorphism uniquely. -/
theorem rationalTensorDescent
    (R : WfTensorCompletion.RationalComparison D C T₀ E₀)
    (hR : R.Normalized D C T₀ E₀)
    (mu :
      (letI := sfWeilPrimeInvertible D C.l C.different T₀
       constructibleIntegralTensor C.l (pbcFiniteField C.l C.Qbar E₀)
         (D.geometricFiber T₀).left) ⋙ S.integral.functor ≅
      (S.integral.functor.prod S.integral.functor) ⋙
        WfTensorCompletion.ordinary D C T₀ E₀) :
    ∃! d :
      (letI := sfWeilPrimeInvertible D C.l C.different T₀
       rationalDerivedTensor C.l (pbcFiniteField C.l C.Qbar E₀)
         (D.geometricFiber T₀).left) ⋙ S.rational.functor ≅
        (S.rational.functor.prod S.rational.functor) ⋙ R.ordinary,
      ∀ M N : sfIntegralConstructibleCategory C.l (pbcFiniteField C.l C.Qbar E₀)
          (D.geometricFiber T₀).left,
        HEq (d.hom.app
          ((sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
              (D.geometricFiber T₀).left).obj M,
            (sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
              (D.geometricFiber T₀).left).obj N))
          ((pbcStageLocalization C.l C.Qbar (D.geometricFiber T₀).left E₀).map
            (mu.hom.app (M, N))) := by
  classical
  let := sfWeilPrimeInvertible D C.l C.different T₀
  let X := (D.geometricFiber T₀).left
  let K := pbcFiniteField C.l C.Qbar E₀
  let J := S.integral.functor
  let H := S.rational.functor
  let A := rationalDerivedTensor C.l K X ⋙ H
  let B := (H.prod H) ⋙ R.ordinary
  let Q := pbcStageLocalization C.l C.Qbar X E₀
  have ho (M : sfRationalConstructibleCategory C.l K X) :
      H.obj M = Q.obj (J.obj M.obj) := by
    exact S.objects M
  have ht (M N : sfRationalConstructibleCategory C.l K X) :
      (rationalDerivedTensor C.l K X).obj (M, N) =
        ⟨(constructibleIntegralTensor C.l K X).obj (M.obj, N.obj)⟩ := by
    exact (rationalTensor_spec C.l K X).1 (M, N)
  have ha (M N : sfRationalConstructibleCategory C.l K X) :
      A.obj (M, N) = Q.obj (J.obj
        ((constructibleIntegralTensor C.l K X).obj (M.obj, N.obj))) := by
    change H.obj ((rationalDerivedTensor C.l K X).obj (M, N)) = _
    rw [ht M N]
    exact ho _
  have hb (M N : sfRationalConstructibleCategory C.l K X) :
      B.obj (M, N) = Q.obj ((WfTensorCompletion.ordinary D C T₀ E₀).obj
        (J.obj M.obj, J.obj N.obj)) := by
    change R.ordinary.obj (H.obj M, H.obj N) = _
    rw [ho M, ho N]
    exact congrArg (fun T ↦ T.obj (J.obj M.obj, J.obj N.obj)) hR.1
  let e (Z : sfRationalConstructibleCategory C.l K X ×
      sfRationalConstructibleCategory C.l K X) : A.obj Z ≅ B.obj Z :=
    eqToIso (ha Z.1 Z.2) ≪≫
      Q.mapIso (mu.app (Z.1.obj, Z.2.obj)) ≪≫
      (eqToIso (hb Z.1 Z.2)).symm
  have he (M N : sfIntegralConstructibleCategory C.l K X) :
      HEq (e (⟨M⟩, ⟨N⟩)).hom
        (Q.map (mu.app (M, N)).hom) := by
    exact transported_hom_heq (ha ⟨M⟩ ⟨N⟩) (hb ⟨M⟩ ⟨N⟩) _
  let q := sfRationalConstructibleLocalization C.l K X
  have hH : q ⋙ H = J ⋙ Q := by
    apply Functor.hext (fun M ↦ ho ⟨M⟩)
    intro M N f
    have hs := S.tensors M N 1 f
    simp only [fdRawTensor, map_one] at hs
    exact hs
  have hT : (q.prod q) ⋙ rationalDerivedTensor C.l K X =
      constructibleIntegralTensor C.l K X ⋙ q := by
    apply Functor.hext (fun Z ↦ ht ⟨Z.1⟩ ⟨Z.2⟩)
    intro Y Z f
    obtain ⟨β, hβ, pβ⟩ := (rationalTensor_spec C.l K X).2
      (q.obj Y.1) (q.obj Z.1) (q.obj Y.2) (q.obj Z.2)
    change HEq ((rationalDerivedTensor C.l K X).map
      (Prod.mkHom (q.map f.1) (q.map f.2))) _
    rw [hβ]
    have hs := pβ f.1 f.2 1 1
    simp only [one_mul] at hs
    exact hs
  let U := constructibleIntegralTensor C.l K X ⋙ J
  let V := (J.prod J) ⋙ WfTensorCompletion.ordinary D C T₀ E₀
  have hA : (q.prod q) ⋙ A = U ⋙ Q := by
    change ((q.prod q) ⋙ rationalDerivedTensor C.l K X) ⋙ H = _
    rw [hT]
    change constructibleIntegralTensor C.l K X ⋙ (q ⋙ H) = _
    rw [hH]
    rfl
  have hB : (q.prod q) ⋙ B = V ⋙ Q := by
    change ((q ⋙ H).prod (q ⋙ H)) ⋙ R.ordinary = _
    rw [hH]
    change (J.prod J) ⋙ ((Q.prod Q) ⋙ R.ordinary) = _
    rw [hR.1]
    rfl
  let eta : (q.prod q) ⋙ A ≅ (q.prod q) ⋙ B := NatIso.ofComponents
    (fun Z ↦ e ((q.prod q).obj Z))
    (naturality_of_heq hA hB (fun Z ↦ (e ((q.prod q).obj Z)).hom)
      (Functor.isoWhiskerRight mu Q).hom (fun Z ↦ he Z.1 Z.2))
  let R₀ := Padic.coefficientExtensionIntegers C.l K
  let p := Padic.coefficientExtensionUniformizer C.l K
  let S₀ := sfIntegralConstructibleCategory C.l K X
  let V₀ := Rationalization.W (Submonoid.powers p) S₀
  have : q.IsLocalization V₀ :=
    ScalarLocalization.semilinear_localization_isLocalization R₀ S₀ p
  let ff := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (V₀.prod V₀)
    (pbcStageCategory C.l C.Qbar X E₀)
  let d : A ≅ B := ff.preimageIso eta
  have hd (M N : sfIntegralConstructibleCategory C.l K X) :
      HEq (d.hom.app (q.obj M, q.obj N))
        (Q.map (mu.app (M, N)).hom) := by
    exact (heq_of_eq (congr_app (ff.map_preimage eta.hom) (M, N))).trans (he M N)
  refine ⟨d, ?_, ?_⟩
  · exact hd
  · intro d' hd'
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    exact eq_of_heq ((hd' Z.1.obj Z.2.obj).trans (hd Z.1.obj Z.2.obj).symm)

end WeilConjectures.CompactSupportCoefficientTensor
