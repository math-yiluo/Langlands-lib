/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionCoefficientTransport.RationalProjectionTensorCompatibility
public import WeilConjectures.SixFunctors.ProjectionCoefficientTransport.ProjectionMateFactors
public import WeilConjectures.SixFunctors.Common.CommonProjectionTensorComparison
import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackTensorCompatibility

/-! # Common-stage preservation of a projection factor

Source: thm-sf-pf-field.proof.md, Compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
open ProjectionCoefficientTransport

private theorem transportProjectionMate
    {A B : Type*} [Category* A] [Category* B]
    {F F' : A ⥤ B} {G G' : B ⥤ A}
    {T T' : B ⥤ B ⥤ B} {U U' : A ⥤ A ⥤ A}
    (hF : F = F') (hG : G = G') (hT : T = T') (hU : U = U')
    (adj : F ⊣ G) (adj' : F' ⊣ G') (hadj : HEq adj adj')
    (φ : (Functor.postcompose₂.obj F).obj U ≅
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T) (M : B) (N : A) :
    HEq (((adj.rightAdjointProjectionMap φ.hom).app M).app N)
      (((adj'.rightAdjointProjectionMap
        (projectionTransportTensorComparison hF hT hU φ).hom).app M).app N) := by
  subst F'
  subst G'
  subst T'
  subst U'
  cases eq_of_heq hadj
  rfl

private theorem iso_app_hom_heq
    {A B : Type*} [Category* A] [Category* B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G')
    (e : F ≅ G) (e' : F' ≅ G') (he : HEq e e') (K : A) :
    HEq (e.hom.app K) (e'.hom.app K) := by
  subst F'
  subst G'
  cases eq_of_heq he
  rfl

private theorem tensor_map_heq
    {A : Type*} [Category* A] {T T' : A ⥤ A ⥤ A} (hT : T = T')
    {X Y X' Y' : A} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (f' : X' ⟶ Y') (hf : HEq f f') (N : A) :
    HEq ((T.map f).app N) ((T'.map f').app N) := by
  subst T'
  subst X'
  subst Y'
  cases eq_of_heq hf
  rfl

private theorem comp_heq
    {A : Type*} [Category* A] {X Y Z X' Y' Z' : A}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst X'
  subst Y'
  subst Z'
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

private theorem transport_hom_eq
    {A : Type*} [Category* A] {X Y X' Y' : A}
    (hX : X = X') (hY : Y = Y')
    (f : X' ⟶ Y') (g : X ⟶ Y) (h : HEq f g) :
    eqToHom hX ≫ f ≫ eqToHom hY.symm = g := by
  subst X'
  subst Y'
  simpa using eq_of_heq h

private theorem properFactor_normalized
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q)
    (K : B Q.X) (N : B Q.Y) :
    properFactor A K N =
      ((T Q.Y).map
        ((sixFunctorFactoredSupportIdentification S Q.i Q.p Q.open_i Q.proper_p
          Q.f Q.factorization).hom.app K)).app N ≫
      (((S.pullDirectAdjunction Q.p).rightAdjointProjectionMap
        (projectionPullbackTensor A).hom).app ((S.openExtension Q.i Q.open_i).obj K)).app
          N := by
  have hraw := transportProjectionMate A.properPull A.properPush A.tensorBar A.tensorY
    A.stage.properAdjunction (S.pullDirectAdjunction Q.p) A.properAdjunction
    A.stage.tensorPullback (A.stage.openExtension.obj K) N
  have hm : HEq
      (((A.stage.properAdjunction.rightAdjointProjectionMap
        A.stage.tensorPullback.hom).app (A.stage.openExtension.obj K)).app N)
      ((((S.pullDirectAdjunction Q.p).rightAdjointProjectionMap
        (projectionPullbackTensor A).hom).app (A.stage.openExtension.obj K)).app N) := by
    simpa only [projectionPullbackTensor] using hraw
  have hi := iso_app_hom_heq A.compactSupport
    (congrArg₂ (· ⋙ ·) A.openExtension A.properPush)
    A.stage.compactSupportIdentification
    (sixFunctorFactoredSupportIdentification S Q.i Q.p Q.open_i Q.proper_p
      Q.f Q.factorization) A.compactSupportNormalization K
  have ht := tensor_map_heq A.tensorY
    (congrArg (fun F ↦ F.obj K) A.compactSupport)
    (congrArg (fun F ↦ F.obj K)
      (congrArg₂ (· ⋙ ·) A.openExtension A.properPush))
    _ _ hi N
  have hmo : HEq
      (((S.pullDirectAdjunction Q.p).rightAdjointProjectionMap
        (projectionPullbackTensor A).hom).app (A.stage.openExtension.obj K) |>.app N)
      (((S.pullDirectAdjunction Q.p).rightAdjointProjectionMap
        (projectionPullbackTensor A).hom).app
          ((S.openExtension Q.i Q.open_i).obj K) |>.app N) := by
    rw [A.openExtension]
  have he := comp_heq (by rw [A.tensorY, A.compactSupport])
    (by rw [A.tensorY, A.properPush, A.openExtension])
    (middle_eq A K N).symm ht (hm.trans hmo)
  unfold properFactor
  simpa only [Category.assoc, SixFunctorCompactifiedSquare.compactification,
    sixFunctorFactorCompactification, middleObject] using
    transport_hom_eq (by rw [A.tensorY, A.compactSupport]) (middle_eq A K N) _ _ he

private theorem adjunctionComparison_mate
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    {adj : F ⊣ G} {adj' : F' ⊣ G'} {V : A ⥤ A'} {W : B ⥤ B'}
    (C : CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison
      adj adj' V W) (M : B) :
    (mateEquiv adj adj' C.left.inv).app M = C.right.hom.app M := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact (mateEquiv_counit adj adj' C.left.inv M).trans (C.counit M).symm

private theorem properMate_preserved
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category* (B X)]
    {B' : SixFunctorSpace D → Type*} [∀ X, Category* (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (hφ : Adjunction.ComparisonCompatible (C.directAdjunction Q.p).left.symm
      (projectionPullbackTensor A).hom (projectionPullbackTensor A').hom
      (projectionCurriedTensorComparison (V Q.Z) (T Q.Z) (T' Q.Z) (t Q.Z))
      (projectionCurriedTensorComparison (V Q.Y) (T Q.Y) (T' Q.Y) (t Q.Y)))
    (M : B Q.Z) (N : B Q.Y) :
    (V Q.Y).map
        ((((S.pullDirectAdjunction Q.p).rightAdjointProjectionMap
          (projectionPullbackTensor A).hom).app M).app N) ≫
      (properTarget C t Q.p M N).hom =
    (properSource C t Q.p M N).hom ≫
      (((S'.pullDirectAdjunction Q.p).rightAdjointProjectionMap
        (projectionPullbackTensor A').hom).app ((V Q.Z).obj M)).app ((V Q.Y).obj N) := by
  have h := Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv
    (S.pullDirectAdjunction Q.p) (S'.pullDirectAdjunction Q.p) hφ M N
  simp only [Iso.symm_hom, Iso.symm_inv, adjunctionComparison_mate] at h
  simpa [properTarget, properSource, ProjectionCoefficientTransport.inner,
    projectionCurriedTensorComparison, Functor.uncurry, Category.assoc] using h

private theorem factoredSupport_preserved
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category* (B X)]
    {B' : SixFunctorSpace D → Type*} [∀ X, Category* (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
    {X Y Z : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (hi : IsOpenImmersion i.hom.left) (hp : IsProper p.hom.left)
    (f : X ⟶ Y) (h : f = i ≫ p) (K : B X) :
    (V Y).map ((sixFunctorFactoredSupportIdentification S i p hi hp f h).hom.app K) ≫
        (C.directAdjunction p).right.hom.app ((S.openExtension i hi).obj K) ≫
        (S'.direct p).map ((C.openExtension i hi).hom.app K) =
      (C.supportAdjunction f (sixFunctorFactorCompactification i p hi hp f h)).left.hom.app
          K ≫
        (sixFunctorFactoredSupportIdentification S' i p hi hp f h).hom.app
          ((V X).obj K) := by
  subst f
  let : IsProper p.hom.left := hp
  simp only [sixFunctorFactoredSupportIdentification, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (C.properIdentity p ((S.openExtension i hi).obj K))]
  rw [← (S'.properIdentity p).hom.naturality]
  have hn := (C.supportAdjunction p (.ofIsProper p.hom.left)).left.hom.naturality
    ((S.openIdentification i hi).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, C.openIdentification]
  rw [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (C.composition i p (sixFunctorOpenCompactification i hi)
    (.ofIsProper p.hom.left) (sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl) K)]
  rfl

private theorem tensor_transport_square
    {A B : Type*} [Category* A] [Category* B]
    {T : A ⥤ A ⥤ A} {T' : B ⥤ B ⥤ B} {V : A ⥤ B}
    (t : Functor.uncurry.obj T ⋙ V ≅ V.prod V ⋙ Functor.uncurry.obj T')
    {X₀ X₁ : A} {Y₀ Y₁ Z : B} (σ : X₀ ⟶ X₁)
    (a : V.obj X₁ ⟶ Y₀) (b : Y₀ ⟶ Y₁) (c : V.obj X₀ ⟶ Z) (σ' : Z ⟶ Y₁)
    (h : V.map σ ≫ a ≫ b = c ≫ σ') (N : A) :
    V.map ((T.map σ).app N) ≫ t.hom.app (X₁, N) ≫
        (T'.map a).app (V.obj N) ≫ (T'.map b).app (V.obj N) =
      t.hom.app (X₀, N) ≫ (T'.map c).app (V.obj N) ≫
        (T'.map σ').app (V.obj N) := by
  have ht := t.hom.naturality (Prod.mkHom σ (𝟙 N))
  dsimp only [Functor.comp, Functor.prod, Functor.uncurry, Prod.mkHom] at ht
  erw [(T.obj X₁).map_id N, V.map_id N,
    (T'.obj (V.obj X₁)).map_id (V.obj N), Category.comp_id, Category.comp_id] at ht
  rw [reassoc_of% ht]
  have hh := congrArg (fun f ↦ (T'.map f).app (V.obj N)) h
  simpa only [Functor.map_comp, NatTrans.comp_app, Category.assoc] using
    congrArg (fun a ↦ t.hom.app (X₀, N) ≫ a) hh

private theorem properFactor_preserved_of_tensor
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category* (B X)]
    {B' : SixFunctorSpace D → Type*} [∀ X, Category* (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q)
    (hφ : projectionTensorComparisonCompatible C t A A')
    (K : B Q.X) (N : B Q.Y) :
    (V Q.Y).map (properFactor A K N) ≫ (middle C t Q K N).hom =
      (source C t Q.f Q.compactification K N).hom ≫
        properFactor A' ((V Q.X).obj K) ((V Q.Y).obj N) := by
  dsimp only [SixFunctorCompactifiedSquare.compactification,
    sixFunctorFactorCompactification, middleObject]
  let M := (S.openExtension Q.i Q.open_i).obj K
  let e := (C.openExtension Q.i Q.open_i).hom.app K
  let π' := (S'.pullDirectAdjunction Q.p).rightAdjointProjectionMap
    (projectionPullbackTensor A').hom
  have hn :
      ((T' Q.Y).map ((S'.direct Q.p).map e)).app ((V Q.Y).obj N) ≫
          (π'.app ((S'.openExtension Q.i Q.open_i).obj ((V Q.X).obj K))).app
            ((V Q.Y).obj N) =
        (π'.app ((V Q.Z).obj M)).app ((V Q.Y).obj N) ≫
          (S'.direct Q.p).map
            (((T' Q.Z).map e).app ((S'.pull Q.p).obj ((V Q.Y).obj N))) :=
    NatTrans.congr_app (π'.naturality e) ((V Q.Y).obj N)
  have hm : (middle C t Q K N).hom =
      (properTarget C t Q.p M N).hom ≫
        (S'.direct Q.p).map
          (((T' Q.Z).map e).app ((S'.pull Q.p).obj ((V Q.Y).obj N))) := by
    dsimp only [middle, properTarget, ProjectionCoefficientTransport.inner, middleObject,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod, Functor.uncurry_obj_map, Prod.mkHom, Iso.refl_hom, Functor.comp_obj]
    erw [(T' Q.Z).map_id ((V Q.Z).obj M), NatTrans.id_app, Category.id_comp]
    simp only [Category.assoc]
    erw [← Functor.map_comp, Category.assoc, ((T' Q.Z).map e).naturality]
    rfl
  have hs := factoredSupport_preserved C Q.i Q.p Q.open_i Q.proper_p
    Q.f Q.factorization K
  have hi :
      (V Q.Y).map
          (((T Q.Y).map
            ((sixFunctorFactoredSupportIdentification S Q.i Q.p Q.open_i Q.proper_p
              Q.f Q.factorization).hom.app K)).app N) ≫
        (properSource C t Q.p M N).hom ≫
        ((T' Q.Y).map ((S'.direct Q.p).map e)).app ((V Q.Y).obj N) =
      (source C t Q.f Q.compactification K N).hom ≫
        ((T' Q.Y).map
          ((sixFunctorFactoredSupportIdentification S' Q.i Q.p Q.open_i Q.proper_p
            Q.f Q.factorization).hom.app ((V Q.X).obj K))).app ((V Q.Y).obj N) := by
    have h := tensor_transport_square (t Q.Y) _ _ _ _ _ hs N
    have hid (P : B' Q.Y) :
        ((T' Q.Y).obj P).map (𝟙 ((V Q.Y).obj N)) = 𝟙 _ :=
      ((T' Q.Y).obj P).map_id ((V Q.Y).obj N)
    simpa only [properSource, source, Iso.trans, Iso.app, Functor.mapIso, Iso.prod,
      Iso.refl, Functor.uncurry, Functor.comp, Prod.mkHom,
      hid, Category.comp_id, Category.assoc, M, e,
      SixFunctorCompactifiedSquare.compactification, sixFunctorFactorCompactification] using h
  erw [properFactor_normalized A, Functor.map_comp, Category.assoc, hm,
    ← Category.assoc _ (properTarget C t Q.p M N).hom,
    properMate_preserved C t A A' (by
      simpa only [projectionTensorComparisonCompatible] using hφ)]
  simp only [Category.assoc]
  rw [← hn]
  have hf := congrArg (fun a ↦ a ≫
    (π'.app ((S'.openExtension Q.i Q.open_i).obj ((V Q.X).obj K))).app
      ((V Q.Y).obj N)) hi
  simpa only [properFactor_normalized, Category.assoc, π', M,
    SixFunctorCompactifiedSquare.compactification, sixFunctorFactorCompactification,
    middleObject] using hf

set_option backward.isDefEq.respectTransparency false in
/-- Finite-stage inclusion preserves the proper counit factor, including the
initial support identification, through the canonical tensorator.

Source: thm-sf-pf-field.proof.md, Compatibility, and steps 2--3 of
lem-sf-common-projection-tensor-compatibility.
(blueprint: lem-sf-common-projection-proper-factor).

Proof: identify the support functor with open extension followed by proper direct
image. The comparison for this identification is the composite of the open and
direct-image comparisons: expand sixFunctorFactoredSupportIdentification and
apply the coefficient composition, openIdentification and properIdentity laws.
Naturality of commonProjectionTensorComparison carries the initial tensor of
this identification across inclusion. It remains to compare the proper counit
mates at the open-extended input. Transpose under the prescribed pull/direct
adjunctions. Each transpose is the canonical tensor/pullback comparison followed
by the counit in the first tensor variable. The finite-representative formula
of canonicalCommonStagePullbackTensor identifies its included rational formula,
using the canonical tensorator at the target and compactifying space. The
recorded coefficient counit equation identifies the other factor. Naturality in
the open-extension comparison then gives exactly the intermediate comparison
middle. Cancel the adjunction Hom equivalence to obtain the square below.
Only the proper factor is compared; the open projection map is absent. The
argument uses the same formulas for empty schemes, zero inputs and identities. -/
theorem commonProjectionProperFactor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Q.X.obj.left E)
    (N : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Q.Y.obj.left E) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) E).map
        (properFactor ((H.coefficientStages E).rationalExchange Q) K N) ≫
        (middle (H.commonStageComparison E) (commonProjectionTensorComparison H E)
          Q K N).hom =
        (source (H.commonStageComparison E) (commonProjectionTensorComparison H E)
          Q.f Q.compactification K N).hom ≫
        properFactor (H.commonStageExchange Q)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Q.X.obj.left) E).obj K)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) E).obj N) := by
  exact properFactor_preserved_of_tensor (H.commonStageComparison E)
    (commonProjectionTensorComparison H E) ((H.coefficientStages E).rationalExchange Q)
    (H.commonStageExchange Q) (commonProjectionPullbackTensorCompatibility H E Q) K N

end WeilConjectures
