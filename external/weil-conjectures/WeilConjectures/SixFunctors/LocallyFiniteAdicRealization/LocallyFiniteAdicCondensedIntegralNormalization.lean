/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedStageData
public import WeilConjectures.SixFunctors.AdicFiniteRealization.LocallyFiniteAdicFiniteCondensedRealization
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralTransition

/-! # Integral tensor normalization for the finite condensed realization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-locally-finite-adic-condensed-integral-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
attribute [local implicit_reducible]
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
attribute [local irreducible] Sheaf.monoidalCategory
namespace WeilConjectures.LocallyFiniteAdicRealization
attribute [local irreducible] nativeCondensedDerived nativeCondensedModules
  sections CoefficientPresentation.integralMap completedTensorComparison pbcDerivedRestrict
  pbcReductionNormalization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization

private theorem mappedCancelIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (H : D ⥤ E) [H.Full] [H.Faithful] {F G : C ⥤ D} {M : C ⥤ E}
    (a : F ⋙ H ≅ M) (q : G ⋙ H ≅ M) (X : C) :
    H.map ((Functor.fullyFaithfulCancelRight H (a ≪≫ q.symm)).hom.app X) =
      a.hom.app X ≫ q.inv.app X := by
  simp only [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  rfl

private theorem assocTrans_hom_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (P : C ⥤ D) (Q : D ⥤ E) (R : E ⥤ F) {M : C ⥤ F}
    (e : P ⋙ Q ⋙ R ≅ M) (K : C) :
    (Functor.associator P Q R ≪≫ e).hom.app K = e.hom.app K := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Category.id_comp]

private theorem transported_hom_app
    {C N V W P Q : Type*} [Category C] [Category N] [Category V]
    [Category W] [Category P] [Category Q]
    (F : C ⥤ N) (G : N ⥤ V) (S : V ⥤ W) (H : N ⥤ P) (R : P ⥤ W)
    (I : C ⥤ Q) (E : Q ⥤ P) (n : G ⋙ S ≅ H ⋙ R)
    (d : F ⋙ H ≅ I ⋙ E) (K : C) :
    (Functor.associator F G S ≪≫ Functor.isoWhiskerLeft F n ≪≫
      Functor.isoWhiskerRight d R ≪≫ Functor.associator I E R).hom.app K =
        n.hom.app (F.obj K) ≫ R.map (d.hom.app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id]

private theorem rebracketed_hom_app
    {C D E F G : Type*} [Category C] [Category D] [Category E]
    [Category F] [Category G]
    (Q : C ⥤ D) (I : D ⥤ E) (J : E ⥤ F) (H : F ⥤ G)
    {M : C ⥤ G} (e : (Q ⋙ I ⋙ J) ⋙ H ≅ M) (K : C) :
    ((Functor.associator Q (I ⋙ J) H ≪≫
      Functor.isoWhiskerLeft Q (Functor.associator I J H)).symm ≪≫ e).hom.app K =
      e.hom.app K := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id]
  exact Category.id_comp _

private theorem faithfulSquare
    {C D : Type*} [Category C] [Category D] (S : C ⥤ D) [S.Faithful]
    {X Y U V : C} (g : X ⟶ Y) (f : U ⟶ V) (a : X ⟶ U) (b : Y ⟶ V)
    (a' : S.obj X ⟶ S.obj U) (b' : S.obj Y ⟶ S.obj V)
    (ha : S.map a = a') (hb : S.map b = b')
    (h : S.map g ≫ b' = a' ≫ S.map f) : g ≫ b = a ≫ f := by
  apply S.map_injective
  rw [S.map_comp, S.map_comp, ha, hb]
  exact h

private theorem regroupHEq
    {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    {Y₀ Y₁ : C} {x : Y₀ ⟶ Y₁} (h : HEq x (a ≫ b ≫ c ≫ d)) :
    HEq x (a ≫ (b ≫ c) ≫ d) := by
  simpa only [Category.assoc] using h

private theorem transportIntegralSquare
    {I N P V W : Type*} [Category I] [Category N] [Category P]
    [Category V] [Category W]
    (H : N ⥤ P) (G : N ⥤ V) (S : V ⥤ W) (R : P ⥤ W)
    (n : G ⋙ S ≅ H ⋙ R) (F : I ⥤ N) (M : I ⥤ P) (d : F ⋙ H ≅ M)
    {B C : I} (hBC : B = C) {X : N} {Y : P} (i : H.obj X ≅ Y)
    (t : Y ⟶ M.obj C) (g : X ⟶ F.obj B)
    (hg : HEq (H.map g) (i.hom ≫ t ≫ d.inv.app C)) :
    HEq (S.map (G.map g) ≫ n.hom.app (F.obj B) ≫ R.map (d.hom.app B))
      (n.hom.app X ≫ R.map i.hom ≫ R.map t) := by
  cases hBC
  have hg' := eq_of_heq hg
  apply heq_of_eq
  have hn := n.hom.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Functor.comp_map, Category.assoc]
  rw [← R.map_comp, hg']
  simp only [R.map_comp, Category.assoc, Iso.inv_hom_id_app,
    R.map_id, Category.comp_id]

private theorem tensorSquaresConjugate
    {C : Type*} [Category C] {X Y U V M N N' : C}
    (g : X ⟶ Y) (f : U ⟶ V) (a : X ≅ M) (b : Y ≅ N)
    (p : U ≅ M) (q : V ≅ N) (t : M ⟶ N') (h : N = N')
    (hg : HEq (g ≫ b.hom) (a.hom ≫ t))
    (hf : HEq (f ≫ q.hom) (p.hom ≫ t)) :
    g ≫ (b.hom ≫ q.inv) = (a.hom ≫ p.inv) ≫ f := by
  cases h
  have hg' := eq_of_heq hg
  have hf' := eq_of_heq hf
  apply (cancel_mono q.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hf']
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.comp_id] using hg'

private noncomputable def integralSectionComparison
    {I N P V W T U : Type*} [Category I] [Category N] [Category P]
    [Category V] [Category W] [Category T] [Category U]
    (F : I ⥤ N) (G : N ⥤ V) (S : V ⥤ W) [S.Full] [S.Faithful]
    (H : N ⥤ P) (R : P ⥤ W) (J : I ⥤ U) (E : U ⥤ P)
    (Q : I ⥤ T) (B : T ⥤ V) (n : G ⋙ S ≅ H ⋙ R)
    (d : F ⋙ H ≅ J ⋙ E) (q : Q ⋙ B ⋙ S ≅ J ⋙ E ⋙ R) :
    F ⋙ G ≅ Q ⋙ B :=
  let a := Functor.associator F G S ≪≫ Functor.isoWhiskerLeft F n ≪≫
    Functor.isoWhiskerRight d R ≪≫ Functor.associator J E R
  let p := Functor.associator Q B S ≪≫ q
  Functor.fullyFaithfulCancelRight S (a ≪≫ p.symm)

private theorem integralSectionComparison_transition
    {I₀ I₁ N P V W T₀ T₁ U₀ U₁ : Type*}
    [Category I₀] [Category I₁] [Category N] [Category P] [Category V]
    [Category W] [Category T₀] [Category T₁] [Category U₀] [Category U₁]
    (F₀ : I₀ ⥤ N) (F₁ : I₁ ⥤ N) (G : N ⥤ V) (S : V ⥤ W)
    [S.Full] [S.Faithful] (H : N ⥤ P) (R : P ⥤ W)
    (J₀ : I₀ ⥤ U₀) (J₁ : I₁ ⥤ U₁) (E₀ : U₀ ⥤ P) (E₁ : U₁ ⥤ P)
    (Q₀ : I₀ ⥤ T₀) (Q₁ : I₁ ⥤ T₁) (B₀ : T₀ ⥤ V) (B₁ : T₁ ⥤ V)
    (n : G ⋙ S ≅ H ⋙ R) (d₀ : F₀ ⋙ H ≅ J₀ ⋙ E₀)
    (d₁ : F₁ ⋙ H ≅ J₁ ⋙ E₁)
    (q₀ : Q₀ ⋙ B₀ ⋙ S ≅ J₀ ⋙ E₀ ⋙ R)
    (q₁ : Q₁ ⋙ B₁ ⋙ S ≅ J₁ ⋙ E₁ ⋙ R)
    (K : I₀) (L L' : I₁) (hL : L = L')
    (g : F₀.obj K ⟶ F₁.obj L)
    (f : B₀.obj (Q₀.obj K) ⟶ B₁.obj (Q₁.obj L))
    (t : E₀.obj (J₀.obj K) ⟶ E₁.obj (J₁.obj L'))
    (hd : HEq (H.map g) (d₀.hom.app K ≫ t ≫ d₁.inv.app L'))
    (hq : integralTensorSquare (S.map f) (q₀.app K) (q₁.app L) (R.map t)) :
    G.map g ≫
        (integralSectionComparison F₁ G S H R J₁ E₁ Q₁ B₁ n d₁ q₁).hom.app L =
      (integralSectionComparison F₀ G S H R J₀ E₀ Q₀ B₀ n d₀ q₀).hom.app K ≫ f := by
  let a₀ := Functor.associator F₀ G S ≪≫ Functor.isoWhiskerLeft F₀ n ≪≫
    Functor.isoWhiskerRight d₀ R ≪≫ Functor.associator J₀ E₀ R
  let a₁ := Functor.associator F₁ G S ≪≫ Functor.isoWhiskerLeft F₁ n ≪≫
    Functor.isoWhiskerRight d₁ R ≪≫ Functor.associator J₁ E₁ R
  let p₀ := Functor.associator Q₀ B₀ S ≪≫ q₀
  let p₁ := Functor.associator Q₁ B₁ S ≪≫ q₁
  apply faithfulSquare S (G.map g) f _ _
    (a₀.hom.app K ≫ p₀.inv.app K) (a₁.hom.app L ≫ p₁.inv.app L)
  · exact mappedCancelIso S a₀ p₀ K
  · exact mappedCancelIso S a₁ p₁ L
  · apply tensorSquaresConjugate _ _ (a₀.app K) (a₁.app L)
      (p₀.app K) (p₁.app L) (R.map t)
      (congrArg (fun Z ↦ R.obj (E₁.obj (J₁.obj Z))) hL)
    · have hg := transportIntegralSquare H G S R n F₁ (J₁ ⋙ E₁) d₁
        hL (d₀.app K) t g hd
      simpa only [a₀, a₁, Iso.app_hom, transported_hom_app, Category.assoc] using hg
    · simpa only [integralTensorSquare, p₀, p₁, Iso.app_hom, assocTrans_hom_app] using hq

attribute [local irreducible] integralSectionComparison

private noncomputable def normalizationIntegralComparison
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (D : NormalizedFunctor l X) (A : AdicFiniteRealization.FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l)) :
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ D.J ⋙
            nativeCondensedDerived l X ≅
        sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
          finiteCondensedClosureFunctor l X A E := by
  letI := D.commutative
  letI := D.sectionsAdditive
  letI := D.sectionsLimits
  letI := D.sectionsColimits
  let C : CoefficientSystem l X :=
    { commutative := D.commutative
      sectionsAdditive := D.sectionsAdditive
      sectionsLimits := D.sectionsLimits
      sectionsColimits := D.sectionsColimits
      coefficient := D.coefficient
      coefficient_scalar := D.coefficient_scalar }
  let R := pbcDerivedRestrict
    (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))
  let S := integralSections l X
  letI := integralSections_isEquivalence l X
  let n := nativeCondensedSectionComparison l X
  let q (E : Index l (PadicAlgCl l)) := finiteCondensedIntegralTensorModel l X A C E
  dsimp only [C] at q
  exact
    (Functor.associator
      (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X)
      (GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ D.J)
      (nativeCondensedDerived l X) ≪≫
      Functor.isoWhiskerLeft
        (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X)
        (Functor.associator (GeneralAlgebraicallyClosedCoefficients.inclusion E) D.J
          (nativeCondensedDerived l X))).symm ≪≫
    integralSectionComparison
      (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ D.J)
      (nativeCondensedDerived l X) S (sections l X).mapDerivedCategory R
      (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
      (pbcDerivedExtend ((D.coefficient E).integralMap l X))
      (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X)
      (finiteCondensedClosureFunctor l X A E) n (D.integral E)
      (q E)

private theorem nativeTensorTransition
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (D : NormalizedFunctor l X) (A : FiniteCondensedData l X) :
    letI := D.commutative
    let C : CoefficientSystem l X :=
      { commutative := D.commutative
        sectionsAdditive := D.sectionsAdditive
        sectionsLimits := D.sectionsLimits
        sectionsColimits := D.sectionsColimits
        coefficient := D.coefficient
        coefficient_scalar := D.coefficient_scalar }
    let R := pbcDerivedRestrict
      (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))
    let S := integralSections l X
    let q := finiteCondensedIntegralTensorModel l X A C
    ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      let B :=
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj
      let T := (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        E L h).obj K
      let f :
          (finiteCondensedClosureFunctor l X A E).obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) ⟶
            (finiteCondensedClosureFunctor l X A L).obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) L) X).obj B) :=
        (finiteCondensedClosureTransition l X A h).hom.app
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)
      let t :
          (pbcDerivedExtend ((D.coefficient E).integralMap l X)).obj
            ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K) ⟶
            (pbcDerivedExtend ((D.coefficient L).integralMap l X)).obj
            ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) L) X).ι.obj T) :=
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((D.coefficient L).integralMap l X) ((D.coefficient E).integralMap l X)
          (D.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((D.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h)).app
              K.obj)
      integralTensorSquare (S.map f) ((q E).app K) ((q L).app B) (R.map t) := by
  letI := D.commutative
  let C : CoefficientSystem l X :=
    { commutative := D.commutative
      sectionsAdditive := D.sectionsAdditive
      sectionsLimits := D.sectionsLimits
      sectionsColimits := D.sectionsColimits
      coefficient := D.coefficient
      coefficient_scalar := D.coefficient_scalar }
  exact finiteCondensedIntegralTensorTransition l X A C

private theorem normalizationIntegralComparison_transition
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (D : NormalizedFunctor l X) (A : AdicFiniteRealization.FiniteCondensedData l X) :
    ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
        (D.J ⋙ nativeCondensedDerived l X).map
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
              ⟨E, (sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K⟩ h).hom ≫
          (normalizationIntegralComparison l X D A L).hom.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj =
          (normalizationIntegralComparison l X D A E).hom.app K ≫
            (finiteCondensedClosureTransition l X A h).hom.app
            ((sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) := by
  letI := D.commutative
  letI := D.sectionsAdditive
  letI := D.sectionsLimits
  letI := D.sectionsColimits
  let C : CoefficientSystem l X :=
    { commutative := D.commutative
      sectionsAdditive := D.sectionsAdditive
      sectionsLimits := D.sectionsLimits
      sectionsColimits := D.sectionsColimits
      coefficient := D.coefficient
      coefficient_scalar := D.coefficient_scalar }
  let R := pbcDerivedRestrict
    (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))
  let S := integralSections l X
  letI := integralSections_isEquivalence l X
  let n := nativeCondensedSectionComparison l X
  let q (E : Index l (PadicAlgCl l)) := finiteCondensedIntegralTensorModel l X A C E
  dsimp only [C] at q
  have he (E : Index l (PadicAlgCl l))
      (Z : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
      (normalizationIntegralComparison l X D A E).hom.app Z =
        (integralSectionComparison
          (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
            GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ D.J)
          (nativeCondensedDerived l X) S (sections l X).mapDerivedCategory R
          (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
          (pbcDerivedExtend ((D.coefficient E).integralMap l X))
          (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X)
          (finiteCondensedClosureFunctor l X A E) n (D.integral E) (q E)).hom.app Z := by
    unfold normalizationIntegralComparison
    exact rebracketed_hom_app _ _ _ _ _ Z
  intro E L h K
  let B := (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj
  let T := (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
    E L h).obj K
  have hB : B = T := finiteCondensedStageIntegralObject l X E L h K
  let t₀ :=
    (pbcReductionNormalization
      (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h) X)
      ((D.coefficient L).integralMap l X) ((D.coefficient E).integralMap l X)
      (D.coefficient_scalar E L h) K.obj).inv
  let t₁ :=
    (pbcDerivedExtend ((D.coefficient L).integralMap l X)).map
      ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj)
  let t :
      (pbcDerivedExtend ((D.coefficient E).integralMap l X)).obj
            ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K) ⟶
        (pbcDerivedExtend ((D.coefficient L).integralMap l X)).obj
            ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) L) X).ι.obj T) := t₀ ≫ t₁
  have hd := regroupHEq ((D.integral E).hom.app K) t₀ t₁
    ((D.integral L).inv.app T) (D.common_field E L h K)
  have hq := nativeTensorTransition l X D A E L h K
  have hstep := integralSectionComparison_transition
    (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ D.J)
    (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) L) X ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙ D.J)
    (nativeCondensedDerived l X) S (sections l X).mapDerivedCategory R
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) L) X).ι
    (pbcDerivedExtend ((D.coefficient E).integralMap l X))
    (pbcDerivedExtend ((D.coefficient L).integralMap l X))
    (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) L) X)
    (finiteCondensedClosureFunctor l X A E) (finiteCondensedClosureFunctor l X A L)
    n (D.integral E) (D.integral L)
    (q E) (q L) K B T hB
    (D.J.map (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
      ⟨E, (sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K⟩ h).hom))
    ((finiteCondensedClosureTransition l X A h).hom.app
      ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) t
  have hstep' := hstep hd
  have hstep'' := hstep' hq
  simp only [he, Functor.comp_map]
  dsimp (config := { proj := false }) only [Functor.comp_obj, B,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι_obj] at hstep'' ⊢
  exact hstep''

/-- The finite condensed tensor realization and a normalized native functor agree on
integral objects and their integral common-field comparisons. This assertion is made
before extending naturality to rational fractions; it contains no finite full-faithfulness
claim and no formula for a general common-stage morphism.

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.11(3), Proposition 6.8.14(2)
and Remark 6.8.15, the integral comparison in the finite realization argument.
(blueprint: lem-sf-locally-finite-adic-condensed-integral-normalization).

Proof in words: the finite coefficient encoding reconstructs the section ring of the
condensed finite field. Its finiteIso sends each continuous function to the same function
under the fixed small-field equivalence. The finite leg into the closure, followed by
globalCoefficientIso and padicAlgClSheafToAdicConstantSheaf, evaluates that function by
the embedding of the finite field into PadicAlgCl. The rationalInclusion_normalized
clause of D specifies this same map. For integral coefficients, compare every finite
quotient projection: the finite constants and integral_residues clauses, and the
quotient normalizations of the raw identity and continuous realization, send a section
to its residue. Joint monicity of the inverse-limit projections identifies the completed
integral maps. Restriction along the coefficient isomorphisms leaves underlying sections
unchanged. Transport extension through the specified internal/section scalar adjunction;
its unit equation fixes the balanced comparison. Compose the integral raw-identity
comparison, the integral formula of the continuous realization, and this balanced
comparison. The counit of finiteCondensedEncoding gives the displayed natural integral
isomorphism e. Compose its inverse with D.integral transported through native scalar
forgetting and condensedNativeMap. This is natural on every integral arrow, including
torsion objects, since every comparison is natural before localization.

For E contained in L, substitute D.common_field. The raw inverse-completion scalar
normalization identifies the completion-chain comparison with the one in A.raw. The
integral equation of A.scalar identifies its continuous rational comparison with the
same balanced tensor transposition. The coefficient_normalization of A.closure is the
commuting square of actual field inclusions. The unit normalization of
finiteSectionScalarComparison and the two tensor-composition adjunctions therefore give
finiteCondensedScalarComparison, and extending once more to the closure gives precisely
finiteCondensedClosureTransition. Both composites flatten b tensor (a tensor k) to ba
tensor k on a K-flat representative. The derived universal property makes them equal;
this is the stated integral transition equation. Identity inclusions use multiplication
by one and the actual completion unitor. Empty schemes and rank-zero modules give the
same equations with zero sections. No assertion about rational numerator inverses or
general common-stage representatives is used here.
-/
theorem finiteCondensedIntegralNormalization
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (D : NormalizedFunctor l X) (A : AdicFiniteRealization.FiniteCondensedData l X) :
    ∃ e : ∀ E : Index l (PadicAlgCl l),
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ D.J ⋙
            nativeCondensedDerived l X ≅
        sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
          finiteCondensedClosureFunctor l X A E,
      ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
        (D.J ⋙ nativeCondensedDerived l X).map
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
              ⟨E, (sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K⟩ h).hom ≫
          (e L).hom.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj =
          (e E).hom.app K ≫ (finiteCondensedClosureTransition l X A h).hom.app
            ((sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) := by
  exact ⟨normalizationIntegralComparison l X D A,
    normalizationIntegralComparison_transition l X D A⟩

end WeilConjectures.LocallyFiniteAdicRealization
