/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel
import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorCompletionChainUniqueness
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion

/-! # Comparison of normalized quotient tensor models

The private constructible-unit proof is the existing proof from the item, extracted so its
checking is independent of coefficient transport. No definition or interface is changed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory

namespace WeilConjectures.ProjectionTensorModelComparison

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted SheafOfModules.monoidalCategory
attribute [local instance 3000] integralTowerHasDerivedCategory

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

attribute [local implicit_reducible] PurCompactSupport.completed

private theorem exists_pair_of_chain
    {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*}
    {D : ∀ a b, C a b → Sort*} {I J : Sort*}
    {p : I → Prop} {q : J → Prop}
    {L M : ∀ a b, C a b → Prop} {N : ∀ a b c, D a b c → Prop}
    {P : A → I → J → Prop} {Q : ∀ a b c, D a b c → I → J → Prop}
    (h : ∃ a b c, L a b c ∧ M a b c ∧
      ∃ d, N a b c d ∧ ∀ i j, p i → q j → P a i j ∧ Q a b c d i j) :
    ∃ (a : A) (_b : B a), ∀ i j, p i → q j → P a i j := by
  obtain ⟨a, b, c, _, _, d, _, hd⟩ := h
  exact ⟨a, b, fun i j hi hj ↦ (hd i j hi hj).1⟩

private theorem completionUnit_comp_isIso
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} (eta : F ⟶ G) {A B : C} {Z : D}
    (e : A ≅ B) (c : G.obj B ≅ Z) (ha : IsIso (eta.app A)) :
    IsIso (eta.app B ≫ c.hom) := by
  have hi : IsIso (eta.app B) := (NatTrans.isIso_app_iff_of_iso eta e).mp ha
  exact IsIso.comp_isIso' hi c.isIso_hom

private theorem completion_isIso (t : OpenFactorCoherence.Tensor l E X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [∀ x : X, Invertible (l : X.residueField x)]
    (M N : sfIntegralConstructibleCategory l E X) :
    IsIso ((t.chi l E).app (M.obj, N.obj)) := by
  classical
  obtain ⟨T, r, hT⟩ := exists_pair_of_chain (constructibleTensorCompletion l E X)
  let q := integralOperationsGoodLocalization l E X
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  have : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E X
  let ff := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (V.prod V)
    (DerivedCategory (integralTowerModules l E X))
  let e : T ≅ t.ordinary.tensor := ff.preimageIso (r.symm ≪≫ t.ordinary.representative)
  have hu : IsIso ((OpenFactorCoherence.eta l E X).app (T.obj (M.obj, N.obj))) :=
    (IntegralOnSlice.canonicalCompletionUnitCriterion l E X _).mpr
      (hT M.obj N.obj M.property N.property)
  exact completionUnit_comp_isIso (OpenFactorCoherence.eta l E X)
    (e.app (M.obj, N.obj)) (t.comparison.app (M.obj, N.obj)) hu

private theorem four_comp_reassociate {C : Type*} [Category* C]
    {A B D E F : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (i : E ⟶ F)
    (k : A ⟶ F) (hk : f ≫ g ≫ h ≫ i = k) : f ≫ (g ≫ h) ≫ i = k := by
  simpa only [Category.assoc] using hk

private theorem ratio_of_squares {C : Type*} [Category* C] {U A B V W : C}
    (r : U ≅ A) (s : U ≅ B) (e : A ≅ B) (a : A ⟶ V) (b : B ⟶ V) (c : V ≅ W)
    (he : r.hom ≫ e.hom = s.hom)
    (h : r.hom ≫ a ≫ c.hom = s.hom ≫ b ≫ c.hom) : e.hom ≫ b = a := by
  apply (cancel_epi r.hom).mp
  apply (cancel_mono c.hom).mp
  have h' := h.symm
  rw [← he] at h'
  simpa only [Category.assoc] using h'

/-- The normalized ratio of two tensor models intertwines their actual completion arrows.
Source: Bhatt--Scholze 3.4.10 and 6.5.5; Stacks 06YS--06YT
(blueprint: lem-sf-projection-tensor-model-comparison).
Proof: restrict the derived localization to flat-term K-flat complexes and take its product.
Fully faithful restriction lifts the ratio of the two representative isomorphisms to an
isomorphism of the ordinary tensor functors. Its defining equation is the first clause.
For the second clause, restrict to representatives and cancel the source representative and
completed target representative. Both remaining maps are the localization of the same chain
augmentation: tensorCompletionChain_unique identifies them from their two coordinates.
Faithfulness of restriction proves the global equation. Empty sites and zero summands need
no separate assumption, since the same universal properties apply. -/
theorem models_comparison (t s : OpenFactorCoherence.Tensor l E X) :
    ∃ e : t.ordinary.tensor ≅ s.ordinary.tensor,
      (∀ P Q : (proEtaleFlatRepresentatives X
          (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory,
        t.ordinary.representative.hom.app (P, Q) ≫
          e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
        s.ordinary.representative.hom.app (P, Q)) ∧
      e.hom ≫ s.chi l E = t.chi l E := by
  let P := proEtaleFlatRepresentatives X (completedIntegralCommRingSheafUnrestricted l E X)
  let q := P.ι ⋙ DerivedCategory.Q
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage P.ι
  have : q.IsLocalization V := goodComplexes_isLocalization
    (completedIntegralCommRingSheafUnrestricted l E X) P (by
      intro K
      exact and_congr
        (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).symm Iff.rfl)
  let ff := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (V.prod V)
    (DerivedCategory (integralTowerModules l E X))
  let e := ff.preimageIso (t.ordinary.representative.symm ≪≫ s.ordinary.representative)
  have he (A B : P.FullSubcategory) :
      t.ordinary.representative.hom.app (A, B) ≫
          e.hom.app (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj) =
        s.ordinary.representative.hom.app (A, B) := by
    have h := congr_app (ff.map_preimage
      (t.ordinary.representative.symm ≪≫ s.ordinary.representative).hom) (A, B)
    change e.hom.app (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj) = _ at h
    rw [h]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Iso.hom_inv_id_app_assoc]
  refine ⟨e, he, ?_⟩
  apply ff.map_injective
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨A, B⟩
  change e.hom.app (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj) ≫
    (s.chi l E).app (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj) =
      (t.chi l E).app (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj)
  let c := (integralCompletedTensorComparison l E X).app
    (⟨A.obj, t.good A.obj A.property⟩, ⟨B.obj, t.good B.obj B.property⟩)
  have ht := t.canonical.2 A.obj B.obj A.property B.property
  have hs := s.canonical.2 A.obj B.obj A.property B.property
  have hc := OpenFactorCoherence.tensorCompletionChain_unique l E X t.chain s.chain
    t.canonical.1 s.canonical.1
  have ht' : t.ordinary.representative.hom.app (A, B) ≫
      (t.chi l E).app (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj) ≫ c.hom =
        DerivedCategory.Q.map (t.chain.app (A.obj, B.obj)) := by
    exact four_comp_reassociate _ _ _ _ _ ht
  have hs' : s.ordinary.representative.hom.app (A, B) ≫
      (s.chi l E).app (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj) ≫ c.hom =
        DerivedCategory.Q.map (s.chain.app (A.obj, B.obj)) := by
    exact four_comp_reassociate _ _ _ _ _ hs
  have hchain := congrArg (fun ch ↦ DerivedCategory.Q.map (ch.app (A.obj, B.obj))) hc
  exact ratio_of_squares (t.ordinary.representative.app (A, B))
    (s.ordinary.representative.app (A, B))
    (e.app (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj)) _ _ c (he A B)
    (ht'.trans (hchain.trans hs'.symm))

end WeilConjectures.ProjectionTensorModelComparison
