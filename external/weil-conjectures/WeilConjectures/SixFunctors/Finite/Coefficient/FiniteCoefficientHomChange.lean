/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteHomArrow
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomIntrinsicTensorComposition
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus
import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteTensorNaturalEquality
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteHomInvertible
import all WeilConjectures.CategoryTheory.Ringed.RingedScalarTensorMonoidal
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomTensorAssociatorModel

/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node lemma-change-coefficients-internal-hom--1 (blueprint:
lemma-change-coefficients-internal-hom--1). Indices n and m below denote exponents n + 1 and m + 1;
thus every positive exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b w c d e f g v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Coherence under composition of coefficient functors, with all three canonical arrows.
Source: blueprint displayed A to B to C equation (blueprint:
lemma-change-coefficients-internal-hom--1). -/
def FiniteHomQuotientCocycleAux
    {A B C : Type a} [Category.{b} A] [Category.{b} B] [Category.{b} C]
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B) (HC : Cᵒᵖ × C ⥤ C)
    (F : A ⥤ B) (G : B ⥤ C) (J : A ⥤ C) (α : F ⋙ G ≅ J)
    (v : ∀ K M : A, F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M))
    (w : ∀ K M : B, G.obj (HB.obj (op K, M)) ⟶ HC.obj (op (G.obj K), G.obj M))
    (z : ∀ K M : A, J.obj (HA.obj (op K, M)) ⟶ HC.obj (op (J.obj K), J.obj M)) : Prop :=
  ∀ K M : A, α.hom.app (HA.obj (op K, M)) ≫ z K M =
    G.map (v K M) ≫ w (F.obj K) (F.obj M) ≫
      HC.map (Prod.mkHom (α.inv.app K).op (α.hom.app M))

/-- The cocycle for canonical transposes, with the quotient diagram's data shared.
Source: blueprint A to B to C equation (blueprint: lemma-change-coefficients-internal-hom--1). -/
def FiniteHomQuotientClosedData.Cocycle
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (α : ∀ {n m r : ℕ} (h : m ≤ n) (k : r ≤ m), F h ⋙ F k ≅ F (k.trans h))
    {n m : ℕ} (h : m ≤ n) : Prop :=
  ∀ (r : ℕ) (k : r ≤ m), FiniteHomQuotientCocycleAux (H n) (H m) (H r)
    (F h) (F k) (F (k.trans h)) (α h k)
    (S.comparison h) (S.comparison k) (S.comparison (k.trans h))

attribute [local implicit_reducible]
  CategoryTheory.uniformProd CategoryTheory.prod CategoryTheory.prod'
  CategoryTheory.catToReflQuiver CoefficientClosedStructure.tensor

private theorem finiteChange_isIso_prod
    {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    {X Y : C} {U V : D} (f : X ⟶ Y) (g : U ⟶ V) [IsIso f] [IsIso g] :
    IsIso (Prod.mkHom f g) :=
  (isIso_prod_iff (f := Prod.mkHom f g)).mpr ⟨inferInstance, inferInstance⟩

attribute [local instance] finiteChange_isIso_prod

private theorem finiteChangeEvaluation_naturality
    {C : Type a} [Category.{c} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (K K' M M' : C) (f : K' ⟶ K) (g : M ⟶ M') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 K')) ≫
      S.evaluation K' M' =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M ≫ g := by
  let := S.monoidal
  have hf : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K')) ≫
      S.evaluation K' M =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫ _ =
      S.monoidal.tensorHom (𝟙 (H.obj (op K, M))) f ≫ _
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    exact S.evaluation_naturality K K' M f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K')) ≫
      S.evaluation K' M' = S.evaluation K' M ≫ g := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') ≫ _ = _
    rw [MonoidalCategory.tensorHom_id]
    exact (S.adjunction K').counit.naturality g
  have hh : Prod.mkHom f.op g =
      Prod.mkHom f.op (𝟙 M) ≫ Prod.mkHom (𝟙 (op K')) g := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.id_comp]
  rw [hh, H.map_comp]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 M)) ≫ H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id]
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

private theorem finiteChangeUncurry
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T P Q : D) (h : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm h =
      S.tensor.map (Prod.mkHom h (𝟙 P)) ≫ S.evaluation P Q := by
  let := S.monoidal
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation] using! (S.adjunction P).homEquiv_counit T Q h

private theorem finiteChangeTensor_comp
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {X Y Z U V W : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : U ⟶ V) (k : V ⟶ W) :
    S.tensor.map (Prod.mkHom (f ≫ g) (h ≫ k)) =
      S.tensor.map (Prod.mkHom f h) ≫ S.tensor.map (Prod.mkHom g k) :=
  S.tensor.map_comp (Prod.mkHom f h) (Prod.mkHom g k)

private theorem finiteChangeUncurry_pre
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T U P Q : D}
    (f : T ⟶ U) (h : U ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm (f ≫ h) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (S.transpose U P Q).symm h := by
  rw [finiteChangeUncurry, finiteChangeUncurry]
  simpa only [Category.id_comp, Category.assoc] using
    congrArg (fun k => k ≫ S.evaluation P Q) (finiteChangeTensor_comp S f h (𝟙 P) (𝟙 P))

private theorem finiteChangeUncurry_post
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T P Q P' Q' : D}
    (h : T ⟶ H.obj (op P, Q)) (f : P' ⟶ P) (g : Q ⟶ Q') :
    (S.transpose T P' Q').symm (h ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ (S.transpose T P Q).symm h ≫ g := by
  rw [finiteChangeUncurry_pre, finiteChangeUncurry, finiteChangeEvaluation_naturality]
  rw [finiteChangeUncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  congr 2
  congr 1
  ext <;> simp

private theorem finiteChangeBaseChangeHom_beta
    {A : Type*} {B : Type*} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    (SB.transpose _ (F.obj P) (F.obj Q)).symm (coefficientBaseChangeHom SA SB F μ P Q) =
      μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) :=
  Equiv.symm_apply_apply _ _

private theorem finiteChange_natural
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (K K' M M' : A) (f : K' ⟶ K) (g : M ⟶ M') :
    F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom SA SB F μ K' M' =
      coefficientBaseChangeHom SA SB F μ K M ≫
        HB.map (Prod.mkHom (F.map f).op (F.map g)) := by
  apply (SB.transpose (F.obj (HA.obj (op K, M))) (F.obj K') (F.obj M')).symm.injective
  rw [finiteChangeUncurry_pre, finiteChangeUncurry_post]
  simp only [finiteChangeBaseChangeHom_beta]
  have hμ₁ := μ.inv.naturality
    (Prod.mkHom (HA.map (Prod.mkHom f.op g)) (𝟙 K'))
  have hμ₂ := μ.inv.naturality (Prod.mkHom (𝟙 (HA.obj (op K, M))) f)
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hμ₁ hμ₂
  rw [← Category.assoc, hμ₁, Category.assoc, ← F.map_comp,
    finiteChangeEvaluation_naturality SA, F.map_comp, F.map_comp, ← Category.assoc,
    ← Category.assoc, ← hμ₂]
  simp only [Category.assoc]

private theorem finiteChange_transpose
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (T K M : A) (f : SA.tensor.obj (T, K) ⟶ M) :
    F.map (SA.transpose T K M f) ≫ coefficientBaseChangeHom SA SB F μ K M =
      SB.transpose (F.obj T) (F.obj K) (F.obj M) (μ.inv.app (T, K) ≫ F.map f) := by
  apply (SB.transpose (F.obj T) (F.obj K) (F.obj M)).symm.injective
  rw [finiteChangeUncurry_pre, finiteChangeBaseChangeHom_beta, Equiv.symm_apply_apply]
  have hn := μ.inv.naturality (Prod.mkHom (SA.transpose T K M f) (𝟙 K))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, ← finiteChangeUncurry,
    Equiv.symm_apply_apply]

private theorem finiteChange_composition
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (s : CoefFiniteHomStrong SA SB F μ) (P Q V : A) :
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
          (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V) := by
  let := SA.monoidal
  let := SB.monoidal
  let := s.val.toMonoidal
  have hμ (X Y : A) : Functor.LaxMonoidal.μ F X Y = μ.inv.app (X, Y) := by
    change (s.val.μIso X Y).hom = _
    rw [s.property]
    rfl
  have hAssoc (X Y Z : A) :
      SB.tensor.map (Prod.mkHom (μ.inv.app (X, Y)) (𝟙 (F.obj Z))) ≫
        μ.inv.app (SA.tensor.obj (X, Y), Z) ≫
          F.map (SA.monoidal.associator X Y Z).hom =
      (SB.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) ≫
          μ.inv.app (X, SA.tensor.obj (Y, Z)) := by
    simpa only [← hμ, CoefficientClosedStructure.tensor, Functor.comp_obj,
      Functor.prod_obj, tensor_obj, tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using
      Functor.LaxMonoidal.associativity F X Y Z
  apply (cancel_epi (μ.inv.app (HA.obj (op Q, V), HA.obj (op P, Q)))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (SB.transpose _ (F.obj P) (F.obj V)).symm.injective
  rw [finiteChangeUncurry_pre, finiteChangeUncurry_pre, finiteChangeBaseChangeHom_beta,
    finiteChangeUncurry_pre]
  have hn := μ.inv.naturality (Prod.mkHom (SA.composition P Q V) (𝟙 P))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn
  rw [reassoc_of% hn, ← F.map_comp, ← finiteChangeUncurry]
  simp only [CoefficientClosedStructure.composition, Equiv.symm_apply_apply, F.map_comp]
  rw [reassoc_of% hAssoc]
  have hn' := μ.inv.naturality
    (Prod.mkHom (𝟙 (HA.obj (op Q, V))) (SA.evaluation P Q))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn'
  rw [← reassoc_of% hn']
  have hβ (X Y : A) :
      SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ X Y)
          (𝟙 (F.obj X))) ≫ SB.evaluation (F.obj X) (F.obj Y) =
        μ.inv.app (HA.obj (op X, Y), X) ≫ F.map (SA.evaluation X Y) := by
    rw [← finiteChangeUncurry, finiteChangeBaseChangeHom_beta]
  let v := coefficientBaseChangeHom SA SB F μ
  have hn'' :
      SB.tensor.map (Prod.mkHom (SB.tensor.map (Prod.mkHom (v Q V) (v P Q)))
          (𝟙 (F.obj P))) ≫
        (SB.monoidal.associator (HB.obj (op (F.obj Q), F.obj V))
          (HB.obj (op (F.obj P), F.obj Q)) (F.obj P)).hom =
      (SB.monoidal.associator (F.obj (HA.obj (op Q, V)))
          (F.obj (HA.obj (op P, Q))) (F.obj P)).hom ≫
        SB.tensor.map (Prod.mkHom (v Q V)
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))))) := by
    simpa only [CoefficientClosedStructure.tensor, tensor_map] using
      MonoidalCategory.associator_naturality (v Q V) (v P Q) (𝟙 (F.obj P))
  rw [reassoc_of% hn'']
  have hex :
      SB.tensor.map (Prod.mkHom (v Q V)
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))))) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (HB.obj (op (F.obj Q), F.obj V)))
          (SB.evaluation (F.obj P) (F.obj Q))) =
      SB.tensor.map (Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V))))
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))) ≫
            SB.evaluation (F.obj P) (F.obj Q))) ≫
        SB.tensor.map (Prod.mkHom (v Q V) (𝟙 (F.obj Q))) := by
    simp only [← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [reassoc_of% hex, hβ P Q, hβ Q V]
  have hp : Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V))))
      (μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q)) =
      Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V)))) (μ.inv.app (HA.obj (op P, Q), P)) ≫
        Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V)))) (F.map (SA.evaluation P Q)) := by
    ext <;> simp
  rw [hp, SB.tensor.map_comp]
  simp only [Category.assoc]

private theorem finiteChange_compatible
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (s : CoefFiniteHomStrong SA SB F μ) : CoefficientEvaluationCompatible SA SB F μ := by
  exact ⟨fun P Q P' Q' f g ↦ finiteChange_natural SA SB F μ P P' Q Q' f g,
    finiteChange_transpose SA SB F μ, finiteChange_composition SA SB F μ s⟩

private theorem finiteHomSupportInterval (Z : ℤ → Prop) (hf : Set.Finite {q | ¬ Z q}) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → Z q := by
  classical
  obtain ⟨a, ha⟩ := hf.bddBelow
  obtain ⟨b, hb⟩ := hf.bddAbove
  refine ⟨min a b, max a b, min_le_max, ?_⟩
  intro q hq
  by_contra hnz
  rcases hq with hq | hq
  · exact (not_lt_of_ge (ha hnz)) (lt_of_lt_of_le hq (min_le_left _ _))
  · exact (not_lt_of_ge (hb hnz)) (lt_of_le_of_lt (le_max_right _ _) hq)

-- The Tor predicate tests all representatives; conjugating their presentation isomorphism
-- therefore transports the predicate without changing a resolution or tensor calculation.
private theorem finiteHomTorOfIso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {P Q : proEtaleDerivedCategory T A} (e : P ≅ Q) {a b : ℤ}
    (hP : HasProEtaleTorAmplitude T A P a b) : HasProEtaleTorAmplitude T A Q a b := by
  refine ⟨hP.1, ?_⟩
  intro L R hL f hf hR M i hi
  exact hP.2 L R (hL.map (fun eL ↦ eL ≪≫ e.symm)) f hf hR M i hi

section ScalarMonoidal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SheafOfModules CategoryTheory.ScalarMonoidalProof
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J S)]
end ScalarMonoidal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end

end WeilConjectures
