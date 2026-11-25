/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Common.CommonStageInternalHomData
import WeilConjectures.ZetaWeil.SpecifiedHomScalarRationalNaturality
import WeilConjectures.ZetaWeil.SpecifiedHomScalarTower

/-! Finite-stage scalar Hom coherence and categorical comparison calculations.

Source: the normalized scalar Hom comparisons in the common-stage internal-Hom paragraph.
(blueprint: lem-weil-common-stage-internal-hom-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.auxLemma false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open Opposite CategoryTheory AlgebraicGeometry

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  rationalDerivedInternalHom sfRationalScalarExtension ScalarLocalization.category
  StageSystem.PairCategory.mkHom
  rationalHomScalarComparison operationStageTransitionIso
  scalarAssociator GeneralAlgebraicallyClosedCoefficients.associator
  sfRationalScalarComp sfRationalScalarUnit
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue ScalarLocalization.composition
  sfIntegralConstructible ScalarLocalization.linear ScalarLocalization.preadditive
  Linear.homModule Preadditive.homGroup Preadditive.fullSubcategory
  Linear.fullSubcategory sfIntegralConstructibleLinear

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

set_option allowUnsafeReducibility true in
attribute [local reducible] ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  rationalHomScalarPair

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (W : Scheme.{u})

namespace CommonStageInternalHom

/-- Extend the two entries of a permitted rational Hom pair and its arrows.
Source: the specified scalar extension and rational Hom pair construction.
(blueprint: lem-weil-common-stage-internal-hom-scalar-coherence). -/
def scalarPairs {E L : Index l Ω} (h : E ≤ L) :
    (constructibleRationalHomPairs l (Coefficient.{u} l Ω E) W).FullSubcategory ⥤
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W).FullSubcategory where
  obj := rationalHomScalarPair l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) W
  map f := ObjectProperty.homMk (Prod.mkHom
    (((transition l Ω W E L h).map f.hom.1.unop).op)
    ((transition l Ω W E L h).map f.hom.2))
  map_id P := by
    apply ObjectProperty.hom_ext
    apply Prod.ext <;> simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Prod.ext <;> simp

set_option allowUnsafeReducibility true in
attribute [local reducible] scalarPairs

/-- The specified rational Hom comparisons, with their prescribed naturality.
Source: specifiedHomScalarRational_naturality.
(blueprint: lem-weil-common-stage-internal-hom-scalar-coherence). -/
def rawComparison {E L : Index l Ω} (h : E ≤ L) :
    rationalDerivedInternalHom l (Coefficient.{u} l Ω E) W ⋙ transition l Ω W E L h ≅
      scalarPairs l Ω W h ⋙ rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W :=
  NatIso.ofComponents (fun P ↦ rationalHomScalarComparison l
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W P)
    (fun {P Q} f ↦ by
      rcases f with ⟨⟨a, b⟩⟩
      simpa only [Functor.comp_map, scalarPairs, Quiver.Hom.op_unop,
        ObjectProperty.homMk, transition] using
        specifiedHomScalarRational_naturality l
          (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) W P Q a.unop b)

attribute [local irreducible] rawComparison

/-- Pair associator: inverse in the contravariant entry, forward in the covariant entry.
Source: the prescribed coefficient-stage scalar associator.
(blueprint: lem-weil-common-stage-internal-hom-scalar-coherence). -/
def scalarPairsAssoc {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M)
    (P : (constructibleRationalHomPairs l (Coefficient.{u} l Ω E) W).FullSubcategory) :
    (scalarPairs l Ω W k).obj ((scalarPairs l Ω W h).obj P) ≅
      (scalarPairs l Ω W (h.trans k)).obj P :=
  ObjectProperty.isoMk _ (Iso.prod
    ((associator l Ω W E L M h k).app P.obj.1.unop).symm.op
    ((associator l Ω W E L M h k).app P.obj.2))

private theorem rawHomTower
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M) (q : E →ₐ[ℚ_[l]] M)
    (hq : j.comp ι = q) (W : Scheme.{u})
    (α : sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
      sfRationalScalarExtension l L W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j ≅
      sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M q)
    (hα : α = scalarAssociator l E L M ι j q hq W)
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    (sfRationalScalarExtension l L W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).map
        (rationalHomScalarComparison l E L ι W P).hom ≫
      (rationalHomScalarComparison l L M j W (rationalHomScalarPair l E L ι W P)).hom ≫
      (rationalDerivedInternalHom l M W).map
        (ObjectProperty.homMk
          (X := rationalHomScalarPair l L M j W (rationalHomScalarPair l E L ι W P))
          (Y := rationalHomScalarPair l E M q W P)
          (Prod.mkHom
            (α.inv.app P.obj.1.unop).op
            (α.hom.app P.obj.2))) =
      α.hom.app
        ((rationalDerivedInternalHom l E W).obj P) ≫
          (rationalHomScalarComparison l E M q W P).hom := by
  subst α
  subst q
  have hs : scalarAssociator l E L M ι j (j.comp ι) rfl W =
      sfRationalScalarComp l E L ι W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j := by
    unfold scalarAssociator
    exact Iso.trans_refl _
  rw [hs]
  exact specifiedHomScalarRational_tower l E L ι W P M j

/-- The specified rational Hom comparison respects two coefficient extensions.
Source: the normalized scalar Hom tower in the common-stage internal-Hom paragraph;
`specifiedHomScalarRational_tower` and the prescribed coefficient-stage associator.
(blueprint: lem-weil-common-stage-internal-hom-scalar-coherence).

Proof: identify the stage associator with the scalar associator using its uniqueness
specification. The coefficient-inclusion composition law identifies the direct extension.
Transport the specified rational Hom tower along these equalities. The contravariant
pair component is the inverse scalar associator; the covariant component is its hom. -/
theorem rationalHomComparison_tower {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M)
    (P : (constructibleRationalHomPairs l (Coefficient.{u} l Ω E) W).FullSubcategory) :
    (transition l Ω W L M k).map ((rawComparison l Ω W h).hom.app P) ≫
      (rawComparison l Ω W k).hom.app ((scalarPairs l Ω W h).obj P) ≫
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω M) W).map
        (scalarPairsAssoc l Ω W h k P).hom =
      (associator l Ω W E L M h k).hom.app
        ((rationalDerivedInternalHom l (Coefficient.{u} l Ω E) W).obj P) ≫
          (rawComparison l Ω W (h.trans k)).hom.app P := by
  have ha := (associator_existsUnique l Ω W E L M h k).exists.choose_spec
  have ha' : associator l Ω W E L M h k =
      scalarAssociator l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E L h)
        (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k) W :=
    by
      unfold GeneralAlgebraicallyClosedCoefficients.associator
      exact eq_of_heq ha
  unfold rawComparison
  dsimp only [NatIso.ofComponents, scalarPairsAssoc,
    ObjectProperty.isoMk, Iso.prod, Iso.op, Iso.symm, Iso.app,
    Functor.comp_obj, scalarPairs]
  exact rawHomTower l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E L h)
    (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k) W
    (associator l Ω W E L M h k) ha' P

private theorem transition_tower
    {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
    (R : ∀ {i j : I}, i ≤ j → C i ⥤ C j)
    (a : ∀ {i j k : I} (h : i ≤ j) (k : j ≤ k), R h ⋙ R k ≅ R (h.trans k))
    (S : StageSystem C) (hR : ∀ {i j : I} (h : i ≤ j), S.T h = R h)
    (ha : ∀ {i j k : I} (h : i ≤ j) (k : j ≤ k), HEq (S.assoc h k) (a h k))
    {i j m : I} (h : i ≤ j) (k : j ≤ m) (X : C i) :
    (S.T k).map ((eqToIso (hR h)).hom.app X) ≫
      (eqToIso (hR k)).hom.app ((R h).obj X) ≫ (a h k).hom.app X =
    (S.assoc h k).hom.app X ≫ (eqToIso (hR (h.trans k))).hom.app X := by
  rcases S with ⟨T, b, hb⟩
  have hT : @T = @R := by funext i j h; exact hR h
  cases hT
  have hB : @b = @a := by funext i j k h k; exact eq_of_heq (ha h k)
  cases hB
  simp

private theorem conjugate_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B U V : C} {A' B' U' V' : D}
    (aP : F.obj A ≅ A') (aQ : F.obj B ≅ B')
    (cP : A ≅ U) (cQ : B ≅ V) (cP' : A' ≅ U') (cQ' : B' ≅ V')
    (dP : F.obj U ≅ U') (dQ : F.obj V ≅ V') (f : U ⟶ V) (g : U' ⟶ V')
    (hp : F.map cP.hom ≫ dP.hom = aP.hom ≫ cP'.hom)
    (hq : F.map cQ.hom ≫ dQ.hom = aQ.hom ≫ cQ'.hom)
    (hn : F.map f ≫ dQ.hom = dP.hom ≫ g) :
    aP.inv ≫ F.map (cP.hom ≫ f ≫ cQ.inv) ≫ aQ.hom =
      cP'.hom ≫ g ≫ cQ'.inv := by
  have hq' : F.map cQ.inv ≫ aQ.hom = dQ.hom ≫ cQ'.inv := by
    apply (cancel_mono cQ'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hq, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [hq', reassoc_of% hn, reassoc_of% hp]
  simp only [Iso.inv_hom_id_assoc]

private theorem transition_inv_tower
    {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
    (R : ∀ {i j : I}, i ≤ j → C i ⥤ C j)
    (a : ∀ {i j k : I} (h : i ≤ j) (k : j ≤ k), R h ⋙ R k ≅ R (h.trans k))
    (S : StageSystem C) (hR : ∀ {i j : I} (h : i ≤ j), S.T h = R h)
    (ha : ∀ {i j k : I} (h : i ≤ j) (k : j ≤ k), HEq (S.assoc h k) (a h k))
    {i j m : I} (h : i ≤ j) (k : j ≤ m) (X : C i) :
    (R k).map ((eqToIso (hR h)).inv.app X) ≫
      (eqToIso (hR k)).inv.app ((S.T h).obj X) ≫
      (S.assoc h k).hom.app X =
    (a h k).hom.app X ≫ (eqToIso (hR (h.trans k))).inv.app X := by
  rcases S with ⟨T, b, hb⟩
  have hT : @T = @R := by funext i j h; exact hR h
  cases hT
  have hB : @b = @a := by funext i j k h k; exact eq_of_heq (ha h k)
  cases hB
  simp

private theorem correction_naturality
    {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
    (S : StageSystem C) {i j n m : I} (hi : i ≤ n) (hj : j ≤ n) (k : n ≤ m)
    (x : C i) (y : C j) (R : C n ⥤ C m) (e : S.T k ≅ R)
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    R.map f ≫ ((e.app ((S.T hj).obj y)).symm ≪≫ (S.assoc hj k).app y).hom =
      ((e.app ((S.T hi).obj x)).symm ≪≫ (S.assoc hi k).app x).hom ≫ S.tr k f := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    StageSystem.tr, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact e.inv.naturality_assoc f _

private theorem inverse_naturality
    {C : Type*} [Category C] {A B A' B' : C}
    (eP : A ≅ A') (eQ : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ eQ.hom = eP.hom ≫ g) : eP.inv ≫ f = g ≫ eQ.inv := by
  rw [eP.inv_comp_eq, ← Category.assoc, eQ.eq_comp_inv]
  exact h

private theorem comparison_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F R : C ⥤ D} (e : F ≅ R) {U : A ⥤ C} {V : B ⥤ D} {S : A ⥤ B}
    (β : U ⋙ R ≅ S ⋙ V) {p q : A} {p' q' : B}
    (cp : S.obj p ≅ p') (cq : S.obj q ≅ q') (f : p ⟶ q) (g : p' ⟶ q')
    (h : S.map f ≫ cq.hom = cp.hom ≫ g) :
    F.map (U.map f) ≫ (e.app (U.obj q) ≪≫ β.app q ≪≫ V.mapIso cq).hom =
      (e.app (U.obj p) ≪≫ β.app p ≪≫ V.mapIso cp).hom ≫ V.map g := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [e.hom.naturality_assoc]
  have hn := β.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← V.map_comp]
  rw [h, V.map_comp]

private theorem comparison_tower_glue
    {A₀ A₁ A₂ C₀ C₁ C₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category C₀] [Category C₁] [Category C₂]
    {U : A₀ ⥤ C₀} {V : A₁ ⥤ C₁} {B : A₂ ⥤ C₂}
    {R₀₁ F₀₁ : C₀ ⥤ C₁} {R₁₂ F₁₂ : C₁ ⥤ C₂} {R₀₂ F₀₂ : C₀ ⥤ C₂}
    {S₀₁ : A₀ ⥤ A₁} {S₁₂ : A₁ ⥤ A₂} {S₀₂ : A₀ ⥤ A₂}
    (e₀₁ : F₀₁ ≅ R₀₁) (e₁₂ : F₁₂ ≅ R₁₂) (e₀₂ : F₀₂ ≅ R₀₂)
    (β₀₁ : U ⋙ R₀₁ ≅ S₀₁ ⋙ V) (β₁₂ : V ⋙ R₁₂ ≅ S₁₂ ⋙ B)
    (β₀₂ : U ⋙ R₀₂ ≅ S₀₂ ⋙ B)
    (a : R₀₁ ⋙ R₁₂ ≅ R₀₂) (a' : F₀₁ ⋙ F₁₂ ≅ F₀₂)
    (p : A₀) {p₁ : A₁} {p₂ : A₂}
    (z₀₁ : S₀₁.obj p ≅ p₁) (z₁₂ : S₁₂.obj p₁ ≅ p₂) (z₀₂ : S₀₂.obj p ≅ p₂)
    (c : S₁₂.obj (S₀₁.obj p) ≅ S₀₂.obj p)
    (hz : S₁₂.map z₀₁.hom ≫ z₁₂.hom = c.hom ≫ z₀₂.hom)
    (hr : R₁₂.map (β₀₁.hom.app p) ≫ β₁₂.hom.app (S₀₁.obj p) ≫ B.map c.hom =
      a.hom.app (U.obj p) ≫ β₀₂.hom.app p)
    (he : F₁₂.map (e₀₁.hom.app (U.obj p)) ≫
        e₁₂.hom.app (R₀₁.obj (U.obj p)) ≫ a.hom.app (U.obj p) =
      a'.hom.app (U.obj p) ≫ e₀₂.hom.app (U.obj p)) :
    F₁₂.map (e₀₁.app (U.obj p) ≪≫ β₀₁.app p ≪≫ V.mapIso z₀₁).hom ≫
        (e₁₂.app (V.obj p₁) ≪≫ β₁₂.app p₁ ≪≫ B.mapIso z₁₂).hom =
      a'.hom.app (U.obj p) ≫
        (e₀₂.app (U.obj p) ≪≫ β₀₂.app p ≪≫ B.mapIso z₀₂).hom := by
  have hn := β₁₂.hom.naturality z₀₁.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have heβ := e₁₂.hom.naturality (β₀₁.hom.app p)
  dsimp only [Functor.comp_obj] at heβ
  rw [e₁₂.hom.naturality_assoc (V.map z₀₁.hom), reassoc_of% heβ,
    reassoc_of% hn]
  rw [← B.map_comp, hz, B.map_comp]
  rw [reassoc_of% hr, reassoc_of% he]

private def inputStep
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    {E L : Index l Ω} (hi : P.stage ≤ E) (h : E ≤ L) :
    (transition l Ω W E L h).obj (P.toStage hi) ≅ P.toStage (hi.trans h) :=
  ((operationStageTransitionIso l Ω W E L h).app (P.toStage hi)).symm ≪≫
    ((stageSystem l Ω W).assoc hi h).app P.obj

private theorem inputStep_tower
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    {E L M : Index l Ω} (hi : P.stage ≤ E) (h : E ≤ L) (k : L ≤ M) :
    (transition l Ω W L M k).mapIso (inputStep l Ω W P hi h) ≪≫
        inputStep l Ω W P (hi.trans h) k =
      (associator l Ω W E L M h k).app (P.toStage hi) ≪≫
        inputStep l Ω W P hi (h.trans k) := by
  apply Iso.ext
  dsimp only [inputStep, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (operationStageTransitionIso l Ω W L M k).inv.naturality]
  rw [(stageSystem l Ω W).cocycle hi h k P.obj]
  have ht := @transition_inv_tower (Index l Ω) inferInstance
    (Stage l Ω W) (stageCategory l Ω W)
    (fun {E L} h ↦ transition l Ω W E L h)
    (fun {E L M} h k ↦ associator l Ω W E L M h k)
    (stageSystem l Ω W)
    (fun {E L} h ↦ by
      simpa only [stageSystem] using
        (stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)
    (fun {E L M} h k ↦ by
      simpa only [stageSystem] using
        (stageSystem_existsUnique l Ω W).exists.choose_spec.2 E L M h k)
    E L M h k (P.toStage hi)
  simpa only [operationStageTransitionIso, Category.assoc] using
    congrArg (fun f ↦ f ≫ ((stageSystem l Ω W).assoc hi (h.trans k)).hom.app P.obj) ht

private theorem inputStep_naturality
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    {E L : Index l Ω} (hi : P.stage ≤ E) (hj : Q.stage ≤ E) (k : E ≤ L)
    (f : P.toStage hi ⟶ Q.toStage hj) :
    (transition l Ω W E L k).map f ≫ (inputStep l Ω W Q hj k).hom =
      (inputStep l Ω W P hi k).hom ≫ (stageSystem l Ω W).tr k f := by
  unfold inputStep
  exact @correction_naturality (Index l Ω) inferInstance
    (Stage l Ω W) (stageCategory l Ω W) (stageSystem l Ω W)
    P.stage Q.stage E L hi hj k P.obj Q.obj (transition l Ω W E L k)
    (operationStageTransitionIso l Ω W E L k) f

end CommonStageInternalHom
end WeilConjectures
