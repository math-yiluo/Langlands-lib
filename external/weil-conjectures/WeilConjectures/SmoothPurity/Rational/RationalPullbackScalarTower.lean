/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

/-! # The coefficient tower equation for rational pullback

Source: the pullback clause of `scalarOperationsOrdinary_tower`, followed by the
completed and rational comparison normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] rationalDerivedPullback sfRationalScalarExtension
  rationalPullbackScalarComparison sfRationalScalarComp HasDerivedCategory.standard
  integralDerivedPullback integralScalarExtension sfIntegralOrdinaryComparison
  completedIntegralCoefficientSheafUnrestricted integralOrdinaryScalar

attribute [local implicit_reducible] scalarReductionSourceDerived
  integralTowerHasDerivedCategory integralCompletedRingHasDerivedCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  sfIntegralConstructibleLinear ScalarLocalization.linear ScalarLocalization.preadditive
  Linear.homModule Preadditive.homGroup

private theorem conjugate_map {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (η : F ⟶ G) {X Y : C}
    (c : F.obj X ≅ G.obj X) (d : F.obj Y ≅ G.obj Y)
    (hc : c.hom = η.app X) (hd : d.hom = η.app Y) (a : X ⟶ Y) :
    G.map a ≫ d.inv = c.inv ≫ F.map a := by
  apply (cancel_epi c.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hc, ← η.naturality, ← hd]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

-- A pointwise pasting calculation, independent of any coefficient or geometric model.
private theorem conjugate_tower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    (S : C₀ ⥤ C₁) (T : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
    (S' : D₀ ⥤ D₁) (T' T'' : D₁ ⥤ D₂) (U' : D₀ ⥤ D₂)
    (q : F₁ ⋙ T' ⟶ T ⋙ F₂) (K : C₀) (K' : C₁)
    (J : D₁) (K'' K''' : C₂) (J''' : D₂)
    (a : S.obj K ≅ K') (b : S'.obj (F₀.obj K) ≅ J)
    (c : T'.obj J ≅ T''.obj J)
    (d : T'.obj (F₁.obj K') ≅ T''.obj (F₁.obj K'))
    (e : U.obj K ≅ K'') (h : U'.obj (F₀.obj K) ≅ J''')
    (i : T.obj K' ≅ K''')
    (p : S'.obj (F₀.obj K) ⟶ F₁.obj (S.obj K))
    (r : U'.obj (F₀.obj K) ⟶ F₂.obj (U.obj K))
    (ax : T'.obj (S'.obj (F₀.obj K)) ⟶ U'.obj (F₀.obj K))
    (ay : T.obj (S.obj K) ⟶ U.obj K)
    (u : J ⟶ F₁.obj K')
    (hu : u = b.inv ≫ p ≫ F₁.map a.hom)
    (hm : T''.map u ≫ d.inv = c.inv ≫ T'.map u)
    (ht : T'.map p ≫ q.app (S.obj K) ≫ F₂.map ay = ax ≫ r) :
    T''.map u ≫ (d.inv ≫ q.app K' ≫ F₂.map i.hom) ≫
        F₂.map (i.inv ≫ T.map a.inv ≫ ay ≫ e.hom) =
      (c.inv ≫ T'.map b.inv ≫ ax ≫ h.hom) ≫
        (h.inv ≫ r ≫ F₂.map e.hom) := by
  have hq := q.naturality a.hom
  dsimp only [Functor.comp_map] at hq
  have ht' := congrArg (fun z ↦ z ≫ F₂.map e.hom) ht
  simp only [Category.assoc] at ht'
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (T''.map u) d.inv, hm, hu]
  simp only [T'.map_comp, Category.assoc]
  rw [← F₂.map_comp_assoc i.hom i.inv, i.hom_inv_id, F₂.map_id, Category.id_comp]
  rw [← Category.assoc (T'.map (F₁.map a.hom)), hq]
  simp only [Category.assoc]
  rw [← F₂.map_comp_assoc (T.map a.hom) (T.map a.inv), ← T.map_comp,
    a.hom_inv_id, T.map_id, F₂.map_id, Category.id_comp, ht']
  simp only [h.hom_inv_id_assoc]

section Integral
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem ordinaryComparison_eq (W : Scheme.{u}) :
    sfIntegralOrdinaryComparison l E L ι W =
      NatIso.ofComponents
        (F := (sfIntegralConstructible l E W).ι ⋙ integralOrdinaryDerivedScalar l E L ι W)
        (G := (sfIntegralConstructible l E W).ι ⋙ integralScalarExtension l E L ι W)
        (fun K : sfIntegralConstructibleCategory l E W ↦
          scalarCompletionIso l E L ι W K.obj K.property.1)
        (fun a ↦ (scalarCompletion l E L ι W).naturality a.hom) := by
  apply (sfIntegralOrdinaryComparison_existsUnique l E L ι W).unique
  · simpa only [sfIntegralOrdinaryComparison] using
      (sfIntegralOrdinaryComparison_existsUnique l E L ι W).exists.choose_spec
  · intro P hP
    exact (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.1 P

private theorem integral_pullback_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralPullbackScalarComparison l E L ι f K).hom.hom =
      (scalarCompletionIso l E L ι X _
        ((constructibleIntegralPullback l E f).obj K).property.1).inv ≫
      (scalarPullbackOrdinary l E L ι f).hom.app K.obj ≫
      (integralDerivedPullback l L f).map
        (scalarCompletionIso l E L ι Y K.obj K.property.1).hom := by
  rfl

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

private theorem integral_tower {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        L M j X).map (integralPullbackScalarComparison l E L ι f K).hom ≫
      (integralPullbackScalarComparison l L M j f
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K)).hom ≫
      (constructibleIntegralPullback l M f).map
        ((sfIntegralScalarComp l E L ι Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K) =
    (sfIntegralScalarComp l E L ι X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app
        ((constructibleIntegralPullback l E f).obj K) ≫
      (integralPullbackScalarComparison l E M (j.comp ι) f K).hom := by
  apply ObjectProperty.hom_ext
  change (integralScalarExtension l L M j X).map
      (integralPullbackScalarComparison l E L ι f K).hom.hom ≫
      (integralPullbackScalarComparison l L M j f
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K)).hom.hom ≫
      (integralDerivedPullback l M f).map
        ((sfIntegralScalarComp l E L ι Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K).hom =
    ((sfIntegralScalarComp l E L ι X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app
        ((constructibleIntegralPullback l E f).obj K)).hom ≫
      (integralPullbackScalarComparison l E M (j.comp ι) f K).hom.hom
  simp only [sfIntegralScalarComp]
  rw [(sfIntegralScalarComp_existsUnique l E L ι Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).exists.choose_spec K,
    (sfIntegralScalarComp_existsUnique l E L ι X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).exists.choose_spec
        ((constructibleIntegralPullback l E f).obj K)]
  rw [ordinaryComparison_eq, ordinaryComparison_eq, ordinaryComparison_eq,
    ordinaryComparison_eq, ordinaryComparison_eq, ordinaryComparison_eq]
  rw [integral_pullback_component l L M j, integral_pullback_component l E M (j.comp ι)]
  exact conjugate_tower
    (integralDerivedPullback l E f) (integralDerivedPullback l L f)
    (integralDerivedPullback l M f)
    (integralOrdinaryDerivedScalar l E L ι Y) (integralOrdinaryDerivedScalar l L M j Y)
    (integralOrdinaryDerivedScalar l E M (j.comp ι) Y)
    (integralOrdinaryDerivedScalar l E L ι X) (integralOrdinaryDerivedScalar l L M j X)
    (integralScalarExtension l L M j X)
    (integralOrdinaryDerivedScalar l E M (j.comp ι) X)
    (scalarPullbackOrdinary l L M j f).hom K.obj _ _ _ _ _
    (scalarCompletionIso l E L ι Y K.obj K.property.1)
    (scalarCompletionIso l E L ι X _
      ((constructibleIntegralPullback l E f).obj K).property.1)
    (scalarCompletionIso l L M j X _
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj
        ((constructibleIntegralPullback l E f).obj K)).property.1)
    (scalarCompletionIso l L M j X _
      ((constructibleIntegralPullback l L f).obj
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K)).property.1)
    (scalarCompletionIso l E M (j.comp ι) Y K.obj K.property.1)
    (scalarCompletionIso l E M (j.comp ι) X _
      ((constructibleIntegralPullback l E f).obj K).property.1)
    (scalarCompletionIso l L M j Y _
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K).property.1)
    ((scalarPullbackOrdinary l E L ι f).hom.app K.obj)
    ((scalarPullbackOrdinary l E M (j.comp ι) f).hom.app K.obj)
    ((integralOrdinaryDerivedScalarComp l E L ι X M j).hom.app
      ((integralDerivedPullback l E f).obj K.obj))
    ((integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K.obj)
    (integralPullbackScalarComparison l E L ι f K).hom.hom
    (integral_pullback_component l E L ι f K)
    (conjugate_map (scalarCompletion l L M j X) _ _ rfl rfl _)
    ((scalarOperationsOrdinary_tower l E L ι M j f X).1 K.obj)

end Integral

private theorem map_heq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem app_heq {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (α : F ⟶ G) {X X' : C} (h : X = X') :
    HEq (α.app X) (α.app X') := by
  cases h
  rfl

private theorem comp_heq {C : Type*} [Category* C]
    {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hX
  cases hY
  cases hZ
  cases hf
  cases hg
  rfl

section Rational
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem pull_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E f).obj K =
      ⟨(constructibleIntegralPullback l E f).obj K.obj⟩ := by
  simpa only [rationalDerivedPullback] using
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K

private theorem pull_map_integral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {K K' : sfIntegralConstructibleCategory l E Y} (a : K ⟶ K') :
    HEq ((rationalDerivedPullback l E f).map
      ((sfRationalConstructibleLocalization l E Y).map a))
      ((sfRationalConstructibleLocalization l E X).map
        ((constructibleIntegralPullback l E f).map a)) := by
  have h := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K K' a 1
  dsimp only [rationalDerivedPullback, sfRationalConstructibleLocalization,
    ScalarLocalization.localization]
  convert h using 1
  unfold rationalDerivedPullback
  rfl

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem scalar_map_integral (W : Scheme.{u})
    {K K' : sfIntegralConstructibleCategory l E W} (a : K ⟶ K') :
    HEq ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
      ((sfRationalConstructibleLocalization l E W).map a))
      ((sfRationalConstructibleLocalization l L W).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map a)) := by
  have h := sfRationalScalarExtension_map_tmul l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι K K' a 1
  simp only [map_one] at h
  dsimp only [sfRationalConstructibleLocalization, ScalarLocalization.localization]
  convert h using 1
  rfl

private theorem pull_scalar_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    HEq ((rationalPullbackScalarComparison l E L ι f).hom.app K)
      ((sfRationalConstructibleLocalization l L X).map
        (integralPullbackScalarComparison l E L ι f K.obj).hom) := by
  simpa only [rationalPullbackScalarComparison] using
    (rationalPullbackScalarComparison_existsUnique l E L ι f).exists.choose_spec K

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

private theorem scalar_comp_component (W : Scheme.{u})
    (K : sfRationalConstructibleCategory l E W) :
    HEq ((sfRationalScalarComp l E L ι W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K)
      ((sfRationalConstructibleLocalization l M W).map
        ((sfIntegralScalarComp l E L ι W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K.obj)) := by
  simpa only [sfRationalScalarComp] using
    (sfRationalScalarComp_existsUnique l E L ι W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).exists.choose_spec K

end Rational

/-- Rational pullback commutes with a tower of the prescribed scalar extensions.
Source: `scalarOperationsOrdinary_tower`, pullback clause, and the scalar comparison
paragraph of prose-03-02; Stacks Project, Tags 07A4 and 099N.
(blueprint: lem-weil-rational-pullback-scalar-tower).

Proof: use the pullback clause of scalarOperationsOrdinary_tower on E -> L -> M.
Conjugate its ordinary scalar functors by scalarCompletionIso on the input and on
its pullback. Naturality moves these completion comparisons through the pullback
comparison; adjacent inverse completion comparisons cancel. The normalization of
sfIntegralScalarComp identifies the remaining scalar associators. Restrict this
identity to constructible objects, using integralPullbackScalarComparison for the
restricted components. Apply rational localization to the equality. The component
specifications of rationalPullbackScalarComparison and sfRationalScalarComp identify
its terms with the displayed ones, and the integral-map formula for
rationalDerivedPullback identifies the mapped associator. This proves the equation
for every rational object, since these have unchanged integral objects. No
faithfulness of finite reduction is used. Repeated fields and identity maps use the
same equation; zero objects and empty schemes impose no additional condition. -/
theorem rationalPullbackScalarComparison_tower
    (l : ℕ) [Fact l.Prime]
    (E L M : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l L X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).map
        ((rationalPullbackScalarComparison l E L ι f).hom.app K) ≫
      (rationalPullbackScalarComparison l L M j f).hom.app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) ≫
      (rationalDerivedPullback l M f).map
        ((sfRationalScalarComp l E L ι Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K) =
    (sfRationalScalarComp l E L ι X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app
        ((rationalDerivedPullback l E f).obj K) ≫
      (rationalPullbackScalarComparison l E M (j.comp ι) f).hom.app K := by
  let S (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
      (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}) :=
    sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) A B i W
  let Q := sfRationalConstructibleLocalization l M X
  have ha := map_heq
    (sfRationalScalarExtension l L X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j)
    (by simp only [Functor.comp_obj, sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [Functor.comp_obj, sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (pull_scalar_component l E L ι f K)
  have ha' := scalar_map_integral l L M j X
    (integralPullbackScalarComparison l E L ι f K.obj).hom
  have hb : HEq
      ((rationalPullbackScalarComparison l L M j f).hom.app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K))
      (Q.map (integralPullbackScalarComparison l L M j f
        ((S E L ι Y).obj K.obj)).hom) := by
    exact (app_heq (rationalPullbackScalarComparison l L M j f).hom
      (sfRationalScalarExtension_obj l E Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι K)).trans
      (pull_scalar_component l L M j f ⟨(S E L ι Y).obj K.obj⟩)
  have hc := map_heq (rationalDerivedPullback l M f)
    (by simp only [Functor.comp_obj, sfRationalScalarExtension_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [sfRationalScalarExtension_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (scalar_comp_component l E L ι M j Y K)
  have hc' := pull_map_integral l M f
    ((sfIntegralScalarComp l E L ι Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K.obj)
  have hbc := comp_heq
    (by simp only [S, Q, Functor.comp_obj, sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [S, Q, Functor.comp_obj, sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization]) hb (hc.trans hc')
  have hleft := comp_heq
    (by simp only [Functor.comp_obj, sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [Functor.comp_obj, sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization]) (ha.trans ha') hbc
  have hd : HEq
      ((sfRationalScalarComp l E L ι X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app
        ((rationalDerivedPullback l E f).obj K))
      (Q.map ((sfIntegralScalarComp l E L ι X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app
        ((constructibleIntegralPullback l E f).obj K.obj))) := by
    exact (app_heq (sfRationalScalarComp l E L ι X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom (pull_obj l E f K)).trans
      (scalar_comp_component l E L ι M j X
        ⟨(constructibleIntegralPullback l E f).obj K.obj⟩)
  have he := pull_scalar_component l E M (j.comp ι) f K
  have hright := comp_heq
    (by simp only [Q, Functor.comp_obj, sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [Q, sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization])
    (by simp only [Functor.comp_obj, sfRationalScalarExtension_obj, pull_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization]) hd he
  have hi := congrArg (fun a ↦ Q.map a) (integral_tower l E L ι M j f K.obj)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp] at hi
  exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

end WeilConjectures
