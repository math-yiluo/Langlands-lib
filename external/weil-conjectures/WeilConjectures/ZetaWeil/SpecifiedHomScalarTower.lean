/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

/-! # Rational tower coherence for the specified Hom comparison

The ordinary internal-Hom tower equation is conjugated by the normalized completion
maps, restricted to constructible objects, and then carried through rational localization.
The first Hom variable uses the inverse scalar associator throughout.

(blueprint: lem-zl-specified-hom-scalar-rational-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory Opposite TensorProduct
universe u₁ v₁ u₂ v₂ u₃ v₃
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue
/-- Conjugating an internal-Hom tower by objectwise isomorphisms preserves its equation.
Move the completion comparison past the first arrow by naturality, use naturality of
ordinary Hom on the two input comparisons, and cancel the adjacent inverse factors. -/
private theorem conjugatedHomTower
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]
    (H : Cᵒᵖ × C ⥤ C) (K : Dᵒᵖ × D ⥤ D) (J : Eᵒᵖ × E ⥤ E)
    (F U : C ⥤ D) (G V : D ⥤ E) (T W : C ⥤ E)
    (a : F ⋙ G ≅ T) (d : G ⟶ V)
    (f : ∀ M N, F.obj (H.obj (op M, N)) ⟶ K.obj (op (F.obj M), F.obj N))
    (g : ∀ M N, G.obj (K.obj (op M, N)) ⟶ J.obj (op (G.obj M), G.obj N))
    (h : ∀ M N, T.obj (H.obj (op M, N)) ⟶ J.obj (op (T.obj M), T.obj N))
    (ng : ∀ M N M' N' (x : M' ⟶ M) (y : N ⟶ N'),
      G.map (K.map (Prod.mkHom x.op y)) ≫ g M' N' =
        g M N ≫ J.map (Prod.mkHom (G.map x).op (G.map y)))
    (tower : ∀ M N, G.map (f M N) ≫ g (F.obj M) (F.obj N) ≫
      J.map (Prod.mkHom (a.inv.app M).op (a.hom.app N)) =
        a.hom.app (H.obj (op M, N)) ≫ h M N)
    (M N : C)
    (cM : F.obj M ≅ U.obj M) (cN : F.obj N ≅ U.obj N)
    (cH : F.obj (H.obj (op M, N)) ≅ U.obj (H.obj (op M, N)))
    (dM : G.obj (U.obj M) ≅ V.obj (U.obj M))
    (dN : G.obj (U.obj N) ≅ V.obj (U.obj N))
    (dH : G.obj (U.obj (H.obj (op M, N))) ≅ V.obj (U.obj (H.obj (op M, N))))
    (dK : G.obj (K.obj (op (U.obj M), U.obj N)) ≅
      V.obj (K.obj (op (U.obj M), U.obj N)))
    (hdH : dH.hom = d.app _) (hdK : dK.hom = d.app _)
    (eM : T.obj M ≅ W.obj M) (eN : T.obj N ≅ W.obj N)
    (eH : T.obj (H.obj (op M, N)) ≅ W.obj (H.obj (op M, N))) :
    V.map (cH.inv ≫ f M N ≫ K.map (Prod.mkHom cM.inv.op cN.hom)) ≫
      (dK.inv ≫ g (U.obj M) (U.obj N) ≫
        J.map (Prod.mkHom dM.inv.op dN.hom)) ≫
      J.map (Prod.mkHom
        ((eM.inv ≫ a.inv.app M ≫ G.map cM.hom ≫ dM.hom).op)
        (dN.inv ≫ G.map cN.inv ≫ a.hom.app N ≫ eN.hom)) =
    (dH.inv ≫ G.map cH.inv ≫ a.hom.app (H.obj (op M, N)) ≫ eH.hom) ≫
      (eH.inv ≫ h M N ≫ J.map (Prod.mkHom eM.inv.op eN.hom)) := by
  have nd := d.naturality (cH.inv ≫ f M N ≫ K.map (Prod.mkHom cM.inv.op cN.hom))
  simp only [← Category.assoc] at nd
  have nd' : V.map (cH.inv ≫ f M N ≫ K.map (Prod.mkHom cM.inv.op cN.hom)) ≫ dK.inv =
      dH.inv ≫ G.map (cH.inv ≫ f M N ≫ K.map (Prod.mkHom cM.inv.op cN.hom)) := by
    apply (cancel_epi dH.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hdH, ← nd]
    rw [← hdK]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [← Category.assoc] at nd' ⊢
  rw [nd']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (ng (F.obj M) (F.obj N) (U.obj M) (U.obj N) cM.inv cN.hom)]
  simp only [← J.map_comp, prod_comp, ← op_comp, Category.assoc,
    Iso.hom_inv_id_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]
  simp only [← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp]
  have hp : Prod.mkHom (eM.inv ≫ a.inv.app M ≫ 𝟙 _).op (a.hom.app N ≫ eN.hom) =
      Prod.mkHom (a.inv.app M).op (a.hom.app N) ≫
        Prod.mkHom eM.inv.op eN.hom := by
    apply Prod.ext
    · simp only [prod_comp, Prod.mkHom, ← op_comp, Category.comp_id]
    · rfl
  erw [hp, J.map_comp]
  simp only [Category.assoc, G.map_comp]
  rw [reassoc_of% (tower M N)]

private theorem depHeq {A : Sort*} {B : A → Sort*} (f : ∀ x, B x)
    {x y : A} (h : x = y) : HEq (f x) (f y) := by
  cases h
  rfl

private theorem mapHeq {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq (T.map f) (T.map g) := by
  cases hA
  cases hB
  cases h
  rfl

private theorem compHeq {C : Type*} [Category C]
    {A B C₁ A' B' C' : C} (hA : A = A') (hB : B = B') (hC : C₁ = C')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : B ⟶ C₁} {g' : B' ⟶ C'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hA
  cases hB
  cases hC
  cases hf
  cases hg
  rfl

private theorem invHeq {C : Type*} [Category C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (e : A ≅ B) (e' : A' ≅ B')
    (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  cases hA
  cases hB
  have he : e = e' := Iso.ext (eq_of_heq h)
  cases he
  rfl

private theorem appHeq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {K K' : C} (h : K = K') :
    HEq (α.app K) (α.app K') := by
  cases h
  rfl

universe u
open AlgebraicGeometry
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
/-- The full-subcategory completion comparison has the specified ambient components.
Both are normalized by the same quotient maps, so the recorded uniqueness applies. -/
private theorem completion_app (X : Scheme.{u})
    (K : sfIntegralConstructibleCategory l E X) :
    (sfIntegralOrdinaryComparison l E L ι X).app K =
      scalarCompletionIso l E L ι X K.obj K.property.1 := by
  let χ := scalarCompletion l E L ι X
  let (J : sfIntegralConstructibleCategory l E X) : IsIso (χ.app J.obj) :=
    (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.2 J.obj J.property.1
  let e : (sfIntegralConstructible l E X).ι ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      (sfIntegralConstructible l E X).ι ⋙ integralScalarExtension l E L ι X :=
    NatIso.ofComponents (fun J ↦ asIso (χ.app J.obj)) (fun f ↦ χ.naturality f.hom)
  have he : e = sfIntegralOrdinaryComparison l E L ι X := by
    apply (sfIntegralOrdinaryComparison_existsUnique l E L ι X).unique
    · intro P hP
      exact (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.1 P
    · exact (sfIntegralOrdinaryComparison_existsUnique l E L ι X).exists.choose_spec
  apply Iso.ext
  exact (congrArg (fun a ↦ a.hom.app K) he).symm

/-- The restricted integral associator is the ordinary associator conjugated by completion.
This is its defining component normalization, with the completion isomorphisms identified. -/
private theorem integralComp_app (X : Scheme.{u})
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (K : sfIntegralConstructibleCategory l E X) :
    (sfIntegralConstructible l F X).ι.mapIso
      ((sfIntegralScalarComp l E L ι X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).app K) =
      (scalarCompletionIso l L F j X _
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K).property.1).symm ≪≫
      (integralOrdinaryDerivedScalar l L F j X).mapIso
        (scalarCompletionIso l E L ι X K.obj K.property.1).symm ≪≫
      (integralOrdinaryDerivedScalarComp l E L ι X F j).app K.obj ≪≫
      scalarCompletionIso l E F (j.comp ι) X K.obj K.property.1 := by
  apply Iso.ext
  have h := (sfIntegralScalarComp_existsUnique l E L ι X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).exists.choose_spec K
  simp only [Functor.mapIso_hom, Iso.app_hom, ObjectProperty.ι_map,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change ((sfIntegralScalarComp l E L ι X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app K).hom = _ at h
  refine h.trans ?_
  have hc := completion_app l E L ι X K
  have hd := completion_app l L F j X
    ((sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K)
  have he := completion_app l E F (j.comp ι) X K
  change (sfIntegralOrdinaryComparison l L F j X).inv.app
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K) ≫
    (integralOrdinaryDerivedScalar l L F j X).map
      ((sfIntegralOrdinaryComparison l E L ι X).inv.app K) ≫
    (integralOrdinaryDerivedScalarComp l E L ι X F j).hom.app K.obj ≫
    (sfIntegralOrdinaryComparison l E F (j.comp ι) X).hom.app K = _
  change (sfIntegralOrdinaryComparison l E L ι X).app K = _ at hc
  rw [show (sfIntegralOrdinaryComparison l E L ι X).inv.app K =
      (scalarCompletionIso l E L ι X K.obj K.property.1).inv from congrArg Iso.inv hc]
  rw [show (sfIntegralOrdinaryComparison l L F j X).inv.app _ = _ from
    congrArg Iso.inv hd]
  rw [show (sfIntegralOrdinaryComparison l E F (j.comp ι) X).hom.app K = _ from
    congrArg Iso.hom he]
  rfl

/-- The ordinary Hom tower descends to the permitted constructible integral pairs.
Apply the categorical conjugation calculation to the three scalar completion maps.
The prescribed integral associator has exactly the conjugated components, and the
full-subcategory inclusion is faithful. Source: the ordinary tower and completion
normalizations in `IntegralOperationsScalarComparisons` and `SfScalarExtensionComposition`. -/
private theorem integralHomTower (X : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E X).FullSubcategory)
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) :
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L F j X).map
        (integralHomScalarComparison l E L ι X P).hom ≫
      (integralHomScalarComparison l L F j X (integralHomScalarPair l E L ι X P)).hom ≫
      (constructibleIntegralHom l F X).map
        (ObjectProperty.homMk
          (X := integralHomScalarPair l L F j X (integralHomScalarPair l E L ι X P))
          (Y := integralHomScalarPair l E F (j.comp ι) X P)
          (Prod.mkHom
            (((sfIntegralScalarComp l E L ι X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).inv.app P.obj.1.unop).op)
            ((sfIntegralScalarComp l E L ι X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app P.obj.2))) =
      (sfIntegralScalarComp l E L ι X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app
          ((constructibleIntegralHom l E X).obj P) ≫
        (integralHomScalarComparison l E F (j.comp ι) X P).hom := by
  apply ObjectProperty.hom_ext
  have h := conjugatedHomTower
    (integralDerivedInternalHom l E X) (integralDerivedInternalHom l L X)
    (integralDerivedInternalHom l F X)
    (integralOrdinaryDerivedScalar l E L ι X) (integralScalarExtension l E L ι X)
    (integralOrdinaryDerivedScalar l L F j X) (integralScalarExtension l L F j X)
    (integralOrdinaryDerivedScalar l E F (j.comp ι) X)
    (integralScalarExtension l E F (j.comp ι) X)
    (integralOrdinaryDerivedScalarComp l E L ι X F j) (scalarCompletion l L F j X)
    (scalarHomOrdinary l E L ι X) (scalarHomOrdinary l L F j X)
    (scalarHomOrdinary l E F (j.comp ι) X)
    (scalarHomOrdinary_naturality l L F j X)
    ((scalarOperationsOrdinary_tower l E L ι F j (𝟙 X) X).2.2)
    P.obj.1.unop.obj P.obj.2.obj
    (scalarCompletionIso l E L ι X _ P.obj.1.unop.property.1)
    (scalarCompletionIso l E L ι X _ P.obj.2.property.1)
    (scalarCompletionIso l E L ι X _ P.property.1)
    (scalarCompletionIso l L F j X _
      (integralHomScalarPair l E L ι X P).obj.1.unop.property.1)
    (scalarCompletionIso l L F j X _
      (integralHomScalarPair l E L ι X P).obj.2.property.1)
    (scalarCompletionIso l L F j X _
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj
          ((constructibleIntegralHom l E X).obj P)).property.1)
    (scalarCompletionIso l L F j X _
      (integralHomScalarPair l E L ι X P).property.1)
    rfl rfl
    (scalarCompletionIso l E F (j.comp ι) X _ P.obj.1.unop.property.1)
    (scalarCompletionIso l E F (j.comp ι) X _ P.obj.2.property.1)
    (scalarCompletionIso l E F (j.comp ι) X _ P.property.1)
  have hm := congrArg Iso.inv (integralComp_app l E L ι X F j P.obj.1.unop)
  have hn := congrArg Iso.hom (integralComp_app l E L ι X F j P.obj.2)
  have hh := congrArg Iso.hom
    (integralComp_app l E L ι X F j ((constructibleIntegralHom l E X).obj P))
  dsimp only [Functor.mapIso_inv, Functor.mapIso_hom, ObjectProperty.ι_map,
    Iso.app_inv, Iso.app_hom, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom]
    at hm hn hh
  -- Normalize the fixed completion comparisons and the three associator components.
  dsimp only [ObjectProperty.FullSubcategory.comp_hom,
    sfConstructibleIntegralScalarExtension, constructibleIntegralHom,
    ObjectProperty.lift, Functor.comp_map, Functor.prod_map, Functor.op_map,
    ObjectProperty.ι_map] at ⊢
  delta integralHomScalarComparison integralHomScalarPair scalarHomCompleted
    ObjectProperty.isoMk ObjectProperty.homMk
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom, Iso.prod_hom,
    Iso.op_hom]
  simp only [Category.assoc] at hm hn hh
  erw [hm, hn, hh]
  exact h

private theorem homObj (X : Scheme.{u})
    (P : (constructibleRationalHomPairs l E X).FullSubcategory) :
    (rationalDerivedInternalHom l E X).obj P =
      ⟨(constructibleIntegralHom l E X).obj (integralPairOfRationalHomPair l E X P)⟩ :=
  (rationalDerivedInternalHom_existsUnique l E X).exists.choose_spec.1 P

private theorem homMap (X : Scheme.{u})
    (P Q : (constructibleRationalHomPairs l E X).FullSubcategory)
    (a : Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj) (b : P.obj.2.obj ⟶ Q.obj.2.obj) :
    HEq ((rationalDerivedInternalHom l E X).map (ObjectProperty.homMk
      (Prod.mkHom ((sfRationalConstructibleLocalization l E X).map a).op
        ((sfRationalConstructibleLocalization l E X).map b))))
      ((sfRationalConstructibleLocalization l E X).map
        ((constructibleIntegralHom l E X).map
          (X := integralPairOfRationalHomPair l E X P)
          (Y := integralPairOfRationalHomPair l E X Q)
          (ObjectProperty.homMk (Prod.mkHom a.op b)))) := by
  obtain ⟨β, hβ, ht⟩ :=
    (rationalDerivedInternalHom_existsUnique l E X).exists.choose_spec.2 P Q
  change HEq ((rationalDerivedInternalHom_existsUnique l E X).exists.choose.map _) _
  erw [hβ]
  with_unfolding_all
    simpa only [sfRationalConstructibleLocalization, ScalarLocalization.localization, one_mul]
      using ht a b 1 1

private theorem homMapTransport (X : Scheme.{u})
    (P Q : (constructibleRationalHomPairs l E X).FullSubcategory)
    (P₀ Q₀ : (constructibleIntegralHomPairs l E X).FullSubcategory)
    (hP : integralPairOfRationalHomPair l E X P = P₀)
    (hQ : integralPairOfRationalHomPair l E X Q = Q₀)
    (a : Q₀.obj.1.unop ⟶ P₀.obj.1.unop) (b : P₀.obj.2 ⟶ Q₀.obj.2)
    (a' : Q.obj.1.unop ⟶ P.obj.1.unop) (b' : P.obj.2 ⟶ Q.obj.2)
    (ha : HEq a' ((sfRationalConstructibleLocalization l E X).map a))
    (hb : HEq b' ((sfRationalConstructibleLocalization l E X).map b)) :
    HEq ((rationalDerivedInternalHom l E X).map
      (ObjectProperty.homMk (Prod.mkHom a'.op b')))
      ((sfRationalConstructibleLocalization l E X).map
        ((constructibleIntegralHom l E X).map (ObjectProperty.homMk (Prod.mkHom a.op b)))) := by
  subst P₀ Q₀
  have ha' : a' = (sfRationalConstructibleLocalization l E X).map a := eq_of_heq ha
  have hb' : b' = (sfRationalConstructibleLocalization l E X).map b := eq_of_heq hb
  rw [ha', hb']
  exact homMap l E X P Q a b

private theorem scalarObj (X : Scheme.{u}) (K : sfRationalConstructibleCategory l E X) :
    (sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K =
      ⟨(sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K.obj⟩ :=
  (sfRationalScalarExtension_existsUnique l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 K

private theorem scalarMap (X : Scheme.{u})
    {K K' : sfIntegralConstructibleCategory l E X} (f : K ⟶ K') :
    HEq ((sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
      ((sfRationalConstructibleLocalization l E X).map f))
      ((sfRationalConstructibleLocalization l L X).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map f)) := by
  have h := (sfRationalScalarExtension_existsUnique l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 K K' f 1
  exact h.trans (heq_of_eq (by simp only [map_one]; rfl))

private theorem scalarPair (X : Scheme.{u})
    (P : (constructibleRationalHomPairs l E X).FullSubcategory) :
    integralPairOfRationalHomPair l L X (rationalHomScalarPair l E L ι X P) =
      integralHomScalarPair l E L ι X (integralPairOfRationalHomPair l E X P) := by
  apply ObjectProperty.FullSubcategory.ext
  change (op (((sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop).obj),
    ((sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2).obj) = _
  rw [scalarObj, scalarObj]
  rfl

private theorem scalarObjComp (X : Scheme.{u})
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (K : sfRationalConstructibleCategory l E X) :
    (sfRationalScalarExtension l L X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).obj
        ((sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) =
      ⟨(sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L F j X).obj
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K.obj)⟩ := by
  rw [scalarObj, scalarObj]

private theorem compInv (X : Scheme.{u})
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (K : sfRationalConstructibleCategory l E X) :
    HEq ((sfRationalScalarComp l E L ι X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).inv.app K)
      ((sfRationalConstructibleLocalization l F X).map
        ((sfIntegralScalarComp l E L ι X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).inv.app K.obj)) := by
  exact invHeq (scalarObjComp l E L ι X F j K)
    (scalarObj l E F (j.comp ι) X K)
    ((sfRationalScalarComp l E L ι X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).app K)
    ((sfRationalConstructibleLocalization l F X).mapIso
      ((sfIntegralScalarComp l E L ι X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).app K.obj))
    ((sfRationalScalarComp_existsUnique l E L ι X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).exists.choose_spec K)

/-- The specified Hom comparison satisfies scalar tower coherence after rationalization.
Source: the scalar-extension compatibility clause of the finite/rational operations
interface and the specified Hom comparison (blueprint: lem-zl-specified-hom-scalar-rational-tower).
Proof: first conjugate the ordinary tower by the normalized completion maps and restrict
it to permitted integral pairs. Rational Hom and scalar extension have the prescribed
integral objects and maps. Their normalization identifies the three Hom comparisons and
the scalar associator with the localized integral components, including the inverse in
the first Hom variable. Functoriality of localization carries the integral equation to
the displayed one. Endpoint equalities are handled explicitly; no faithfulness of the
rational localization is required. -/
theorem specifiedHomScalarRational_tower (X : Scheme.{u})
    (P : (constructibleRationalHomPairs l E X).FullSubcategory)
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) :
      (sfRationalScalarExtension l L X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).map
          (rationalHomScalarComparison l E L ι X P).hom ≫
        (rationalHomScalarComparison l L F j X (rationalHomScalarPair l E L ι X P)).hom ≫
        (rationalDerivedInternalHom l F X).map
          (ObjectProperty.homMk
            (X := rationalHomScalarPair l L F j X (rationalHomScalarPair l E L ι X P))
            (Y := rationalHomScalarPair l E F (j.comp ι) X P)
            (Prod.mkHom
              (((sfRationalScalarComp l E L ι X 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).inv.app P.obj.1.unop).op)
              ((sfRationalScalarComp l E L ι X 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app P.obj.2))) =
        (sfRationalScalarComp l E L ι X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app
            ((rationalDerivedInternalHom l E X).obj P) ≫
          (rationalHomScalarComparison l E F (j.comp ι) X P).hom := by
  let P₀ := integralPairOfRationalHomPair l E X P
  have h₁ := (rationalHomScalarComparison_existsUnique l E L ι X P).exists.choose_spec
  have h₁' := mapHeq (sfRationalScalarExtension l L X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j)
    (by rw [scalarObj, homObj]; rfl)
    (by rw [homObj, scalarPair]; rfl) h₁
  have h₁'' := h₁'.trans (scalarMap l L F j X
    (integralHomScalarComparison l E L ι X P₀).hom)
  have h₂ := (rationalHomScalarComparison_existsUnique l L F j X
    (rationalHomScalarPair l E L ι X P)).exists.choose_spec
  have h₂' := h₂.trans (depHeq
    (fun Q ↦ (sfRationalConstructibleLocalization l F X).map
      (integralHomScalarComparison l L F j X Q).hom) (scalarPair l E L ι X P))
  have h₃ := homMapTransport l F X
    (rationalHomScalarPair l L F j X (rationalHomScalarPair l E L ι X P))
    (rationalHomScalarPair l E F (j.comp ι) X P)
    (integralHomScalarPair l L F j X (integralHomScalarPair l E L ι X P₀))
    (integralHomScalarPair l E F (j.comp ι) X P₀)
    (by rw [scalarPair, scalarPair]) (scalarPair l E F (j.comp ι) X P)
    ((sfIntegralScalarComp l E L ι X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).inv.app P₀.obj.1.unop)
    ((sfIntegralScalarComp l E L ι X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app P₀.obj.2)
    _ _ (compInv l E L ι X F j P.obj.1.unop)
    ((sfRationalScalarComp_existsUnique l E L ι X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).exists.choose_spec P.obj.2)
  have h₄ := appHeq (sfRationalScalarComp l E L ι X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom (homObj l E X P)
  have h₄' := h₄.trans ((sfRationalScalarComp_existsUnique l E L ι X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).exists.choose_spec
      ⟨(constructibleIntegralHom l E X).obj P₀⟩)
  have h₅ := (rationalHomScalarComparison_existsUnique l E F (j.comp ι) X P).exists.choose_spec
  have hleft := compHeq
    (by
      rw [scalarObj, scalarObj, homObj]
      rfl)
    (by rw [scalarObj, homObj, scalarPair]; rfl)
    (by rw [homObj, scalarPair, scalarPair]; rfl) h₁'' h₂'
  have hleft' := compHeq
    (by
      rw [scalarObj, scalarObj, homObj]
      rfl)
    (by rw [homObj, scalarPair, scalarPair]; rfl)
    (by rw [homObj, scalarPair]; rfl) hleft h₃
  have hright := compHeq
    (by
      try dsimp only [Functor.comp_obj]
      rw [scalarObj, scalarObj, homObj]
      rfl)
    (by rw [scalarObj, homObj]; rfl)
    (by rw [homObj, scalarPair]; rfl) h₄' h₅
  have hi := congrArg (fun f ↦ (sfRationalConstructibleLocalization l F X).map f)
    (integralHomTower l E L ι X P₀ F j)
  simp only [Functor.map_comp, ← Category.assoc] at hi
  simp only [← Category.assoc]
  with_unfolding_all exact eq_of_heq (hleft'.trans ((heq_of_eq hi).trans hright.symm))
end WeilConjectures
