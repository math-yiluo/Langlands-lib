/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations

/-! The naturality clause for the specified rational Hom comparison.
Source: blueprint common-stage paragraph (blueprint: lem-zl-specified-hom-scalar-evaluation).
This is the rationalized naturality calculation for arbitrary localized arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u

attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralDerivedInternalHom WeilConjectures.integralScalarExtension
  WeilConjectures.sfRationalScalarExtension
  WeilConjectures.scalarHomOrdinary

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules TensorProduct
namespace WeilConjectures

attribute [local irreducible] rationalDerivedInternalHom rationalHomScalarComparison
attribute [local implicit_reducible] rationalHomScalarPair

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem chosen_spec {A : Sort*} {p : A → Prop} (h : ∃! a, p a)
    (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (hf : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hA; cases hB; cases hf
  rfl

private theorem hom_map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    {q : ObjectProperty (Cᵒᵖ × C)} (F : q.FullSubcategory ⥤ D)
    {P Q P' Q' : q.FullSubcategory} (hP : P = P') (hQ : Q = Q')
    {a : Q.obj.1.unop ⟶ P.obj.1.unop} {b : P.obj.2 ⟶ Q.obj.2}
    {a' : Q'.obj.1.unop ⟶ P'.obj.1.unop} {b' : P'.obj.2 ⟶ Q'.obj.2}
    (ha : HEq a a') (hb : HEq b b') :
    HEq (F.map (ObjectProperty.homMk (Prod.mkHom a.op b)))
      (F.map (ObjectProperty.homMk (Prod.mkHom a'.op b'))) := by
  cases hP; cases hQ; cases ha; cases hb
  rfl

private theorem integral_naturality (X : Scheme.{u})
    (P P' : (constructibleIntegralHomPairs l E X).FullSubcategory)
    (a : P'.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ P'.obj.2) :
    (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map
      ((constructibleIntegralHom l E X).map
        (ObjectProperty.homMk (X := P) (Y := P') (Prod.mkHom a.op b))) ≫
      (integralHomScalarComparison l E L ι X P').hom =
    (integralHomScalarComparison l E L ι X P).hom ≫
      (constructibleIntegralHom l L X).map
        (ObjectProperty.homMk
          (X := integralHomScalarPair l E L ι X P)
          (Y := integralHomScalarPair l E L ι X P')
          (Prod.mkHom
            (((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map a).op)
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map b))) := by
  apply ObjectProperty.hom_ext
  let O := integralOrdinaryDerivedScalar l E L ι X
  let T := integralScalarExtension l E L ι X
  let HE := integralDerivedInternalHom l E X
  let HL := integralDerivedInternalHom l L X
  let c := scalarCompletion l E L ι X
  let e (K : sfIntegralConstructibleCategory l E X) :=
    scalarCompletionIso l E L ι X K.obj K.property.1
  let h (Q : (constructibleIntegralHomPairs l E X).FullSubcategory) :=
    scalarCompletionIso l E L ι X (HE.obj (op Q.obj.1.unop.obj, Q.obj.2.obj)) Q.property.1
  have hc : T.map (HE.map (Prod.mkHom a.hom.op b.hom)) ≫ (h P').inv =
      (h P).inv ≫ O.map (HE.map (Prod.mkHom a.hom.op b.hom)) := by
    have hn : O.map (HE.map (Prod.mkHom a.hom.op b.hom)) ≫ (h P').hom =
        (h P).hom ≫ T.map (HE.map (Prod.mkHom a.hom.op b.hom)) :=
      c.naturality _
    apply (cancel_epi (h P).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun f ↦ f ≫ (h P').inv) hn.symm
  have ha : (e P'.obj.1.unop).inv ≫ O.map a.hom =
      T.map a.hom ≫ (e P.obj.1.unop).inv := by
    have hn : O.map a.hom ≫ (e P.obj.1.unop).hom =
        (e P'.obj.1.unop).hom ≫ T.map a.hom := c.naturality _
    apply (cancel_epi (e P'.obj.1.unop).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun f ↦ f ≫ (e P.obj.1.unop).inv) hn
  have hb : O.map b.hom ≫ (e P'.obj.2).hom =
      (e P.obj.2).hom ≫ T.map b.hom := c.naturality b.hom
  have hd : HL.map (Prod.mkHom (O.map a.hom).op (O.map b.hom)) ≫
        HL.map (Prod.mkHom (e P'.obj.1.unop).inv.op (e P'.obj.2).hom) =
      HL.map (Prod.mkHom (e P.obj.1.unop).inv.op (e P.obj.2).hom) ≫
        HL.map (Prod.mkHom (T.map a.hom).op (T.map b.hom)) := by
    rw [← HL.map_comp, ← HL.map_comp]
    congr 1
    apply Prod.hom_ext
    · exact congrArg Quiver.Hom.op ha
    · exact hb
  change T.map (HE.map (Prod.mkHom a.hom.op b.hom)) ≫
      ((h P').inv ≫ scalarHomOrdinary l E L ι X _ _ ≫
        HL.map (Prod.mkHom (e P'.obj.1.unop).inv.op (e P'.obj.2).hom)) =
    ((h P).inv ≫ scalarHomOrdinary l E L ι X _ _ ≫
        HL.map (Prod.mkHom (e P.obj.1.unop).inv.op (e P.obj.2).hom)) ≫
      HL.map (Prod.mkHom (T.map a.hom).op (T.map b.hom))
  rw [← Category.assoc, hc]
  simp only [Category.assoc]
  rw [← Category.assoc (O.map _), scalarHomOrdinary_naturality]
  simp only [Category.assoc]
  rw [hd]

/-- Rational naturality of the specified Hom comparison for arbitrary localized arrows.
Source: blueprint rational/common-stage paragraphs
(blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: localize the integral comparison and use bilinearity of the rational internal Hom,
with contravariance in the first variable; the universal localization property extends
the equality from integral maps to all localized arrows. -/
theorem specifiedHomScalarRational_naturality (X : Scheme.{u})
    (P P' : (constructibleRationalHomPairs l E X).FullSubcategory)
    (a : P'.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ P'.obj.2) :
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((rationalDerivedInternalHom l E X).map
          (ObjectProperty.homMk (X := P) (Y := P') (Prod.mkHom a.op b))) ≫
      (rationalHomScalarComparison l E L ι X P').hom =
    (rationalHomScalarComparison l E L ι X P).hom ≫
      (rationalDerivedInternalHom l L X).map
        (ObjectProperty.homMk
          (X := rationalHomScalarPair l E L ι X P)
          (Y := rationalHomScalarPair l E L ι X P')
          (Prod.mkHom
            (((sfRationalScalarExtension l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map a).op)
            ((sfRationalScalarExtension l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map b))) := by
  let T := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X
  let F := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let HE := rationalDerivedInternalHom l E X
  let HL := rationalDerivedInternalHom l L X
  let IE := constructibleIntegralHom l E X
  let IL := constructibleIntegralHom l L X
  let Q := sfRationalConstructibleLocalization l L X
  let IP := integralPairOfRationalHomPair l E X
  let SP := rationalHomScalarPair l E L ι X
  let IS := integralHomScalarPair l E L ι X
  let c := (sfRationalCoefficientEquiv l L).symm.toRingHom.comp
    (ι.toRingHom.comp (sfRationalCoefficientEquiv l E).toRingHom)
  have hE (R : (constructibleRationalHomPairs l E X).FullSubcategory) :
      HE.obj R = ⟨IE.obj (IP R)⟩ :=
    by simpa only [HE, rationalDerivedInternalHom] using
      (rationalDerivedInternalHom_existsUnique l E X).exists.choose_spec.1 R
  have hL (R : (constructibleRationalHomPairs l L X).FullSubcategory) :
      HL.obj R = ⟨IL.obj (integralPairOfRationalHomPair l L X R)⟩ :=
    by simpa only [HL, rationalDerivedInternalHom] using
      (rationalDerivedInternalHom_existsUnique l L X).exists.choose_spec.1 R
  have hF (K : sfRationalConstructibleCategory l E X) :
      F.obj K = Q.obj (T.obj K.obj) :=
    sfRationalScalarExtension_obj l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι K
  let RP (R : (constructibleIntegralHomPairs l L X).FullSubcategory) :
      (constructibleRationalHomPairs l L X).FullSubcategory :=
    ⟨(op ⟨R.obj.1.unop⟩, ⟨R.obj.2⟩), R.property⟩
  have hSP (R : (constructibleRationalHomPairs l E X).FullSubcategory) :
      SP R = RP (IS (IP R)) := by
    apply ObjectProperty.FullSubcategory.ext
    change (op (F.obj R.obj.1.unop), F.obj R.obj.2) = _
    rw [hF, hF]
    rfl
  have hsrc R : F.obj (HE.obj R) = Q.obj (T.obj (IE.obj (IP R))) := by
    rw [hE, hF]
  have htgt R : HL.obj (SP R) = Q.obj (IL.obj (IS (IP R))) := by
    rw [hSP, hL]
    rfl
  have hcomp R : HEq (rationalHomScalarComparison l E L ι X R).hom
      (Q.map (integralHomScalarComparison l E L ι X (IP R)).hom) :=
    by delta rationalHomScalarComparison; exact
      (rationalHomScalarComparison_existsUnique l E L ι X R).exists.choose_spec
  have hsE := chosen_spec (rationalDerivedInternalHom_existsUnique l E X) HE
    (by unfold HE rationalDerivedInternalHom; rfl)
  have hsL := chosen_spec (rationalDerivedInternalHom_existsUnique l L X) HL
    (by unfold HL rationalDerivedInternalHom; rfl)
  obtain ⟨β, hβ, pβ⟩ := hsE.2 P P'
  obtain ⟨γ, hγ, pγ⟩ := hsL.2 (SP P) (SP P')
  change F.map (HE.map (ObjectProperty.homMk (Prod.mkHom a.op b))) ≫ _ =
    _ ≫ HL.map (ObjectProperty.homMk (X := SP P) (Y := SP P')
      (Prod.mkHom (F.map a).op (F.map b)))
  rw [hβ, hγ]
  induction a using TensorProduct.inductionOn with
  | add a a' ha ha' =>
    simp only [F.map_add, map_add, LinearMap.add_apply, Preadditive.add_comp,
      Preadditive.comp_add,
      ha, ha']
  | tmul x a =>
    induction b using TensorProduct.inductionOn with
    | add b b' hb hb' =>
      simp only [F.map_add, map_add, Preadditive.add_comp, Preadditive.comp_add, hb, hb']
    | tmul y b =>
      have hm := (map_heq F (hE P) (hE P') (pβ a b x y)).trans
        (sfRationalScalarExtension_map_tmul l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι _ _
          (IE.map (ObjectProperty.homMk (X := IP P) (Y := IP P')
            (Prod.mkHom a.op b))) (x*y))
      have hfa := sfRationalScalarExtension_map_tmul l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι _ _ a x
      have hfb := sfRationalScalarExtension_map_tmul l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι _ _ b y
      have hn := hom_map_heq HL (hSP P) (hSP P') hfa hfb
      obtain ⟨δ, hδ, pδ⟩ :=
        hsL.2 (RP (IS (IP P))) (RP (IS (IP P')))
      have hn' := (heq_of_eq (hγ (F.map (x ⊗ₜ[_] a))
        (F.map (y ⊗ₜ[_] b))).symm).trans hn
      have hd := pδ (T.map a) (T.map b) (c x) (c y)
      have hd' := (heq_of_eq (hδ _ _)).trans hd
      have hr := hn'.trans hd'
      have hleft := heq_comp (hsrc P) (hsrc P') (htgt P') hm (hcomp P')
      have hright := heq_comp (hsrc P) (htgt P) (htgt P') (hcomp P) hr
      apply eq_of_heq
      refine hleft.trans (HEq.trans ?_ hright.symm)
      apply heq_of_eq
      change ScalarLocalization.composition _ _ _ _ _ _
          (1 ⊗ₜ[_] (integralHomScalarComparison l E L ι X (IP P')).hom)
          (c (x*y) ⊗ₜ[_] T.map (IE.map
            (ObjectProperty.homMk (Prod.mkHom a.op b)))) =
        ScalarLocalization.composition _ _ _ _ _ _
          ((c x * c y) ⊗ₜ[_] IL.map
            (ObjectProperty.homMk (X := IS (IP P)) (Y := IS (IP P'))
              (Prod.mkHom (T.map a).op (T.map b))))
          (1 ⊗ₜ[_] (integralHomScalarComparison l E L ι X (IP P)).hom)
      simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, map_mul]
      exact congrArg (fun f ↦ (c x * c y) ⊗ₜ[Padic.coefficientExtensionIntegers l L] f)
        (integral_naturality l E L ι X (IP P) (IP P') a b)

end WeilConjectures
