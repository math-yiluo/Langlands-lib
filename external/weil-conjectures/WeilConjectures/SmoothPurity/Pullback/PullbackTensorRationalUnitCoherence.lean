/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitCoherence

/-! Rational unit coherence for the completed pullback tensor comparison.

Source: Stacks Project, Tags 07A4 and 0941; the rational part of
`lem-pur-pullback-tensor-unit-coherence`.
(blueprint: lem-pur-pullback-tensor-rational-unit-coherence)

The proof localizes the integral unit comparison and transports the normalized
left and right unitor equations. The localized comparison is unique by the
same unit cancellation argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField Padic
  sfIntegralConstructible HasDerivedCategory.standard

private theorem chosen_spec {A : Sort*} {p : A → Prop}
    (h : ∃! a, p a) (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

-- Naturality descends through the specified tensor and unit reduction maps.
private theorem reducedLeftUnitor_natural
    {C D : Type*} [Category* C] [Category* D]
    (Q : C ⥤ D) [Q.Faithful] (T : C × C ⥤ C) (S : D × D ⥤ D)
    (b : T ⋙ Q ≅ (Q.prod Q) ⋙ S) (U : C) (V : D) (e : Q.obj U ≅ V)
    (lu : ∀ M, S.obj (V, M) ≅ M)
    (hn : ∀ {M N} (f : M ⟶ N),
      S.map (Prod.mkHom (𝟙 V) f) ≫ (lu N).hom = (lu M).hom ≫ f)
    (li : ∀ M, T.obj (U, M) ≅ M)
    (hi : ∀ M, Q.map (li M).hom = b.hom.app (U, M) ≫
      S.map (Prod.mkHom e.hom (𝟙 _)) ≫ (lu (Q.obj M)).hom)
    {M N : C} (f : M ⟶ N) :
    T.map (Prod.mkHom (𝟙 U) f) ≫ (li N).hom = (li M).hom ≫ f := by
  have hb := b.hom.naturality (Prod.mkHom (𝟙 U) f)
  change Q.map (T.map (Prod.mkHom (𝟙 U) f)) ≫ b.hom.app (U, N) =
    b.hom.app (U, M) ≫ S.map (Prod.mkHom (Q.map (𝟙 U)) (Q.map f)) at hb
  apply Q.map_injective
  simp only [Functor.map_comp, hi, Category.assoc]
  rw [← Category.assoc, hb, Q.map_id]
  simp only [Category.assoc]
  have hs : S.map (Prod.mkHom (𝟙 (Q.obj U)) (Q.map f)) ≫
      S.map (Prod.mkHom e.hom (𝟙 (Q.obj N))) =
    S.map (Prod.mkHom e.hom (𝟙 (Q.obj M))) ≫
      S.map (Prod.mkHom (𝟙 V) (Q.map f)) := by
    simp only [← S.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  rw [reassoc_of% hs, hn]

-- Tensoring by an object isomorphic to the unit is faithful.
private theorem unitIso_unique
    {C : Type*} [Category* C] (T : C × C ⥤ C) (U A : C)
    (lu : ∀ M, T.obj (U, M) ≅ M)
    (hn : ∀ {M N} (f : M ⟶ N),
      T.map (Prod.mkHom (𝟙 U) f) ≫ (lu N).hom = (lu M).hom ≫ f)
    (j k : A ≅ U)
    (h : T.map (Prod.mkHom (𝟙 A) j.hom) =
      T.map (Prod.mkHom (𝟙 A) k.hom)) : j = k := by
  have ht := congrArg (fun z ↦ T.map (Prod.mkHom j.inv (𝟙 A)) ≫ z ≫
    T.map (Prod.mkHom j.hom (𝟙 U))) h
  simp only [← T.map_comp, prod_comp, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id] at ht
  have he := congrArg (fun z ↦ z ≫ (lu U).hom) ht
  rw [hn, hn] at he
  exact Iso.ext ((cancel_epi (lu A).hom).mp he)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem integralLeftUnitor_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N : sfIntegralConstructibleCategory l E W} (f : M ⟶ N) :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom (𝟙 (pullbackTensorIntegralUnit l E W)) f) ≫
        (pullbackTensorIntegralLeftUnitor l E W N).hom =
      (pullbackTensorIntegralLeftUnitor l E W M).hom ≫ f := by
  have := (coherentReduction_fullyFaithful l E W).2
  apply reducedLeftUnitor_natural (coherentReduction l E W)
    (constructibleIntegralTensor l E W) (pullbackTensorCalculus l E W).systemClosed.tensor
    (reduction_tensor l E W) (pullbackTensorIntegralUnit l E W) _
    (pullbackTensorIntegralUnitReduction l E W)
    (pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
  · intro M N f
    let := (pullbackTensorCalculus l E W).systemClosed.monoidal
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.id_tensorHom] using MonoidalCategory.leftUnitor_naturality f
  · intro M
    exact (pullbackTensorIntegralLeftUnitor_existsUnique l E W M).exists.choose_spec

private theorem rationalLeftUnitor_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N : sfRationalConstructibleCategory l E W} (f : M ⟶ N) :
    (rationalDerivedTensor l E W).map
        (Prod.mkHom (𝟙 (pullbackTensorRationalUnit l E W)) f) ≫
        (pullbackTensorRationalLeftUnitor l E W N).hom =
      (pullbackTensorRationalLeftUnitor l E W M).hom ≫ f := by
  let T := rationalDerivedTensor l E W
  let I := constructibleIntegralTensor l E W
  let R := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  let U := pullbackTensorRationalUnit l E W
  let U₀ := pullbackTensorIntegralUnit l E W
  have spec := chosen_spec (rationalDerivedTensor_existsUnique l E W) T rfl
  have ho (MN : sfRationalConstructibleCategory l E W ×
      sfRationalConstructibleCategory l E W) :
      T.obj MN = ScalarLocalization.mk (I.obj (MN.1.obj, MN.2.obj)) := spec.1 MN
  obtain ⟨b, hb, hp⟩ := spec.2 U U M N
  change T.map (Prod.mkHom (𝟙 U) f) ≫ _ = _
  rw [hb]
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    change (b (𝟙 U)) (f + g) ≫ _ = _ ≫ (f + g)
    rw [map_add, Preadditive.add_comp]
    rw [hf, hg]
    exact (Preadditive.comp_add _ _ _
      (pullbackTensorRationalLeftUnitor l E W M).hom f g).symm
  | tmul a f =>
    have ht : HEq (b (𝟙 U) (a ⊗ₜ[R] f))
        ((1 * a) ⊗ₜ[R] I.map (Prod.mkHom (𝟙 U₀) f)) := hp (𝟙 U₀) f 1 a
    have hL := (pullbackTensorRationalLeftUnitor_existsUnique l E W N).exists.choose_spec
    have hM := (pullbackTensorRationalLeftUnitor_existsUnique l E W M).exists.choose_spec
    have hl := heq_comp (ho (U, M)) (ho (U, N)) rfl ht hL
    have hr := heq_comp (ho (U, M)) rfl rfl hM (HEq.rfl (a := a ⊗ₜ[R] f))
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ScalarLocalization.composition R _ p _ _ _
        (1 ⊗ₜ[R] (pullbackTensorIntegralLeftUnitor l E W N.obj).hom)
        ((1 * a) ⊗ₜ[R] I.map (Prod.mkHom (𝟙 U₀) f)) =
      ScalarLocalization.composition R _ p _ _ _ (a ⊗ₜ[R] f)
        (1 ⊗ₜ[R] (pullbackTensorIntegralLeftUnitor l E W M.obj).hom)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    rw [integralLeftUnitor_natural l E W f]

theorem pullbackTensorRationalUnitCoherence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    canonicalRationalPullbackTensor_unit l E f := by
  let F := rationalDerivedPullback l E f
  let I := constructibleIntegralPullback l E f
  let Q := sfRationalConstructibleLocalization l E X
  let QY := sfRationalConstructibleLocalization l E Y
  let U := pullbackTensorRationalUnit l E Y
  let UX := pullbackTensorIntegralUnit l E X
  have fspec := chosen_spec (rationalDerivedPullback_existsUnique l E f) F rfl
  have hF (K) : F.obj K = Q.obj (I.obj K.obj) := fspec.2.1 K
  have hTY (MN) : (rationalDerivedTensor l E Y).obj MN =
      QY.obj ((constructibleIntegralTensor l E Y).obj (MN.1.obj, MN.2.obj)) :=
    (chosen_spec (rationalDerivedTensor_existsUnique l E Y)
      (rationalDerivedTensor l E Y) rfl).1 MN
  have hTX (MN) : (rationalDerivedTensor l E X).obj MN =
      Q.obj ((constructibleIntegralTensor l E X).obj (MN.1.obj, MN.2.obj)) :=
    (chosen_spec (rationalDerivedTensor_existsUnique l E X)
      (rationalDerivedTensor l E X) rfl).1 MN
  -- Localize the integral unit comparison, retaining its prescribed hom.
  obtain ⟨εI, hI, _⟩ := pullbackTensorIntegralUnitCoherence l E f
  obtain ⟨ε, hε, _⟩ := existsUnique_iso_of_eq (hF U) rfl (Q.mapIso εI)
  change ∃! ε : F.obj U ≅ Q.obj UX, _
  have equations : ∀ M,
      ((canonicalRationalPullbackTensor l E f U M).hom ≫
        (rationalDerivedTensor l E X).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        (pullbackTensorRationalLeftUnitor l E X (F.obj M)).hom =
        F.map (pullbackTensorRationalLeftUnitor l E Y M).hom) ∧
      ((canonicalRationalPullbackTensor l E f M U).hom ≫
        (rationalDerivedTensor l E X).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        (pullbackTensorRationalRightUnitor l E X (F.obj M)).hom =
        F.map (pullbackTensorRationalRightUnitor l E Y M).hom) := by
    intro M
    have hbase : (F.obj M).obj = I.obj M.obj := by rw [hF]; rfl
    have hid : HEq (𝟙 (F.obj M)) (Q.map (𝟙 (I.obj M.obj))) := by
      have hh {A : sfRationalConstructibleCategory l E X}
          {B : sfIntegralConstructibleCategory l E X} (h : A = Q.obj B) :
          HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
      exact hh (hF M)
    have htmap {A B C D : sfRationalConstructibleCategory l E X}
        {A' B' C' D' : sfIntegralConstructibleCategory l E X}
        (hA : A = Q.obj A') (hB : B = Q.obj B')
        (hC : C = Q.obj C') (hD : D = Q.obj D')
        (a : A ⟶ B) (b : C ⟶ D) (a' : A' ⟶ B') (b' : C' ⟶ D')
        (ha : HEq a (Q.map a')) (hb : HEq b (Q.map b')) :
        HEq ((rationalDerivedTensor l E X).map (Prod.mkHom a b))
          (Q.map ((constructibleIntegralTensor l E X).map (Prod.mkHom a' b'))) := by
      subst A B C D
      have ha' := eq_of_heq ha
      have hb' := eq_of_heq hb
      subst a b
      obtain ⟨bil, hbil, hbil'⟩ :=
        (chosen_spec (rationalDerivedTensor_existsUnique l E X)
          (rationalDerivedTensor l E X) rfl).2
          (Q.obj A') (Q.obj B') (Q.obj C') (Q.obj D')
      rw [hbil]
      convert hbil' a' b' 1 1 using 1
      simp only [one_mul]
      rfl
    have hmap {A B : sfRationalConstructibleCategory l E Y}
        {A' B' : sfIntegralConstructibleCategory l E Y}
        (hA : A = QY.obj A') (hB : B = QY.obj B')
        (a : A ⟶ B) (b : A' ⟶ B') (hab : HEq a (QY.map b)) :
        HEq (F.map a) (Q.map (I.map b)) :=
      map_localized_heq I F QY Q (fun c ↦ fspec.2.2 _ _ c 1) hA hB a b hab
    constructor
    · have hc := (canonicalRationalPullbackTensor_existsUnique l E f U M).exists.choose_spec
      have ht := htmap (hF U) rfl (hF M) (hF M) ε.hom (𝟙 _) εI.hom (𝟙 _) hε hid
      have hu := (pullbackTensorRationalLeftUnitor_existsUnique l E X
        (F.obj M)).exists.choose_spec
      have hcongr {A B : sfIntegralConstructibleCategory l E X} (h : A = B) :
          HEq (Q.map (pullbackTensorIntegralLeftUnitor l E X A).hom)
            (Q.map (pullbackTensorIntegralLeftUnitor l E X B).hom) := by subst B; rfl
      have hu' := hu.trans (hcongr hbase)
      have htail := heq_comp (by rw [hTX, hF, hF]; rfl)
        (by rw [hTX, hF]; rfl) (hF M) ht hu'
      have hleft := heq_comp (by rw [hF, hTY]; rfl)
        (by rw [hTX, hF, hF]; rfl) (hF M) hc htail
      have hright := hmap (hTY (U, M)) rfl _ _
        (pullbackTensorRationalLeftUnitor_existsUnique l E Y M).exists.choose_spec
      apply eq_of_heq
      refine hleft.trans ((heq_of_eq ?_).trans hright.symm)
      have h := congrArg Q.map (hI M.obj).1
      simp only [Functor.map_comp] at h
      convert h using 1
      rfl
    · have hc := (canonicalRationalPullbackTensor_existsUnique l E f M U).exists.choose_spec
      have ht := htmap (hF M) (hF M) (hF U) rfl (𝟙 _) ε.hom (𝟙 _) εI.hom hid hε
      have hu := (pullbackTensorRationalRightUnitor_existsUnique l E X
        (F.obj M)).exists.choose_spec
      have hcongr {A B : sfIntegralConstructibleCategory l E X} (h : A = B) :
          HEq (Q.map (pullbackTensorIntegralRightUnitor l E X A).hom)
            (Q.map (pullbackTensorIntegralRightUnitor l E X B).hom) := by subst B; rfl
      have hu' := hu.trans (hcongr hbase)
      have htail := heq_comp (by rw [hTX, hF, hF]; rfl)
        (by rw [hTX, hF]; rfl) (hF M) ht hu'
      have hleft := heq_comp (by rw [hF, hTY]; rfl)
        (by rw [hTX, hF, hF]; rfl) (hF M) hc htail
      have hright := hmap (hTY (M, U)) rfl _ _
        (pullbackTensorRationalRightUnitor_existsUnique l E Y M).exists.choose_spec
      apply eq_of_heq
      refine hleft.trans ((heq_of_eq ?_).trans hright.symm)
      have h := congrArg Q.map (hI M.obj).2
      simp only [Functor.map_comp] at h
      convert h using 1
      rfl
  refine ⟨ε, equations, ?_⟩
  intro ε' hε'
  -- The right equation at the unit fixes its tensor with pullback of the unit.
  have he := ((hε' U).2).trans (equations U).2.symm
  have ht : (rationalDerivedTensor l E X).map (Prod.mkHom (𝟙 (F.obj U)) ε'.hom) =
        (rationalDerivedTensor l E X).map (Prod.mkHom (𝟙 (F.obj U)) ε.hom) := by
    apply (cancel_mono (pullbackTensorRationalRightUnitor l E X (F.obj U)).hom).mp
    apply (cancel_epi (canonicalRationalPullbackTensor l E f U U).hom).mp
    convert he using 1 <;> rfl
  exact unitIso_unique (rationalDerivedTensor l E X) (pullbackTensorRationalUnit l E X)
    (F.obj U) (pullbackTensorRationalLeftUnitor l E X)
    (fun g ↦ rationalLeftUnitor_natural l E X g) ε' ε ht

end WeilConjectures
