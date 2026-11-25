/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportClauses
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismPullbackRawStage
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # A step of normalized isomorphism transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option linter.privateModule false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
namespace WeilConjectures

open scoped TensorProduct

section LinearExtension
universe r a b c d
variable {A : Type r} [CommRing A]
  {C : Type a} [Category.{b} C] [Preadditive C] [Linear A C]
  {D : Type c} [Category.{d} D] [Preadditive D] [Linear A D]

private abbrev linearExtension (t : A) (F : C ⥤ D) [F.Additive] [F.Linear A] :=
  ScalarLocalization.extension t t (RingHom.id A)
    (IsLocalization.Away.algebraMap_isUnit t) F (fun _ _ a f ↦ F.map_smul a f)

private theorem linearExtension_tmul (t : A) (F : C ⥤ D) [F.Additive] [F.Linear A]
    (K M : C) (a : Localization.Away t) (f : K ⟶ M) :
    (linearExtension t F).map
      (a ⊗ₜ[A] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk M) =
      a ⊗ₜ[A] F.map f := by
  have hc : ScalarLocalization.coefficientMap t t (RingHom.id A)
      (IsLocalization.Away.algebraMap_isUnit t) = RingHom.id (Localization.Away t) := by
    symm
    apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).1
    rfl
  change ScalarLocalization.extensionHom _ _ _ _ _ _ _ _ _ = _
  unfold ScalarLocalization.extensionHom
  rw [(ScalarLocalization.existsUnique_semilinearHom t t (RingHom.id A)
    (IsLocalization.Away.algebraMap_isUnit t) F
    (fun _ _ a f ↦ F.map_smul a f) K M).exists.choose_spec a f, hc]
  rfl

private theorem add_naturality
    {C' D' : Type*} [Category* C'] [Category* D'] [Preadditive C'] [Preadditive D']
    {U V : C' ⥤ D'} [U.Additive] [V.Additive] {K M : C'}
    (a : U.obj K ⟶ V.obj K) (b : U.obj M ⟶ V.obj M) (f g : K ⟶ M)
    (hf : U.map f ≫ b = a ≫ V.map f) (hg : U.map g ≫ b = a ≫ V.map g) :
    U.map (f + g) ≫ b = a ≫ V.map (f + g) := by
  simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

private def linearExtensionCounit (t : A) (F : C ⥤ D) (G : D ⥤ C)
    [F.Additive] [F.Linear A] [G.Additive] [G.Linear A] (e : F ⋙ G ≅ 𝟭 C) :
    linearExtension t F ⋙ linearExtension t G ≅ 𝟭 (ScalarLocalization A C t) :=
  NatIso.ofComponents
    (fun K ↦ (ScalarLocalization.localization A C t).mapIso (e.app K.obj)) (by
      intro K M f
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        change (linearExtension t G).map ((linearExtension t F).map (a ⊗ₜ[A] f)) ≫
            (ScalarLocalization.localization A C t).map (e.hom.app M.obj) =
          (ScalarLocalization.localization A C t).map (e.hom.app K.obj) ≫ (a ⊗ₜ[A] f)
        rw [linearExtension_tmul, linearExtension_tmul]
        change ScalarLocalization.composition A C t _ _ _
            (1 ⊗ₜ[A] e.hom.app M.obj) (a ⊗ₜ[A] (F ⋙ G).map f) =
          ScalarLocalization.composition A C t _ _ _
            (a ⊗ₜ[A] f) (1 ⊗ₜ[A] e.hom.app K.obj)
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one,
          e.hom.naturality, Functor.id_map]
      | add f g hf hg =>
        exact add_naturality
          (U := linearExtension t F ⋙ linearExtension t G) (V := 𝟭 _)
          ((ScalarLocalization.localization A C t).map (e.hom.app K.obj))
          ((ScalarLocalization.localization A C t).map (e.hom.app M.obj)) f g hf hg)

end LinearExtension

open scoped TensorProduct

private theorem inverse_normalized {C : Type*} [Category* C] {K M : C}
    (e : K ≅ M) (f : M ≅ K) (h : e.hom = f.inv) : e.inv = f.hom := by
  apply (cancel_mono e.hom).1
  calc
    e.inv ≫ e.hom = 𝟙 M := e.inv_hom_id
    _ = f.hom ≫ e.hom := by rw [h]; exact f.hom_inv_id.symm

section FiniteStage
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
  (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))

include hX hY in
private theorem integralCounit :
    ∃ e : constructibleIntegralPullback l E g ⋙ constructibleIntegralPullback l E (inv g) ≅
        𝟭 (sfIntegralConstructibleCategory l E Y),
      ∀ K, HEq (e.hom.app K).hom (pullbackIdentityEpsilon l E g K).hom := by
  obtain ⟨_, e, he, _, _, _, _⟩ := isomorphismPullbackRawStage l E g hX hY
  obtain ⟨_, ei, hei, _, _, _, _⟩ := isomorphismPullbackRawStage l E (inv g) hY hX
  let P := constructibleIntegralPullback l E g
  let Q := constructibleIntegralPullback l E (inv g)
  let I := (sfIntegralConstructible l E Y).ι
  let J := (sfIntegralConstructible l E X).ι
  let G := inverseImageIntegralDerived l E g
  let H := inverseImageIntegralDerived l E (inv g)
  let c : (P ⋙ Q) ⋙ I ≅ I :=
    Functor.associator P Q I ≪≫ Functor.isoWhiskerLeft P ei.symm ≪≫
      (Functor.associator P J H).symm ≪≫ Functor.isoWhiskerRight e.symm H ≪≫
      Functor.associator I G H ≪≫
      Functor.isoWhiskerLeft I (pullbackIdentityInverseImageCounit l E g) ≪≫
      I.rightUnitor
  refine ⟨NatIso.ofComponents (fun K ↦ (sfIntegralConstructible l E Y).isoMk (c.app K))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact c.hom.naturality f), ?_⟩
  intro K
  have hg (M : sfIntegralConstructibleCategory l E Y) :
      e.inv.app M = (pullbackIdentityLambda l E g hX hY M).hom :=
    inverse_normalized (e.app M) (pullbackIdentityLambda l E g hX hY M)
      (eq_of_heq (he M))
  have hi (M : sfIntegralConstructibleCategory l E X) :
      ei.inv.app M = (pullbackIdentityLambda l E (inv g) hY hX M).hom :=
    inverse_normalized (ei.app M) (pullbackIdentityLambda l E (inv g) hY hX M)
      (eq_of_heq (hei M))
  change HEq (c.hom.app K) (pullbackIdentityEpsilon l E g K).hom
  dsimp only [c, Iso.trans_hom, Iso.app_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_hom_app,
    NatTrans.comp_app, Iso.symm_hom, Functor.comp_map]
  simp only [hg, hi]
  dsimp only [P, Q, I, J, G, H, Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [Category.id_comp]
  have ht : (pullbackIdentityInverseImageCounit l E g).hom.app K.obj ≫ 𝟙 K.obj =
      (pullbackIdentityInverseImageCounit l E g).hom.app K.obj := Category.comp_id _
  rw [ht]
  exact HEq.rfl

omit [IsIso g] in
private theorem rational_eq [(constructibleIntegralPullback l E g).Additive]
    [(constructibleIntegralPullback l E g).Linear (Padic.coefficientExtensionIntegers l E)] :
    rationalDerivedPullback l E g =
      linearExtension (Padic.coefficientExtensionUniformizer l E)
        (constructibleIntegralPullback l E g) := by
  apply (rationalDerivedPullback_existsUnique l E g).unique
  · exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec
  · refine ⟨inferInstance, fun _ ↦ rfl, fun K M f a ↦ ?_⟩
    exact heq_of_eq (linearExtension_tmul _ _ K M a f)

private theorem rationalCounit
    [(constructibleIntegralPullback l E g).Additive]
    [(constructibleIntegralPullback l E g).Linear (Padic.coefficientExtensionIntegers l E)]
    [(constructibleIntegralPullback l E (inv g)).Additive]
    [(constructibleIntegralPullback l E (inv g)).Linear
      (Padic.coefficientExtensionIntegers l E)]
    (e : constructibleIntegralPullback l E g ⋙ constructibleIntegralPullback l E (inv g) ≅
      𝟭 (sfIntegralConstructibleCategory l E Y)) :
    ∃ er : rationalDerivedPullback l E g ⋙ rationalDerivedPullback l E (inv g) ≅
        𝟭 (sfRationalConstructibleCategory l E Y),
      ∀ K, HEq (er.hom.app K)
        ((sfRationalConstructibleLocalization l E Y).map (e.hom.app K.obj)) := by
  rw [rational_eq l E g, rational_eq l E (inv g)]
  exact ⟨linearExtensionCounit _ _ _ e, fun _ ↦ HEq.rfl⟩

end FiniteStage

/-- Normalized inverse transport at one finite coefficient field.
Source: the inverse automorphism paragraph of the current blueprint,
sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md;
steps 1, 2 and 4 of lem-pod-isomorphism-field-transport.
(blueprint: lem-pod-isomorphism-field-transport-finite-stage).

Proof: the completed coefficient map is the limit lift of its quotient components.
The module inverse images along g and its inverse have the section-normalized
counits, and therefore are additive exact equivalences. Derive them termwise.
Use the normalized inverse-image comparison supplied by isomorphismPullbackRawStage;
its inverse is pullbackIdentityLambda. Compose lambda for the inverse, inverse image
of lambda for g, and the section-normalized derived counit. Naturality of these
three factors gives an integral counit with exactly pullbackIdentityEpsilon as
component. Exchange g and its inverse to obtain the other counit, hence an equivalence.
Retain the integral shift, linearity and exactness supplied by the raw-stage theorem.
Localize both functors and both counits with the identity coefficient map. Balancing
and tensor induction identify these functors with rationalDerivedPullback on every
arrow, and localize the integral epsilon components. The localized counits give the
rational equivalence. Retain the normalized rational shift and exactness of the
raw-stage theorem. Empty schemes and torsion arrows are included in these arguments.
-/
theorem isomorphismFieldTransportFiniteStage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (IsomorphismFieldTransportStage l E g hX hY) := by
  obtain ⟨s, e, he, hs, hlin, _, sr, hsr, htr, _⟩ :=
    isomorphismPullbackRawStage l E g hX hY
  obtain ⟨si, _, _, hsInv, hlinInv, _, _⟩ :=
    isomorphismPullbackRawStage l E (inv g) hY hX
  let := s
  let := sr
  let := hs.1
  let := hs.2
  let := si
  let := hsInv.2
  let := hlin
  let := hlinInv
  let : (constructibleIntegralPullback l E g).Additive := inferInstance
  let : (constructibleIntegralPullback l E (inv g)).Additive := inferInstance
  have : (constructibleIntegralPullback l E (inv (inv g))).Linear
      (Padic.coefficientExtensionIntegers l E) := by simpa only [IsIso.inv_inv] using hlin
  have : (constructibleIntegralPullback l E (inv (inv g))).Additive :=
    by simpa only [IsIso.inv_inv] using
      (inferInstance : (constructibleIntegralPullback l E g).Additive)
  obtain ⟨ε, hε⟩ := integralCounit l E g hX hY
  obtain ⟨εi, _⟩ := integralCounit l E (inv g) hY hX
  obtain ⟨εr, hεr⟩ := rationalCounit l E g ε
  obtain ⟨εri, _⟩ := rationalCounit l E (inv g) εi
  let εm := pullbackIdentityModuleCounit l E g
  let εmi : inverseImageIntegralModules l E (inv g) ⋙ inverseImageIntegralModules l E g ≅
      𝟭 (integralTowerModules l E X) := by
    simpa only [IsIso.inv_inv] using pullbackIdentityModuleCounit l E (inv g)
  have hm := (CategoryTheory.Equivalence.mk (inverseImageIntegralModules l E g)
    (inverseImageIntegralModules l E (inv g)) εm.symm εmi).isEquivalence_functor
  have hi := (CategoryTheory.Equivalence.mk (constructibleIntegralPullback l E g)
    (constructibleIntegralPullback l E (inv g)) ε.symm
    (by simpa only [IsIso.inv_inv] using εi)).isEquivalence_functor
  have hr := (CategoryTheory.Equivalence.mk (rationalDerivedPullback l E g)
    (rationalDerivedPullback l E (inv g)) εr.symm
    (by simpa only [IsIso.inv_inv] using εri)).isEquivalence_functor
  have hspec := (rationalDerivedPullback_existsUnique l E g).exists.choose_spec
  change (rationalDerivedPullback l E g).Additive ∧ _ at hspec
  refine ⟨{
    coefficient_projection := ?_
    moduleEquivalence := hm
    moduleAdditive := inferInstance
    moduleLimits := inferInstance
    moduleColimits := inferInstance
    moduleEpsilon := εm
    module_epsilon_formula := fun _ ↦ rfl
    integralEquivalence := hi
    integralShift := s
    lambda := e.symm
    lambda_formula := ?_
    lambda_shift := inferInstance
    integralExact := hs.2
    integralLinear := hlin
    epsilon := ε
    epsilon_formula := hε
    rationalEquivalence := hr
    rationalShift := sr
    rational_shift_formula := hsr
    rationalExact := htr
    rationalAdditive := hspec.1
    rational_object := hspec.2.1
    rational_tensor := hspec.2.2
    rationalEpsilon := εr
    rational_epsilon_formula := hεr }⟩
  · intro n
    simp only [inverseImageCompletedCoefficientMap, limit.lift_π]
  · intro K
    exact heq_of_eq (inverse_normalized (e.app K)
      (pullbackIdentityLambda l E g hX hY K) (eq_of_heq (he K)))

end WeilConjectures
