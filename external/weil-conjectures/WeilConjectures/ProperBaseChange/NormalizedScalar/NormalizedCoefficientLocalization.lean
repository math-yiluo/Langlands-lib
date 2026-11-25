/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedCoefficientModel
public import Mathlib.CategoryTheory.Functor.OfSequence

import WeilConjectures.ProperBaseChange.NormalizedScalar.FieldModel.NormalizedCoefficientExact
import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedScalarActions

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralRegularTelescope
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Types.Filtered
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.ConstructibleSheaf.FreeLifting

/-! # Localization of the given-norm integral coefficient sheaf

The coefficient rings are the actual pulled-back continuous-function rings.
The small-field telescope is transported by the same isometric field map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Obj

open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing CategoryTheory.MonObj

namespace WeilConjectures.NormalizedScalar

/-- The regular integral coefficient module on X.
Source: the displayed sequence in the blueprint localization lemma
(blueprint: lem-weil-pbc-normalized-coefficient-localization). -/
abbrev regularIntegral (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :=
  Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj (integers ℓ E)) X)

/-- The existing coefficient ring E_X as an integral module along the specified inclusion φ.
Source: the blueprint localization lemma, first and last sentences
(blueprint: lem-weil-pbc-normalized-coefficient-localization). -/
abbrev restrictedField (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :=
  (Mod.comap (coefficientMap (scalarMap (l := ℓ) (E := E)) X)).obj
    (Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))

/-- The sequence of regular integral modules with transition multiplication by ℓ.
Source: the displayed sequence in the blueprint localization lemma
(blueprint: lem-weil-pbc-normalized-coefficient-localization). -/
abbrev ellSequence (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ℕ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj (integers ℓ E)) X) :=
  CategoryTheory.Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (regularIntegral X ℓ E))

private theorem scalar_colimit_hom_ext
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (p : ℕ) (M : C) (c : Cocone (CategoryTheory.Functor.ofSequence (fun _ ↦ p • 𝟙 M)))
    (hc : IsColimit c) (F : C ⥤ D) [F.Additive]
    [PreservesColimit (CategoryTheory.Functor.ofSequence (fun _ ↦ p • 𝟙 M)) F]
    {B : D} [IsIso (p • 𝟙 B)] (f g : F.obj c.pt ⟶ B)
    (hzero : F.map (c.ι.app 0) ≫ f = F.map (c.ι.app 0) ≫ g) : f = g := by
  apply (isColimitOfPreserves F hc).hom_ext
  intro n
  change F.map (c.ι.app n) ≫ f = F.map (c.ι.app n) ≫ g
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have hs : p • c.ι.app (n + 1) = c.ι.app n := by
      have h := c.w (homOfLE (Nat.le_succ n))
      rw [CategoryTheory.Functor.ofSequence_map_homOfLE_succ] at h
      change (p • 𝟙 M) ≫ (c.ι.app (n + 1) : M ⟶ c.pt) = c.ι.app n at h
      rw [Preadditive.nsmul_comp, Category.id_comp] at h
      exact h
    apply (cancel_mono (p • 𝟙 B)).1
    simp only [Preadditive.comp_nsmul, Category.comp_id,
      ← Preadditive.nsmul_comp, ← F.map_nsmul, hs]
    exact ih

/-- Multiplication by ell is invertible on actual field-coefficient modules.
Source: the nonzero constant field scalar ell.
(blueprint: lem-weil-pbc-normalized-coefficient-localization).
Proof: use multiplication by its inverse as the inverse endomorphism. -/
theorem field_nsmul_isIso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)) :
    IsIso (ℓ • 𝟙 M) := by
  let := modulesLinear E X
  have hp : (ℓ : E) ≠ 0 := by
    have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h
  let e : M ≅ M :=
    { hom := (ℓ : E) • 𝟙 M
      inv := (ℓ : E)⁻¹ • 𝟙 M
      hom_inv_id := by simp [Linear.comp_smul, smul_smul, hp]
      inv_hom_id := by simp [Linear.comp_smul, smul_smul, hp] }
  have he : e.hom = ℓ • 𝟙 M := by
    exact Nat.cast_smul_eq_nsmul E ℓ (𝟙 M)
  rw [← he]
  exact e.isIso_hom

/-- Localization of a ring object at an integer, stated by its initial map.
Source: the universal property of inverting a central integer.
(blueprint: lem-weil-pbc-normalized-coefficient-localization). -/
def RingLocalizationAt {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    (p : ℕ) {A B : C} [MonObj A] [MonObj B] (φ : A ⟶ B) : Prop :=
  IsIso (p • 𝟙 B) ∧
  ∀ (D : C) (_ : MonObj D) (_ : IsIso (p • 𝟙 D)) (g : A ⟶ D),
    IsMonHom g → ∃! f : B ⟶ D, IsMonHom f ∧ φ ≫ f = g

/-- The coefficient inclusion is the initial map of A_T[1/ell].
Source: sheaf localization, Bhatt--Scholze Lemma 6.8.2.
(blueprint: lem-weil-pbc-normalized-coefficient-localization). -/
def CoefficientLocalization (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] : Prop :=
  RingLocalizationAt ℓ (coefficientMap (scalarMap (l := ℓ) (E := E)) X)

/-- The ordinary regular coefficient telescope, transported to the original
finite normed field and its actual unit ball.
Source: the regular coefficient telescope and isometric coefficient transport.
(blueprint: lem-weil-pbc-normalized-coefficient-localization).
Proof: restrict the small-field telescope along the inverse integral coefficient
isomorphism. The field comparison identifies the target module. Colimit
preservation and the commuting coefficient square give the specified zeroth leg. -/
theorem regular_telescope (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ c : Cocone (ellSequence X ℓ E), Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ restrictedField X ℓ E,
        (c.ι.app 0 ≫ e.hom).hom = coefficientMap (scalarMap (l := ℓ) (E := E)) X := by
  obtain ⟨m⟩ := fieldModel_nonempty ℓ E
  obtain ⟨c, ⟨hc⟩, e, hz⟩ := integralRegularTelescope ℓ m.carrier X
  let a := m.integerIso X
  let b := m.fieldIso X
  let φ := coefficientMap (integralScalarMap ℓ m.carrier) X
  let ψ := coefficientMap (scalarMap (l := ℓ) (E := E)) X
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) a.inv
  let er : F.obj (Mod.regular (condensedRingObj (integralCoeff ℓ m.carrier) X)) ≅
      regularIntegral X ℓ E :=
    restrictedRegularIso a.inv (𝟙 _) a (by exact a.inv_hom_id) ≪≫
      (Mod.comapId _).app _
  let es : F.obj c.pt ≅ restrictedField X ℓ E :=
    F.mapIso e ≪≫ (Mod.comapComp a.inv φ).symm.app _ ≪≫
      restrictedRegularIso (a.inv ≫ φ) ψ b (by
        rw [Category.assoc, ← m.scalar_square_scheme X, Iso.inv_hom_id_assoc])
  apply transportRegularTelescope ℓ F c (isColimitOfPreserves F hc)
    er es (Mod.forget _) ψ
  change (c.ι.app 0 ≫ e.hom).hom ≫ b.hom = a.hom ≫ ψ
  rw [hz]
  exact (m.scalar_square_scheme X).symm

private theorem ring_localization_of_telescope
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] (p : ℕ) {A B : C} [MonObj A] [MonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    (c : Cocone (Functor.ofSequence (fun _ ↦ p • 𝟙 A))) (hc : IsColimit c)
    (e : c.pt ≅ B) (hz : c.ι.app 0 ≫ e.hom = φ)
    [∀ Y : C, PreservesColimitsOfShape ℕ (tensorLeft Y)]
    [∀ Y : C, PreservesColimitsOfShape ℕ (tensorRight Y)]
    (D : C) [MonObj D] [IsIso (p • 𝟙 D)] (g : A ⟶ D) [IsMonHom g] :
    ∃! f : B ⟶ D, IsMonHom f ∧ φ ≫ f = g := by
  let t : End D := .of (inv (p • 𝟙 D))
  let d : Cocone (Functor.ofSequence (fun _ ↦ p • 𝟙 A)) :=
    { pt := D
      «ι» := NatTrans.ofSequence
        (fun n ↦ g ≫ (t ^ n).asHom) (by
          intro n
          simp only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
          change (p • 𝟙 A) ≫ (g ≫ (t ^ (n + 1)).asHom) =
            (g ≫ (t ^ n).asHom) ≫ 𝟙 D
          rw [Category.comp_id, ← Category.assoc]
          have hw : (p • 𝟙 A) ≫ g = g ≫ (p • 𝟙 D) := by simp
          have ht : (p • 𝟙 D) ≫ (t ^ (n + 1)).asHom = (t ^ n).asHom := by
            rw [pow_succ, End.mul_asHom, ← Category.assoc]
            simp only [t, IsIso.hom_inv_id, Category.id_comp]
          rw [hw, Category.assoc, ht]) }
  let f : B ⟶ D := e.inv ≫ hc.desc d
  have hf : φ ≫ f = g := by
    rw [← hz]
    simp only [f, Category.assoc, Iso.hom_inv_id_assoc, hc.fac]
    simp [d]
  have hext (F : C ⥤ C) [F.Additive]
      [PreservesColimitsOfShape ℕ F] {s t : F.obj B ⟶ D}
      (h : F.map φ ≫ s = F.map φ ≫ t) : s = t := by
    apply (cancel_epi (F.map e.hom)).1
    apply scalar_colimit_hom_ext p A c hc F
    simpa only [← Category.assoc, ← F.map_comp, hz] using h
  have hm : IsMonHom f := by
    constructor
    · rw [← IsMonHom.one_hom φ, Category.assoc, hf, IsMonHom.one_hom g]
    · apply hext (tensorLeft B)
      apply hext (tensorRight A)
      change φ ▷ A ≫ B ◁ φ ≫ μ[B] ≫ f =
        φ ▷ A ≫ B ◁ φ ≫ (f ⊗ₘ f) ≫ μ[D]
      simp only [← Category.assoc]
      rw [← MonoidalCategory.tensorHom_def, ← IsMonHom.mul_hom φ,
        MonoidalCategory.tensorHom_comp_tensorHom]
      rw [Category.assoc, hf, IsMonHom.mul_hom g]
  refine ⟨f, ⟨hm, hf⟩, ?_⟩
  intro f' hf'
  exact hext (𝟭 C) (by simpa only [Functor.id_map] using hf'.2.trans hf.symm)

/-- The actual field coefficient sheaf is the ring localization of the integral
coefficient sheaf at ell, with initial map the pulled-back inclusion.
Source: Bhatt--Scholze Lemma 6.8.2 and the regular coefficient telescope.
(blueprint: lem-weil-pbc-normalized-coefficient-localization).
Proof: the telescope determines additive extensions by dividing its nth leg by
ell^n. Ring units are preserved because the initial inclusion preserves them.
For multiplication, tensor preserves the telescope colimit in either variable;
check the equality on its zeroth legs using the initial ring map. Uniqueness is
colimit uniqueness, since ell is invertible in the target. This is the ring
localization universal property, and hence fixes the localization isomorphism
and its initial map independently of every choice of localization representative. -/
theorem coefficient_localization (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] : CoefficientLocalization X ℓ E := by
  obtain ⟨c, ⟨hc⟩, e, hz⟩ := regular_telescope X ℓ E
  let A := condensedRingObj (Profinite.continuousCoefficientRingObj (integers ℓ E)) X
  let B := condensedRingObj (Profinite.continuousCoefficientRingObj E) X
  let φ := coefficientMap (scalarMap (l := ℓ) (E := E)) X
  obtain ⟨c', ⟨hc'⟩, e', hz'⟩ := transportRegularTelescope ℓ
    (Mod.forget A) c (isColimitOfPreserves (Mod.forget A) hc)
    (Iso.refl A) ((Mod.forget A).mapIso e) (𝟭 _) φ (by exact hz)
  have hi : IsIso (ℓ • 𝟙 B) := by
    have h := field_nsmul_isIso X ℓ E (Mod.regular B)
    exact Functor.map_isIso (Mod.forget B) (ℓ • 𝟙 (Mod.regular B))
  refine ⟨hi, ?_⟩
  intro D hD hp g hg
  exact ring_localization_of_telescope ℓ φ c' hc' e' hz' D g

private theorem ring_localization_iso
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    (p : ℕ) {A B L : C} [MonObj A] [MonObj B] [MonObj L]
    (φ : A ⟶ B) [IsMonHom φ] (j : A ⟶ L) [IsMonHom j]
    (hφ : RingLocalizationAt p φ) (hj : RingLocalizationAt p j) :
    ∃ e : Mon.mk L ≅ Mon.mk B, j ≫ e.hom.hom = φ := by
  obtain ⟨f, ⟨hf, hfj⟩, _⟩ := hj.2 B inferInstance hφ.1 φ inferInstance
  obtain ⟨g, ⟨hg, hgφ⟩, _⟩ := hφ.2 L inferInstance hj.1 j inferInstance
  have hfg : f ≫ g = 𝟙 L := by
    apply (hj.2 L inferInstance hj.1 j inferInstance).unique
    · exact ⟨inferInstance, by rw [← Category.assoc, hfj, hgφ]⟩
    · exact ⟨inferInstance, Category.comp_id j⟩
  have hgf : g ≫ f = 𝟙 B := by
    apply (hφ.2 B inferInstance hφ.1 φ inferInstance).unique
    · exact ⟨inferInstance, by rw [← Category.assoc, hgφ, hfj]⟩
    · exact ⟨inferInstance, Category.comp_id φ⟩
  let e : L ≅ B := ⟨f, g, hfg, hgf⟩
  exact ⟨Mon.mkIso e (IsMonHom.one_hom f) (IsMonHom.mul_hom f), hfj⟩

/-- The normalized comparison A_T[1/ell] ≅ E_T for every representative of the
ring localization. Its restriction to the initial term is the actual inclusion.
Source: uniqueness of localization with its specified initial map.
(blueprint: lem-weil-pbc-normalized-coefficient-localization). -/
def CoefficientLocalizationComparison (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] : Prop :=
  ∀ (L : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (_ : MonObj L)
    (j : condensedRingObj (Profinite.continuousCoefficientRingObj (integers ℓ E)) X ⟶ L)
    (_ : IsMonHom j), RingLocalizationAt ℓ j →
      ∃ e : Mon.mk L ≅
          Mon.mk (condensedRingObj (Profinite.continuousCoefficientRingObj E) X),
        j ≫ e.hom.hom = coefficientMap (scalarMap (l := ℓ) (E := E)) X

/-- The coefficient localization comparison preserves the initial inclusion.
Source: the universal property just proved.
(blueprint: lem-weil-pbc-normalized-coefficient-localization).
Proof: the two localization universal properties give mutually inverse ring maps.
Their composites are identities by uniqueness with the specified initial map. -/
theorem coefficient_localization_comparison (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] : CoefficientLocalizationComparison X ℓ E := by
  intro L hL j hj hloc
  exact ring_localization_iso ℓ _ j (coefficient_localization X ℓ E) hloc

end WeilConjectures.NormalizedScalar
