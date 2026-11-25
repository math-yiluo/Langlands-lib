/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import WeilConjectures.AlgebraicGeometry.Sites.Cospecialization
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections

/-!
# Points of strict localizations and common refinements of geometric points

- Two morphisms `Spec K₁ ⟶ X`, `Spec K₂ ⟶ X` from spectra of fields with the same image point
  become equal after precomposition with morphisms from the spectrum of a common algebraically
  closed field (`AlgebraicGeometry.Scheme.exists_comp_eq_comp_of_apply_closedPoint_eq`).
- For a geometric point `s` of `S`, the structure morphism `S_(s) ⟶ S` of the strict
  localization maps the closed point to the image of `s`
  (`AlgebraicGeometry.Scheme.strictLocalizationToBase_apply_closedPoint`), its image consists of
  generizations of the image of `s`
  (`AlgebraicGeometry.Scheme.strictLocalizationToBase_specializes`),
  and every such generization is attained
  (`AlgebraicGeometry.Scheme.exists_strictLocalizationToBase_apply_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

/-- **Amalgamation of field extensions.** Two extensions `K₁`, `K₂` of a field `k` embed
compatibly into a common algebraically closed field. -/
theorem exists_isAlgClosed_ringHom_comp_eq {k K₁ K₂ : Type u} [Field k] [Field K₁] [Field K₂]
    (φ₁ : k →+* K₁) (φ₂ : k →+* K₂) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (ψ₁ : K₁ →+* Ω) (ψ₂ : K₂ →+* Ω),
      ψ₁.comp φ₁ = ψ₂.comp φ₂ := by
  algebraize [φ₁, φ₂]
  have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K₁ K₂
    φ₁.injective φ₂.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct k K₁ K₂)
  let _ := Ideal.Quotient.field m
  refine ⟨AlgebraicClosure (TensorProduct k K₁ K₂ ⧸ m), inferInstance, inferInstance,
    (algebraMap _ _).comp ((Ideal.Quotient.mk m).comp
      Algebra.TensorProduct.includeLeftRingHom),
    (algebraMap _ _).comp ((Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight (R := k) (A := K₁) (B := K₂)).toRingHom), ?_⟩
  ext a
  have h₁ : Algebra.TensorProduct.includeLeftRingHom (φ₁ a) =
      algebraMap k (TensorProduct k K₁ K₂) a :=
    (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := K₁) (B := K₂)).commutes a
  have h₂ : Algebra.TensorProduct.includeRight (R := k) (A := K₁) (B := K₂) (φ₂ a) =
      algebraMap k (TensorProduct k K₁ K₂) a :=
    (Algebra.TensorProduct.includeRight (R := k) (A := K₁) (B := K₂)).commutes a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom]
  rw [h₁, h₂]

/-- **Common refinement of points with the same image.** Two morphisms `t₁ : Spec K₁ ⟶ X` and
`t₂ : Spec K₂ ⟶ X` from spectra of fields with the same image point agree after precomposition
with morphisms `Spec Ω ⟶ Spec Kᵢ` from the spectrum of an algebraically closed field `Ω`. -/
theorem exists_comp_eq_comp_of_apply_closedPoint_eq {X : Scheme.{u}} {K₁ K₂ : Type u}
    [Field K₁] [Field K₂] (t₁ : Spec (.of K₁) ⟶ X) (t₂ : Spec (.of K₂) ⟶ X)
    (h : t₁ (closedPoint K₁) = t₂ (closedPoint K₂)) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (a : Spec (.of Ω) ⟶ Spec (.of K₁))
      (b : Spec (.of Ω) ⟶ Spec (.of K₂)), a ≫ t₁ = b ≫ t₂ := by
  obtain ⟨⟨x₁, d₁⟩, rfl⟩ := (SpecToEquivOfField K₁ X).symm.surjective t₁
  obtain ⟨⟨x₂, d₂⟩, rfl⟩ := (SpecToEquivOfField K₂ X).symm.surjective t₂
  simp only [SpecToEquivOfField_symm_apply, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply] at h ⊢
  subst h
  obtain ⟨Ω, _, _, ψ₁, ψ₂, hψ⟩ := exists_isAlgClosed_ringHom_comp_eq d₁.hom d₂.hom
  refine ⟨Ω, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom ψ₁),
    Spec.map (CommRingCat.ofHom ψ₂), ?_⟩
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  exact congrArg (fun φ : _ →+* Ω ↦ φ a) hψ

/-- Every point `x` of a scheme is the image of a geometric point `Spec Ω ⟶ X` with `Ω`
algebraically closed, for instance `Spec κ(x)^alg ⟶ Spec κ(x) ⟶ X`. -/
theorem exists_isAlgClosed_apply_closedPoint_eq {X : Scheme.{u}} (x : X) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (t : Spec (.of Ω) ⟶ X),
      t (closedPoint Ω) = x :=
  ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x)
      (AlgebraicClosure (X.residueField x)))) ≫ X.fromSpecResidueField x, by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _⟩

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The structure morphism `S_(s) ⟶ S` maps the closed point to the image of `s`. -/
lemma strictLocalizationToBase_apply_closedPoint :
    strictLocalizationToBase s (closedPoint (strictHenselization s)) = s (closedPoint Ω) := by
  rw [← spec_map_strictHenselizationEval_apply_closedPoint s, ← Scheme.Hom.comp_apply,
    spec_map_strictHenselizationEval_comp_strictLocalizationToBase]

/-- Every point of the strict localization `S_(s)` maps to a generization of the image of
`s`. -/
lemma strictLocalizationToBase_specializes (p : strictLocalization s) :
    strictLocalizationToBase s p ⤳ s (closedPoint Ω) := by
  rw [← strictLocalizationToBase_apply_closedPoint]
  exact (specializes_closedPoint p).map (strictLocalizationToBase s).continuous

/-- Every generization of the image of `s` is the image of a point of the strict localization
`S_(s)`. -/
lemma exists_strictLocalizationToBase_apply_eq {w : S} (hw : w ⤳ s (closedPoint Ω)) :
    ∃ p : strictLocalization s, strictLocalizationToBase s p = w :=
  exists_strictLocalizationConeAll_π_app_base_eq s (PointedEtaleNeighborhood.base s) hw

end AlgebraicGeometry.Scheme
