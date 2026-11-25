/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections
public import WeilConjectures.TraceFormula.Specialization.PointModel

/-!

# The nearby cycles of the trait are faithful on the endomorphisms of the unit

Let `k` be a field and `k'` a separably closed extension of `k`. The nearby cycles
`Ψ_s : Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Spec k')⟦ℚ̲̄_ℓ⟧` of the trait `S = Spec k'⟦t⟧`
(`ProEtale.CondensedRing.traitSpecialization`) are injective on the endomorphisms of the unit
(`ProEtale.CondensedRing.traitSpecialization_map_eq_zero_iff`).

The argument does not compute `Ψ_s` on morphisms. For any field `k`, the ring
`End (𝟙_ Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧)` is the ring `H⁰(Spec k, ℚ̄_ℓ)` of continuous functions on the
one-point space `Spec k` with values in a finite subextension of `ℚ̄_ℓ / ℚ_ℓ`
(`ProEtale.CondensedRing.exists_bijective_unitEnd_point`, through
`AlgebraicGeometry.ProEtale.padicAlgClSectionRingHom_bijective`), that is `ℚ̄_ℓ`. Hence every
endomorphism of the unit is zero or invertible
(`ProEtale.CondensedRing.eq_zero_or_isUnit_unitEnd_point`) and the unit has a nonzero identity
(`ProEtale.CondensedRing.nontrivial_unitEnd_point`). If `Ψ_s` killed an invertible
endomorphism, it would kill the identity of `Ψ_s ℚ̄_ℓ ≅ ℚ̄_ℓ` (the specialization unit is an
isomorphism, `ProEtale.CondensedRing.isIso_traitSpecializationUnit`), whereas the unit of
`Dᵇc(Spec k')⟦ℚ̲̄_ℓ⟧` has a nonzero identity. Conversely `Ψ_s` preserves zero morphisms, being
built from the adjoints `Lε^*`, `Rj_*` and `Li^*`.

## Main results

- `ProEtale.CondensedRing.exists_bijective_unitEnd_point`:
  `End (𝟙_ Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧) ≅ H⁰(Spec k, ℚ̄_ℓ)` for any field `k`.
- `ProEtale.CondensedRing.eq_zero_or_isUnit_unitEnd_point`: every endomorphism of the unit of
  `Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧` is zero or invertible.
- `ProEtale.CondensedRing.traitSpecialization_map_eq_zero_iff`: `Ψ_s f = 0 ↔ f = 0` for an
  endomorphism `f` of the unit.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- A functor between full subcategories lifting a functor which preserves zero morphisms
preserves zero morphisms. -/
private lemma ObjectProperty.preservesZeroMorphisms_lift_of_preservesZeroMorphisms {C D : Type*}
    [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (P : ObjectProperty C) (Q : ObjectProperty D)
    (G : C ⥤ D) [G.PreservesZeroMorphisms] (h : ∀ X : P.FullSubcategory, Q (G.obj X.obj)) :
    (Q.lift (P.ι ⋙ G) h).PreservesZeroMorphisms where
  map_zero X Y := Q.ι.map_injective
    (by rw [Q.ι.map_zero]; exact (G.congr_map (P.ι.map_zero X Y)).trans (G.map_zero _ _))

/-- The composite `F₁ ⋙ G₂ ⋙ F₃` of a left adjoint, a right adjoint and a left adjoint preserves
zero morphisms. -/
private lemma preservesZeroMorphisms_comp_comp_of_adjunction {C₁ C₂ C₃ C₄ : Type*}
    [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    [Preadditive C₄] {F₁ : C₁ ⥤ C₂} {G₁ : C₂ ⥤ C₁} {F₂ : C₃ ⥤ C₂} {G₂ : C₂ ⥤ C₃}
    {F₃ : C₃ ⥤ C₄} {G₃ : C₄ ⥤ C₃} (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (a₃ : F₃ ⊣ G₃) :
    (F₁ ⋙ G₂ ⋙ F₃).PreservesZeroMorphisms := by
  have := a₁.isLeftAdjoint
  have := a₂.isRightAdjoint
  have := a₃.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint F₁
  have := Functor.preservesZeroMorphisms_of_isRightAdjoint G₂
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint F₃
  infer_instance

/-- On a space with at most one point, a continuous function with values in a finite
subextension of `ℚ̄_ℓ / ℚ_ℓ` is zero or invertible. -/
lemma eq_zero_or_isUnit_finiteIntermediateFieldValued (ℓ : ℕ) [Fact ℓ.Prime] (U : Type*)
    [TopologicalSpace U] [Subsingleton U] (f : PadicAlgCl.finiteIntermediateFieldValued ℓ U) :
    f = 0 ∨ IsUnit f := by
  by_cases h : ∀ x, (f : C(U, PadicAlgCl ℓ)) x = 0
  · exact Or.inl (Subtype.ext (ContinuousMap.ext h))
  push Not at h
  obtain ⟨x, hx⟩ := h
  obtain ⟨E, hE, hfE⟩ := f.2
  let g : PadicAlgCl.finiteIntermediateFieldValued ℓ U :=
    ⟨ContinuousMap.const U ((f : C(U, PadicAlgCl ℓ)) x)⁻¹, E, hE, fun _ ↦ inv_mem (hfE x)⟩
  refine Or.inr (isUnit_iff_exists_inv.2 ⟨g, Subtype.ext (ContinuousMap.ext fun y ↦ ?_)⟩)
  change (f : C(U, PadicAlgCl ℓ)) y * ((f : C(U, PadicAlgCl ℓ)) x)⁻¹ = 1
  rw [Subsingleton.elim y x]
  exact mul_inv_cancel₀ hx

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Point

variable (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]

-- the ring structure on `End (𝟙_ Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧)` is found by a long instance search
/-- The endomorphisms of the unit of `Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧` are `H⁰(Spec k, ℚ̄_ℓ)`, the continuous
functions on the one-point space `Spec k` with values in a finite subextension of
`ℚ̄_ℓ / ℚ_ℓ`: placing the endomorphisms of the unit module in degree `0` is bijective, the
endomorphisms of the unit module are its global sections (`Mod.regularEndRingHom_bijective`),
and these are computed by `padicAlgClSectionRingHom_bijective`. -/
theorem exists_bijective_unitEnd_point :
    ∃ φ : PadicAlgCl.finiteIntermediateFieldValued ℓ (point k).left →+*
      End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)), Function.Bijective φ := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let A := Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
    (condensedRingObj Λ (point k).left)
  let F := HomologicalComplex.single A (ComplexShape.up ℤ) 0 ⋙
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let e : DerivedCategory.singleFunctor A 0 ≅ F := (DerivedCategory.singleFunctorIsoCompQ A 0).trans
    (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso A).symm)
  have : F.Full := Functor.Full.of_iso e
  have : F.Faithful := Functor.Faithful.of_iso e
  have hF : Function.Bijective
      (F.mapEndRingHom (Mod.regular (condensedRingObj Λ (point k).left))) :=
    ((Functor.FullyFaithful.ofFullyFaithful F).mulEquivEnd _).bijective
  have hι : Function.Bijective
      ((ObjectProperty.ι _).mapEndRingHom (𝟙_ (Dᵇc((point k).left)⟦Λ⟧))) :=
    ((ObjectProperty.fullyFaithfulι _).mulEquivEnd _).bijective
  have : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := A))) :=
    inferInstanceAs (IsIso (𝟙 _))
  have : CompactSpace (point k).left := inferInstanceAs (CompactSpace (Spec (.of k)))
  have : QuasiSeparatedSpace (point k).left :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of k)))
  let e₁ := (RingEquiv.ofBijective _ hι).symm
  let e₂ := (asIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := A)))).symm.conjRingEquiv
  exact ⟨e₁.toRingHom.comp (e₂.toRingHom.comp
    ((F.mapEndRingHom (Mod.regular (condensedRingObj Λ (point k).left))).comp
      (Mod.regularEndRingHom.comp (padicAlgClSectionRingHom ℓ (point k).left)))),
    e₁.bijective.comp (e₂.bijective.comp (hF.comp
      (Mod.regularEndRingHom_bijective.comp (padicAlgClSectionRingHom_bijective ℓ _))))⟩

/-- Every endomorphism of the unit of `Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧` is zero or invertible: the ring
`End (𝟙_ Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧)` is `H⁰(Spec k, ℚ̄_ℓ) = ℚ̄_ℓ`. -/
theorem eq_zero_or_isUnit_unitEnd_point
    (f : End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :
    f = 0 ∨ IsUnit f := by
  obtain ⟨φ, hφ⟩ := exists_bijective_unitEnd_point k (ℓ := ℓ)
  obtain ⟨s, rfl⟩ := hφ.2 f
  have : Subsingleton (point k).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rcases eq_zero_or_isUnit_finiteIntermediateFieldValued ℓ (point k).left s with hs | hs
  · exact Or.inl (by rw [hs, map_zero])
  · exact Or.inr (hs.map φ)

/-- The unit of `Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧` has a nonzero identity. -/
instance nontrivial_unitEnd_point :
    Nontrivial (End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  obtain ⟨φ, hφ⟩ := exists_bijective_unitEnd_point k (ℓ := ℓ)
  have : Nonempty (point k).left := inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact hφ.1.nontrivial

end Point

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k'] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- The nearby cycles `Ψ_s` of the trait `S = Spec k'⟦t⟧` are injective on the endomorphisms of
the unit of `Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧`. -/
theorem traitSpecialization_map_eq_zero_iff
    (f : 𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶ 𝟙_ _) :
    (traitSpecialization k k' (ℓ := ℓ)).map f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases eq_zero_or_isUnit_unitEnd_point k (End.of f) with hf | hf
    · exact congrArg End.asHom hf
    have : IsIso f := (isUnit_iff_isIso (End.of f)).1 hf
    exfalso
    have hid : 𝟙 ((traitSpecialization k k' (ℓ := ℓ)).obj (𝟙_ _)) = 0 := by
      rw [← CategoryTheory.Functor.map_id, ← IsIso.inv_hom_id f,
        Functor.map_comp, h, comp_zero]
    have := isIso_traitSpecializationUnit k k' (ℓ := ℓ)
    have h1 : (1 : End (𝟙_ (Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧))) = 0 := by
      apply End.ext
      rw [End.one_asHom, End.zero_asHom,
        ← IsIso.hom_inv_id (traitSpecializationUnit k k' (ℓ := ℓ)),
        ← Category.id_comp (inv _), hid, zero_comp, comp_zero]
    exact one_ne_zero h1
  · subst h
    let Λ := Profinite.padicAlgClRingObj.{u} ℓ
    let M := traitModel k k'
    have : (M.nearbyCycles Λ).PreservesZeroMorphisms :=
      preservesZeroMorphisms_comp_comp_of_adjunction
        (derivedUpperStarLowerStarAdjunction Λ M.ε)
        (derivedUpperStarLowerStarAdjunction Λ M.j) (derivedUpperStarLowerStarAdjunction Λ M.i)
    have : (traitSpecialization k k' (ℓ := ℓ)).PreservesZeroMorphisms :=
      ObjectProperty.preservesZeroMorphisms_lift_of_preservesZeroMorphisms _ _ _ _
    exact Functor.map_zero _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing
