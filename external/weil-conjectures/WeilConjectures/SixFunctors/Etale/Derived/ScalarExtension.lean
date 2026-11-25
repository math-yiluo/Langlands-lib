/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.CoextendScalarsAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.EpiMono
public import WeilConjectures.NumberTheory.Padics.IntegersMap
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

/-!
# Scalar extension between the rational stages

Let `E ⊆ L` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, with rings of integers `𝒪_E ⊆ 𝒪_L`.
The scalar extension `- ⊗_E L : D_comp(Y, E) ⥤ D_comp(Y, L)` of blueprint
`proposition-inverting-ell--2` is computed on an integral representative `K` by the derived
base change `K ⊗ᴸ_{𝒪_E} 𝒪_L`, followed by rationalization. Here the derived base change is
characterized by its universal property (`AlgebraicGeometry.Etale.IsDerivedBaseChange`): a
morphism `η : K ⟶ Res K'` to the restriction of scalars of `K' ∈ D(Y_ét, 𝒪_L)` through which
every morphism from `K` to a restriction of scalars factors uniquely.

## Main statements

- `AlgebraicGeometry.Etale.IsDerivedBaseChange.map`: the morphism `K₁' ⟶ K₂'` induced by a
  morphism `K₁ ⟶ K₂` between objects with derived base changes; it is functorial and linear
  along `𝒪_E ⟶ 𝒪_L`.
- `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_integersShrinkMap` and
  `AlgebraicGeometry.Etale.derivedCompleteIntegral_derivedBaseChange_integersShrinkMap`: every
  object of `D(Y_ét, 𝒪_E)` has a derived base change along `𝒪_E ⟶ 𝒪_L`, and derived base change
  preserves derived completeness.
- `AlgebraicGeometry.Etale.nonempty_iso_fromIntegral_of_isDerivedBaseChange`: the rationalization of
  the derived base change only depends on the rationalization of the integral representative.
- `AlgebraicGeometry.Etale.isTriangulated_derivedCompleteRationalScalarExtension`: the scalar
  extension `D_comp(Y, E) ⥤ D_comp(Y, L)` is triangulated.

## Construction of the derived base change

`𝒪_L` is a finite free `𝒪_E`-module with a Frobenius form
(`PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap`), so coextension of scalars
`M ↦ Hom_{𝒪_E}(𝒪_L, M)` of étale sheaves is left adjoint to restriction of scalars
(`AlgebraicGeometry.Etale.coextendRestrictScalarsAdj`), besides being right adjoint to it. It is
therefore exact, and the functor it induces on derived categories is both left and right adjoint
to restriction of scalars. The left adjunction says that it computes the derived base change;
the right adjunction says that it preserves derived completeness, which is right orthogonality
to the objects on which a uniformizer acts invertibly. The derived base change functor is then
the left adjoint of restriction of scalars (`AlgebraicGeometry.Etale.derivedBaseChange`), and
the functor between rationalizations is induced along `𝒪_E ⟶ 𝒪_L`
(`CategoryTheory.Rationalization.mapOfRingHom`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

attribute [local instance] AlgebraicGeometry.Scheme.Etale.essentiallySmall

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

section RestrictScalars

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') {X : Scheme.{u}}

/-- Restriction of scalars along `φ : Λ ⟶ Λ'` is linear along `φ`: it carries the
multiplication by `φ r` to the multiplication by `r`. -/
lemma derivedRestrictScalars_map_smul_id (r : Λ) (N : 𝐃(X, Λ')) :
    (derivedRestrictScalars φ X).map (φ r • 𝟙 N) = r • 𝟙 _ := by
  let F := Sheaf.restrictScalars X.smallEtaleTopology φ
  let P := (_root_.DerivedCategory.Q).objPreimage N
  let eN : (_root_.DerivedCategory.Q).obj P ≅ N := (_root_.DerivedCategory.Q).objObjPreimageIso N
  have h₀ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (φ r • 𝟙 P) = r • 𝟙 _ := by
    refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
    simp only [Functor.mapHomologicalComplex_map_f, HomologicalComplex.smul_f_apply,
      HomologicalComplex.id_f]
    ext U x
    exact (ModuleCat.restrictScalars.smul_def φ r x).symm
  have h₁ : (derivedRestrictScalars φ X).map ((_root_.DerivedCategory.Q).map (φ r • 𝟙 P)) =
      r • 𝟙 _ := by
    have h : (derivedRestrictScalars φ X).map ((_root_.DerivedCategory.Q).map (φ r • 𝟙 P)) ≫
        F.mapDerivedCategoryFactors.hom.app P = F.mapDerivedCategoryFactors.hom.app P ≫
          (_root_.DerivedCategory.Q).map ((F.mapHomologicalComplex _).map (φ r • 𝟙 P)) :=
      F.mapDerivedCategoryFactors.hom.naturality (φ r • 𝟙 P)
    rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app P), h, h₀, Functor.map_smul,
      CategoryTheory.Functor.map_id, Linear.comp_smul]
    simp only [Linear.smul_comp, Category.id_comp]
    erw [Category.comp_id]
  have h₂ : φ r • 𝟙 N = eN.inv ≫ (_root_.DerivedCategory.Q).map (φ r • 𝟙 P) ≫ eN.hom := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Iso.inv_hom_id]
  rw [h₂, Functor.map_comp, Functor.map_comp, h₁, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- Restriction of scalars along `φ : Λ ⟶ Λ'` is linear along `φ`. -/
lemma derivedRestrictScalars_map_smul (r : Λ) {N N' : 𝐃(X, Λ')} (g : N ⟶ N') :
    (derivedRestrictScalars φ X).map (φ r • g) = r • (derivedRestrictScalars φ X).map g := by
  have : φ r • g = g ≫ (φ r • 𝟙 N') := by rw [Linear.comp_smul, Category.comp_id]
  rw [this, Functor.map_comp, derivedRestrictScalars_map_smul_id, Linear.comp_smul,
    Category.comp_id]

end RestrictScalars

namespace IsDerivedBaseChange

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'} {X : Scheme.{u}}
  {K₁ K₂ K₃ : 𝐃(X, Λ)} {K₁' K₂' K₃' : 𝐃(X, Λ')}
  {η₁ : K₁ ⟶ (derivedRestrictScalars φ X).obj K₁'}
  {η₂ : K₂ ⟶ (derivedRestrictScalars φ X).obj K₂'}
  {η₃ : K₃ ⟶ (derivedRestrictScalars φ X).obj K₃'}

/-- The morphism out of a derived base change corresponding to a morphism into a restriction of
scalars. -/
noncomputable def lift (h₁ : IsDerivedBaseChange η₁) {N : 𝐃(X, Λ')}
    (f : K₁ ⟶ (derivedRestrictScalars φ X).obj N) : K₁' ⟶ N :=
  ((h₁ N).2 f).choose

@[reassoc (attr := simp)]
lemma fac (h₁ : IsDerivedBaseChange η₁) {N : 𝐃(X, Λ')}
    (f : K₁ ⟶ (derivedRestrictScalars φ X).obj N) :
    η₁ ≫ (derivedRestrictScalars φ X).map (h₁.lift f) = f :=
  ((h₁ N).2 f).choose_spec

lemma hom_ext (h₁ : IsDerivedBaseChange η₁) {N : 𝐃(X, Λ')} {g g' : K₁' ⟶ N}
    (h : η₁ ≫ (derivedRestrictScalars φ X).map g = η₁ ≫ (derivedRestrictScalars φ X).map g') :
    g = g' :=
  (h₁ N).1 h

/-- The morphism `K₁' ⟶ K₂'` between derived base changes induced by a morphism `K₁ ⟶ K₂`: the
unique morphism compatible with `η₁` and `η₂`. -/
noncomputable def map (h₁ : IsDerivedBaseChange η₁) (η₂ : K₂ ⟶ (derivedRestrictScalars φ X).obj K₂')
    (f : K₁ ⟶ K₂) : K₁' ⟶ K₂' :=
  h₁.lift (f ≫ η₂)

@[reassoc (attr := simp)]
lemma map_fac (h₁ : IsDerivedBaseChange η₁) (f : K₁ ⟶ K₂) :
    η₁ ≫ (derivedRestrictScalars φ X).map (h₁.map η₂ f) = f ≫ η₂ :=
  h₁.fac _

lemma map_id (h₁ : IsDerivedBaseChange η₁) : h₁.map η₁ (𝟙 K₁) = 𝟙 K₁' :=
  h₁.hom_ext (by rw [map_fac, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id])

lemma map_comp (h₁ : IsDerivedBaseChange η₁) (h₂ : IsDerivedBaseChange η₂) (f : K₁ ⟶ K₂)
    (g : K₂ ⟶ K₃) : h₁.map η₃ (f ≫ g) = h₁.map η₂ f ≫ h₂.map η₃ g :=
  h₁.hom_ext (by rw [map_fac, Functor.map_comp, map_fac_assoc, map_fac, Category.assoc])

lemma map_smul (h₁ : IsDerivedBaseChange η₁) (r : Λ) (f : K₁ ⟶ K₂) :
    h₁.map η₂ (r • f) = φ r • h₁.map η₂ f :=
  h₁.hom_ext (by
    rw [map_fac, derivedRestrictScalars_map_smul, Linear.comp_smul, map_fac, Linear.smul_comp])

end IsDerivedBaseChange

section BaseChangeFunctor

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})
  (h : ∀ K : 𝐃(X, Λ), ∃ (K' : 𝐃(X, Λ')) (η : K ⟶ (derivedRestrictScalars φ X).obj K'),
    IsDerivedBaseChange η)

/-- The universal property of the derived base changes, as a family of bijections. -/
noncomputable def derivedBaseChangeHomEquiv (K : 𝐃(X, Λ)) (N : 𝐃(X, Λ')) :
    ((h K).choose ⟶ N) ≃ (K ⟶ (derivedRestrictScalars φ X).obj N) :=
  Equiv.ofBijective _ ((h K).choose_spec.choose_spec N)

/-- If every object of `D(X_ét, Λ)` admits a derived base change along `φ : Λ ⟶ Λ'`, the
derived base change `K ↦ K ⊗ᴸ_Λ Λ'` as a functor `D(X_ét, Λ) ⥤ D(X_ét, Λ')`, left adjoint to
restriction of scalars. -/
noncomputable def derivedBaseChange : 𝐃(X, Λ) ⥤ 𝐃(X, Λ') :=
  Adjunction.leftAdjointOfEquiv (derivedBaseChangeHomEquiv φ X h) fun K N N' g g' ↦ by
    simp only [derivedBaseChangeHomEquiv, Equiv.ofBijective_apply, Functor.map_comp,
      Category.assoc]

/-- The derived base change is left adjoint to restriction of scalars. -/
noncomputable def derivedBaseChangeAdjunction :
    derivedBaseChange φ X h ⊣ derivedRestrictScalars φ X :=
  Adjunction.adjunctionOfEquivLeft _ _

noncomputable instance : (derivedBaseChange φ X h).CommShift ℤ :=
  (derivedBaseChangeAdjunction φ X h).leftAdjointCommShift ℤ

/-- The derived base change is a triangulated functor, being left adjoint to the triangulated
restriction of scalars. -/
instance : (derivedBaseChange φ X h).IsTriangulated :=
  have := (derivedBaseChangeAdjunction φ X h).commShift_of_rightAdjoint ℤ
  (derivedBaseChangeAdjunction φ X h).isTriangulated_leftAdjoint

/-- The derived base change is linear along `φ`. -/
lemma derivedBaseChange_map_smul (r : Λ) {K₁ K₂ : 𝐃(X, Λ)} (f : K₁ ⟶ K₂) :
    (derivedBaseChange φ X h).map (r • f) = φ r • (derivedBaseChange φ X h).map f := by
  let adj := derivedBaseChangeAdjunction φ X h
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, derivedRestrictScalars_map_smul,
    Linear.comp_smul, adj.unit_naturality, adj.unit_naturality, Linear.smul_comp]

end BaseChangeFunctor

section Frobenius

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {ι : Type*} [Fintype ι]
  (b : Module.Basis ι Λ Λ') (φ : Λ' →ₗ[Λ] Λ)
  (hφ : Function.Bijective fun s : Λ' ↦ φ ∘ₗ LinearMap.mulLeft Λ s) (X : Scheme.{u})

/-- Along a finite free extension `Λ ⟶ Λ'` with a Frobenius form, coextension of scalars of
étale sheaves is left adjoint to restriction of scalars. -/
noncomputable def coextendRestrictScalarsAdj :
    coextendScalars (algebraMap Λ Λ') X ⊣
      Sheaf.restrictScalars X.smallEtaleTopology (algebraMap Λ Λ') :=
  Sheaf.sheafComposeRestrictScalarsAdj _ _ (ModuleCat.coextendRestrictScalarsAdj b φ hφ)

/- Along a finite free extension with a Frobenius form, coextension of scalars of étale sheaves is
right exact, being a left adjoint (`AlgebraicGeometry.Etale.coextendRestrictScalarsAdj`); this is
assumed as an instance below. -/
variable [PreservesFiniteColimits (coextendScalars (algebraMap Λ Λ') X)]

instance : PreservesFiniteLimits (coextendScalars (algebraMap Λ Λ') X) :=
  have := (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology (algebraMap Λ Λ')).isRightAdjoint
  inferInstance

include b φ hφ in
/-- The derived coextension of scalars is left adjoint to restriction of scalars, along a finite
free extension with a Frobenius form. -/
noncomputable def derivedCoextendRestrictScalarsAdj :
    (coextendScalars (algebraMap Λ Λ') X).mapDerivedCategory ⊣
      derivedRestrictScalars (algebraMap Λ Λ') X :=
  (coextendRestrictScalarsAdj b φ hφ X).mapDerivedCategoryAdjunction

/-- The derived coextension of scalars is right adjoint to restriction of scalars. -/
noncomputable def derivedRestrictCoextendScalarsAdj :
    derivedRestrictScalars (algebraMap Λ Λ') X ⊣
      (coextendScalars (algebraMap Λ Λ') X).mapDerivedCategory :=
  (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology (algebraMap Λ Λ'))
    |>.mapDerivedCategoryAdjunction

/-- Along a finite free extension with a Frobenius form, the derived coextension of scalars of
`K` is its derived base change, through the unit of
`AlgebraicGeometry.Etale.derivedCoextendRestrictScalarsAdj`. -/
lemma isDerivedBaseChange_derivedCoextendRestrictScalarsAdj_unit (K : 𝐃(X, Λ)) :
    IsDerivedBaseChange ((derivedCoextendRestrictScalarsAdj b φ hφ X).unit.app K) := fun N ↦ by
  convert ((derivedCoextendRestrictScalarsAdj b φ hφ X).homEquiv K N).bijective using 1
  ext g
  exact ((derivedCoextendRestrictScalarsAdj b φ hφ X).homEquiv_unit K N g).symm

end Frobenius

section Rational

variable (l : ℕ) [Fact l.Prime] (E L : Type w) [Field E] [Field L]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra E L]
  [IsScalarTower E L (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] L] [Small.{u + 1} E] [Small.{u + 1} L]

variable {Y : Scheme.{u}}

/-- Well-definedness of scalar extension.

Let `E ⊆ L` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`. If two integral objects
`K₁, K₂ ∈ D_comp(Y_ét, 𝒪_E)` become isomorphic in the rationalization `D_comp(Y_ét, E)`, then
their derived base changes `K₁ ⊗ᴸ_{𝒪_E} 𝒪_L` and `K₂ ⊗ᴸ_{𝒪_E} 𝒪_L` (objects of
`D_comp(Y_ét, 𝒪_L)` given with the universal property `IsDerivedBaseChange`) become isomorphic in
`D_comp(Y_ét, L)`. So the scalar extension `(K ⊗ᴸ_{𝒪_E} 𝒪_L) ⊗_{𝒪_L} L` of an object of
`D_comp(Y_ét, E)` does not depend on the chosen integral representative `K`.

As in the blueprint, this is the uniqueness of the extension of the `𝒪_E`-linear derived base
change to the rationalizations: an isomorphism of rationalizations is a morphism `f : K₁ ⟶ K₂`
with a morphism `g : K₂ ⟶ K₁` such that `g ∘ f` and `f ∘ g` are nonzero scalars up to torsion
(`CategoryTheory.Rationalization.exists_smul_eq_map`,
`CategoryTheory.Rationalization.map_eq_map_iff`), and the base change of morphisms is
functorial and linear along `𝒪_E ⟶ 𝒪_L` (`AlgebraicGeometry.Etale.IsDerivedBaseChange.map`).

The statement only asserts that an isomorphism exists. For the derived base changes given by the
functor `AlgebraicGeometry.Etale.derivedCompleteIntegralScalarExtension`, the isomorphism is
canonical: it is the image of `e` under the scalar extension
`AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtension`, read through the isomorphisms
`AlgebraicGeometry.Etale.derivedCompleteRationalScalarExtensionFromIntegralIso`. -/
theorem nonempty_iso_fromIntegral_of_isDerivedBaseChange
    {K₁ K₂ : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E}
    {K₁' K₂' : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l L}
    {η₁ : K₁.obj ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E L) Y).obj K₁'.obj}
    {η₂ : K₂.obj ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E L) Y).obj K₂'.obj}
    (h₁ : IsDerivedBaseChange η₁) (h₂ : IsDerivedBaseChange η₂)
    (e : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K₁ ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K₂) :
    Nonempty ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l L).obj K₁' ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l L).obj K₂') := by
  let φ := PadicAlgCl.integersShrinkMap.{w, u} l E L
  let QE := DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E
  let QL := DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l L
  obtain ⟨m₁, hm₁, f, hf⟩ := Rationalization.exists_smul_eq_map e.hom
  obtain ⟨m₂, hm₂, g, hg⟩ := Rationalization.exists_smul_eq_map e.inv
  -- the base changes of `f` and `g`
  let f' : K₁' ⟶ K₂' := ObjectProperty.homMk (h₁.map η₂ f.hom)
  let g' : K₂' ⟶ K₁' := ObjectProperty.homMk (h₂.map η₁ g.hom)
  -- `g ∘ f` and `f ∘ g` are scalars up to torsion
  have key : ∀ {P₁ P₂ : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E}
      {P₁' P₂' : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l L}
      {θ₁ : P₁.obj ⟶ (derivedRestrictScalars φ Y).obj P₁'.obj}
      {θ₂ : P₂.obj ⟶ (derivedRestrictScalars φ Y).obj P₂'.obj}
      (k₁ : IsDerivedBaseChange θ₁) (k₂ : IsDerivedBaseChange θ₂) (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₁)
      (c : Shrink.{u + 1} (PadicAlgCl.integers l E)) (hc : c ∈ nonZeroDivisors _)
      (hab : QE.map (a ≫ b) = c • 𝟙 _),
      QL.map (ObjectProperty.homMk (k₁.map θ₂ a.hom) ≫ ObjectProperty.homMk (k₂.map θ₁ b.hom)) =
        φ c • 𝟙 _ := by
    intro P₁ P₂ P₁' P₂' θ₁ θ₂ k₁ k₂ a b c hc hab
    have hab' : QE.map (a ≫ b) = QE.map (c • 𝟙 _) := by
      rw [hab, Functor.map_smul, CategoryTheory.Functor.map_id]
    obtain ⟨m, hm, hm'⟩ := (Rationalization.map_eq_map_iff _ _).1 hab'
    have hm'' : m • (a.hom ≫ b.hom) = (m * c) • 𝟙 P₁.obj := by
      have := congrArg (fun t ↦ t.hom) hm'
      change m • (a.hom ≫ b.hom) = m • c • 𝟙 P₁.obj at this
      rw [this, smul_smul]
    have hbc : φ m • (k₁.map θ₂ a.hom ≫ k₂.map θ₁ b.hom) = φ (m * c) • 𝟙 P₁'.obj := by
      rw [← IsDerivedBaseChange.map_comp, ← IsDerivedBaseChange.map_smul, hm'',
        IsDerivedBaseChange.map_smul, IsDerivedBaseChange.map_id]
    have hφm : φ m ∈ nonZeroDivisors _ :=
      PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E L hm
    refine Rationalization.smul_left_injective hφm ?_
    dsimp only
    have : φ m • (ObjectProperty.homMk (k₁.map θ₂ a.hom) ≫
        ObjectProperty.homMk (k₂.map θ₁ b.hom) : P₁' ⟶ P₁') = φ (m * c) • 𝟙 P₁' :=
      ObjectProperty.hom_ext _ (by
        change φ m • (k₁.map θ₂ a.hom ≫ k₂.map θ₁ b.hom) = φ (m * c) • 𝟙 P₁'.obj
        exact hbc)
    rw [← Functor.map_smul, this, Functor.map_smul, CategoryTheory.Functor.map_id, map_mul,
      mul_smul]
  have hfg : QE.map (f ≫ g) = (m₁ * m₂) • 𝟙 _ := by
    rw [Functor.map_comp, ← hf, ← hg, Linear.smul_comp, Linear.comp_smul, Iso.hom_inv_id,
      mul_smul]
  have hgf : QE.map (g ≫ f) = (m₂ * m₁) • 𝟙 _ := by
    rw [Functor.map_comp, ← hf, ← hg, Linear.smul_comp, Linear.comp_smul, Iso.inv_hom_id,
      mul_smul]
  have h₁₂ := key h₁ h₂ f g _ (Submonoid.mul_mem _ hm₁ hm₂) hfg
  have h₂₁ := key h₂ h₁ g f _ (Submonoid.mul_mem _ hm₂ hm₁) hgf
  have hφ₁ := Rationalization.isIso_smul_id
    (PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E L (Submonoid.mul_mem _ hm₁ hm₂))
    (QL.obj K₁')
  have hφ₂ := Rationalization.isIso_smul_id
    (PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E L (Submonoid.mul_mem _ hm₂ hm₁))
    (QL.obj K₂')
  have : IsIso (QL.map f') := by
    refine isIso_of_isIso_comp_of_isIso_comp _ (QL.map g') ?_ ?_
    · rw [← Functor.map_comp, h₁₂]
      exact hφ₁
    · rw [← Functor.map_comp, h₂₁]
      exact hφ₂
  exact ⟨asIso (QL.map f')⟩



variable {l E L} in
/-- Every object of `D(Y_ét, 𝒪_E)` has a derived base change `K ⊗ᴸ_{𝒪_E} 𝒪_L` along the inclusion
`𝒪_E ⟶ 𝒪_L`: the derived coextension of scalars, `𝒪_L` being finite free over `𝒪_E` with a
Frobenius form. -/
theorem exists_isDerivedBaseChange_integersShrinkMap
    (K : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l E))) :
    ∃ (K' : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l L)))
      (η : K ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E L) Y).obj K'),
      IsDerivedBaseChange η := by
  let := (PadicAlgCl.integersShrinkMap.{w, u} l E L).toAlgebra
  obtain ⟨n, b, φ, hφ⟩ := PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap.{w, u} l E L
  have := (coextendRestrictScalarsAdj b φ hφ Y).isLeftAdjoint
  exact ⟨_, _, isDerivedBaseChange_derivedCoextendRestrictScalarsAdj_unit b φ hφ Y K⟩

variable {l E L} in
/-- Derived base change along `𝒪_E ⟶ 𝒪_L` preserves derived completeness.

The derived base change is the derived coextension of scalars, which is also right adjoint to
restriction of scalars. If a uniformizer `ϖ_L` acts invertibly on `Z ∈ D(Y_ét, 𝒪_L)`, so does the
image of a uniformizer `ϖ_E` of `𝒪_E` (it divides a power of `ϖ_L`), hence `ϖ_E` acts invertibly
on the restriction of scalars of `Z`. So a morphism `Z ⟶ K ⊗ᴸ 𝒪_L` corresponds to a morphism
from this restriction of scalars to the derived complete `K`, which vanishes. -/
theorem derivedCompleteIntegral_derivedBaseChange_integersShrinkMap
    {K : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l E))}
    (hK : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l L
      ((derivedBaseChange (PadicAlgCl.integersShrinkMap l E L) Y
        exists_isDerivedBaseChange_integersShrinkMap).obj K) := by
  let := (PadicAlgCl.integersShrinkMap.{w, u} l E L).toAlgebra
  obtain ⟨n, b, φ, hφ⟩ := PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap.{w, u} l E L
  have := (coextendRestrictScalarsAdj b φ hφ Y).isLeftAdjoint
  let e := (derivedBaseChangeAdjunction (PadicAlgCl.integersShrinkMap l E L) Y
    exists_isDerivedBaseChange_integersShrinkMap).leftAdjointUniq
      (derivedCoextendRestrictScalarsAdj b φ hφ Y)
  let adj := derivedRestrictCoextendScalarsAdj (Λ := Shrink.{u + 1} (PadicAlgCl.integers l E))
    (Λ' := Shrink.{u + 1} (PadicAlgCl.integers l L)) Y
  obtain ⟨ϖE, hϖE, hIE⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  obtain ⟨ϖL, hϖL, hIL⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l L
  replace hK := (_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖE hIE K).1 hK
  refine (_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖL hIL _).2 ?_
  intro Z f (hZ : IsIso (ϖL • 𝟙 Z))
  -- the image of `ϖ_E` acts invertibly on `Z`
  obtain ⟨k, c, hc⟩ := PadicAlgCl.exists_dvd_pow_of_mem_maximalIdealShrink
    (x := PadicAlgCl.integersShrinkMap l E L ϖE) (y := ϖL)
    (nonZeroDivisors.ne_zero (PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E L hϖE))
    (hIL ▸ Ideal.mem_span_singleton_self ϖL)
  have hk : IsIso (ϖL ^ k • 𝟙 Z) :=
    _root_.DerivedCategory.smulInvertible.pow (J := Y.smallEtaleTopology) hZ k
  have hZ' : IsIso (PadicAlgCl.integersShrinkMap l E L ϖE • 𝟙 Z) := by
    refine isIso_of_isIso_comp_of_isIso_comp _ (c • 𝟙 Z) ?_ ?_
    · rwa [Linear.smul_comp, Category.id_comp, smul_smul, ← hc]
    · rwa [Linear.smul_comp, Category.id_comp, smul_smul, mul_comm, ← hc]
  -- so `ϖ_E` acts invertibly on the restriction of scalars of `Z`
  have hRZ : _root_.DerivedCategory.smulInvertible Y.smallEtaleTopology ϖE
      ((derivedRestrictScalars (algebraMap _ _) Y).obj Z) := by
    change IsIso (ϖE • 𝟙 _)
    rw [← CategoryTheory.Functor.map_id, ← derivedRestrictScalars_map_smul]
    exact Functor.map_isIso _ _
  have h₀ : f ≫ e.hom.app K = 0 := by
    rw [← (adj.homEquiv _ _).apply_symm_apply (f ≫ e.hom.app K),
      hK ((adj.homEquiv _ _).symm (f ≫ e.hom.app K)) hRZ, Adjunction.homEquiv_unit,
      Functor.map_zero, Limits.comp_zero]
  rw [← cancel_mono (e.hom.app K), h₀, Limits.zero_comp]

/-- The derived base change `D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_L)` between the integral
stages, as a functor between the full subcategories of derived complete objects. -/
noncomputable abbrev derivedCompleteIntegralScalarExtensionAux :
    (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).FullSubcategory ⥤
      (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l L).FullSubcategory :=
  (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l L).lift
    ((_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι ⋙
      derivedBaseChange (PadicAlgCl.integersShrinkMap l E L) Y
        exists_isDerivedBaseChange_integersShrinkMap)
    fun K ↦ derivedCompleteIntegral_derivedBaseChange_integersShrinkMap K.property

/-- The derived base change `D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_L)` between the integral
stages. -/
noncomputable def derivedCompleteIntegralScalarExtension :
    DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l L :=
  derivedCompleteIntegralScalarExtensionAux l E L

noncomputable instance : (derivedCompleteIntegralScalarExtension (Y := Y) l E L).CommShift ℤ :=
  inferInstanceAs ((derivedCompleteIntegralScalarExtensionAux (Y := Y) l E L).CommShift ℤ)

instance : (derivedCompleteIntegralScalarExtension (Y := Y) l E L).IsTriangulated :=
  inferInstanceAs (derivedCompleteIntegralScalarExtensionAux (Y := Y) l E L).IsTriangulated

lemma derivedCompleteIntegralScalarExtension_map_smul
    (r : Shrink.{u + 1} (PadicAlgCl.integers l E)) {K₁ K₂} (f : K₁ ⟶ K₂) :
    (derivedCompleteIntegralScalarExtension (Y := Y) l E L).map (r • f) =
      PadicAlgCl.integersShrinkMap l E L r •
        (derivedCompleteIntegralScalarExtension (Y := Y) l E L).map f :=
  ObjectProperty.hom_ext _ (derivedBaseChange_map_smul _ Y _ r f.hom)

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L] in
lemma integersShrinkMap_nonZeroDivisors_le :
    nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)) ≤
      (nonZeroDivisors _).comap (PadicAlgCl.integersShrinkMap l E L) := fun _ hx ↦
  PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E L hx

/-- The scalar extension `- ⊗_E L : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, L)` of blueprint
`proposition-inverting-ell--2`: the functor induced on the rationalizations by the derived
base change along `𝒪_E ⟶ 𝒪_L`. -/
noncomputable abbrev derivedCompleteRationalScalarExtension :
    DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l L :=
  Rationalization.mapOfRingHom (PadicAlgCl.integersShrinkMap l E L)
    (integersShrinkMap_nonZeroDivisors_le l E L) (derivedCompleteIntegralScalarExtension l E L)
    (derivedCompleteIntegralScalarExtension_map_smul l E L)

/-- Scalar extension is an exact triangulated functor.

Let `E ⊆ L` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`. The scalar extension
`- ⊗_E L : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, L)` (`proposition-inverting-ell--2`), induced on
the rationalizations by the derived base change `K ↦ K ⊗ᴸ_{𝒪_E} 𝒪_L`, is a triangulated
functor: it commutes with shifts and carries distinguished triangles to distinguished triangles.

As in the blueprint, it is the composite of the derived base change, which is triangulated as the
left adjoint of the triangulated restriction of scalars, and of the rationalization; the induced
functor on the rationalizations is triangulated
(`CategoryTheory.Rationalization.isTriangulated_mapOfRingHom`). The derived base change exists
and preserves derived completeness
(`AlgebraicGeometry.Etale.exists_isDerivedBaseChange_integersShrinkMap`,
`AlgebraicGeometry.Etale.derivedCompleteIntegral_derivedBaseChange_integersShrinkMap`). By
`AlgebraicGeometry.Etale.nonempty_iso_fromIntegral_of_isDerivedBaseChange` the functor does not
depend on the integral representatives. -/
instance isTriangulated_derivedCompleteRationalScalarExtension :
    (derivedCompleteRationalScalarExtension (Y := Y) l E L).IsTriangulated :=
  inferInstance

/-- The scalar extension of the rationalization of an integral object `K` is the rationalization
of its derived base change. -/
noncomputable def derivedCompleteRationalScalarExtensionFromIntegralIso
    (K : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E) :
    (derivedCompleteRationalScalarExtension l E L).obj
        ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K) ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l L).obj
        ((derivedCompleteIntegralScalarExtension l E L).obj K) :=
  (Localization.Lifting.iso (Rationalization.Q _ _)
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) _)
    (derivedCompleteIntegralScalarExtension l E L ⋙ Rationalization.Q _ _)
    (derivedCompleteRationalScalarExtension l E L)).app K

end Rational

end Etale

end AlgebraicGeometry
