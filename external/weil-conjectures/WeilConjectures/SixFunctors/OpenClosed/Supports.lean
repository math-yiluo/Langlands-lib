/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.Algebra.Homology.KInjectiveResolution

/-!
# The support-localization triangle of a complex of injective sheaves

Let `j : U ⟶ X` be an open immersion with closed complement `s : Z ⟶ X`. For a complex `I` of
étale sheaves on `X` put

`A(I) = s_* s^! I = ker(I ⟶ j_* j^* I)`, `B(I) = I`, `C(I) = j_* j^* I`,

the complex of sections supported on `Z`, the complex itself and the restriction to the open
part. If the terms of `I` are injective, the restriction `I ⟶ j_* j^* I` is a degreewise split
epimorphism, so `0 ⟶ A(I) ⟶ B(I) ⟶ C(I) ⟶ 0` is a short exact sequence of complexes
(`lemma-local-cohomology-right-adjoint--2`). The map from the mapping cone of the inclusion
`u : A(I) ⟶ B(I)` to `C(I)`, `(b, a) ↦ [b]`, is then a quasi-isomorphism, and
the *support-localization triangle* `A(I) ⟶ B(I) ⟶ C(I) ⟶ A(I)[1]` is the image of the cone triangle
in the derived category, with its third term identified with `C(I)`
(`lemma-local-cohomology-right-adjoint--2`).

## Main definitions

- `AlgebraicGeometry.Etale.supportsShortComplex`: the short complex `A(I) ⟶ B(I) ⟶ C(I)`.
- `AlgebraicGeometry.Etale.supportLocalizationTriangle`: the support-localization triangle.

## Main statements

- `AlgebraicGeometry.Etale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`
- `AlgebraicGeometry.Etale.shortExact_supportsShortComplex`
- `AlgebraicGeometry.Etale.quasiIso_descShortComplex_supportsShortComplex`
- `AlgebraicGeometry.Etale.supportLocalizationTriangle_distinguished`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U Z X : Scheme.{u}} (j : U ⟶ X) (s : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion s]

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJZ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [hJX : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJX hJZ in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: The exact sequence of supported sections
for injective objects

For an injective étale sheaf `I` on `X` and an open immersion `j` with closed complement `s`,
the restriction `I ⟶ j_* j^* I` (the unit of `j^* ⊣ j_*`) is a split epimorphism. Put
`F = j_* j^* I`. The counit `j_! j^* F ⟶ F` is a monomorphism
(`AlgebraicGeometry.Etale.shortExact_openClosedShortComplex`), so by injectivity of `I` the map
`j_! j^* F ⟶ I` adjoint to the counit `j^* j_* j^* I ⟶ j^* I` extends to `σ : F ⟶ I`; `σ` is a
section of the unit, as both `σ ≫ η_I` and `𝟙_F` are adjoint to the counit. -/
theorem isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective
    (hjs : Set.range s.base = (Set.range j.base)ᶜ) (I : Sheaf X.smallEtaleTopology A)
    [Injective I] :
    IsSplitEpi ((upperStarLowerStarAdjunction A j).unit.app I) := by
  let adj := upperStarLowerStarAdjunction A j
  let adj' := openImmersionLowerShriekUpperStarAdjunction A j
  let F := (j)_*[A].obj ((j)^*[A].obj I)
  have : Mono (adj'.counit.app F) :=
    (shortExact_openClosedShortComplex A j s F hjs).mono_f
  let φ : (j)_!open[A].obj ((j)^*[A].obj F) ⟶ I := (adj'.homEquiv _ _).symm (adj.counit.app _)
  let σ : F ⟶ I := Injective.factorThru φ (adj'.counit.app F)
  have hσ : adj'.counit.app F ≫ σ = φ := Injective.comp_factorThru _ _
  refine ⟨⟨σ, ?_⟩⟩
  apply (adj.homEquiv _ _).symm.injective
  have h₁ : (j)^*[A].map σ = adj.counit.app ((j)^*[A].obj I) := by
    have := congrArg (adj'.homEquiv _ _) hσ
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp, ← assoc,
      adj'.right_triangle_components, id_comp] at this
    exact this
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, assoc, h₁]
  erw [adj.left_triangle_components]
  simp

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: The support-localization triangle of a
complex: the construction

The restriction `I ⟶ j_* j^* I` of a complex of étale sheaves to the open part, degreewise the
unit of `j^* ⊣ j_*`. -/
@[simps]
noncomputable def supportsUnit (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    I ⟶ (((j)^*[A] ⋙ (j)_*[A]).mapHomologicalComplex _).obj I where
  f n := (upperStarLowerStarAdjunction A j).unit.app (I.X n)
  comm' n m _ := ((upperStarLowerStarAdjunction A j).unit.naturality (I.d n m)).symm

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: The support-localization triangle of a
complex: the construction

The short complex `A(I) ⟶ B(I) ⟶ C(I)` of a complex `I` of étale sheaves: `B(I) = I`,
`C(I) = j_* j^* I`, and `A(I) = s_* s^! I` is the kernel of the restriction `I ⟶ j_* j^* I`, the
complex of sections supported on the closed complement of `j`. The first map is the inclusion
`u : A(I) ⟶ B(I)`. -/
@[simps]
noncomputable def supportsShortComplex (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    ShortComplex (CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :=
  ShortComplex.mk (kernel.ι (supportsUnit A j I)) (supportsUnit A j I) (kernel.condition _)

include hJX hJZ in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: The exact sequence of supported sections
for injective objects

For a complex `I` of injective étale sheaves, `0 ⟶ s_* s^! I ⟶ I ⟶ j_* j^* I ⟶ 0` is a short exact
sequence of complexes: the restriction `I ⟶ j_* j^* I` is a degreewise (split) epimorphism by
`AlgebraicGeometry.Etale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`. This
is the étale form, the site of the purity chapter (`def-pur-conventions`); the pro-étale form is
`AlgebraicGeometry.ProEtale.shortExact_supportsShortComplex`. -/
theorem shortExact_supportsShortComplex (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)] :
    (supportsShortComplex A j I).ShortExact := by
  have : Epi (supportsUnit A j I) := by
    refine HomologicalComplex.epi_of_epi_f _ fun n ↦ ?_
    have := isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective A j s hjs (I.X n)
    rw [supportsUnit_f]
    infer_instance
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    (by rw [supportsShortComplex_f]; infer_instance) this

include hJX hJZ in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Pointer to the properties of
`lemma-local-cohomology-right-adjoint--2`

For a complex `I` of injective étale sheaves, the map `Cone(u) ⟶ C(I)`, `(b, a) ↦ [b]`, from the
mapping cone of the inclusion `u : s_* s^! I ⟶ I` to `j_* j^* I` is a quasi-isomorphism, by the
short exact sequence `AlgebraicGeometry.Etale.shortExact_supportsShortComplex`. -/
theorem quasiIso_descShortComplex_supportsShortComplex
    (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)] :
    QuasiIso (CochainComplex.mappingCone.descShortComplex (supportsShortComplex A j I)) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex
    (shortExact_supportsShortComplex A j s hjs I)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Pointer to the properties of
`lemma-local-cohomology-right-adjoint--2`

The *support-localization triangle* `s_* s^! I ⟶ I ⟶ j_* j^* I ⟶ (s_* s^! I)[1]` of a complex `I`
of injective étale sheaves, in the derived category: the triangle of the short exact sequence
`AlgebraicGeometry.Etale.shortExact_supportsShortComplex`. -/
noncomputable def supportLocalizationTriangle (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)] :
    Pretriangulated.Triangle (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  DerivedCategory.triangleOfSES (shortExact_supportsShortComplex A j s hjs I)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Pointer to the properties of
`lemma-local-cohomology-right-adjoint--2`

The support-localization triangle is the image of the cone triangle of the inclusion
`u : s_* s^! I ⟶ I` in the derived category, its third term `Cone(u)` being identified with
`j_* j^* I` through the quasi-isomorphism
`AlgebraicGeometry.Etale.quasiIso_descShortComplex_supportsShortComplex`. -/
noncomputable def supportLocalizationTriangleIso
    (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)] :
    supportLocalizationTriangle A j s hjs I ≅
      DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle (supportsShortComplex A j I).f) :=
  DerivedCategory.triangleOfSESIso _

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Pointer to the properties of
`lemma-local-cohomology-right-adjoint--2`

The support-localization triangle is distinguished. -/
theorem supportLocalizationTriangle_distinguished
    (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)] :
    supportLocalizationTriangle A j s hjs I ∈ distTriang _ :=
  DerivedCategory.triangleOfSES_distinguished _

section Resolution

variable {X' : Scheme.{u}}

/-- The specified resolution `K ⟶ I(K)` of a complex `K` of étale sheaves which is
cohomologically concentrated in degrees `≥ n`: the truncation `K ⟶ τ_{≥ n} K` followed by a chosen
K-injective resolution of `τ_{≥ n} K` by a complex of injective sheaves concentrated in degrees
`≥ n` (`CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE`). -/
noncomputable def injectiveResolutionOfIsGE (K : CochainComplex (Sheaf X'.smallEtaleTopology A) ℤ)
    (n : ℤ) [K.IsGE n] : K.KInjectiveResolution :=
  let R := (CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE (K.truncGE n) n).choose
  ⟨R.I, K.πTruncGE n ≫ R.ι, inferInstance, inferInstance⟩

/-- The terms of the specified resolution `I(K)` are injective. -/
instance injective_injectiveResolutionOfIsGE_I_X
    (K : CochainComplex (Sheaf X'.smallEtaleTopology A) ℤ) (n : ℤ) [K.IsGE n] (m : ℤ) :
    Injective ((injectiveResolutionOfIsGE A K n).I.X m) :=
  (CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE (K.truncGE n) n).choose_spec.2 m

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: The support-localization triangle of a
complex: the construction

For a bounded below complex `K` of étale sheaves on `X` (cohomologically concentrated in degrees
`≥ n`), with specified resolution `K ⟶ I(K)` by a K-injective complex of injective sheaves
(`AlgebraicGeometry.Etale.injectiveResolutionOfIsGE`), the short complex

`A(K) = s_* s^! I(K) ⟶ B(K) = I(K) ⟶ C(K) = j_* j^* I(K)`,

whose first map is the inclusion `u : A(K) ⟶ B(K)` of the supported sections
(`AlgebraicGeometry.Etale.supportsShortComplex`). Here `A(K)` is the kernel of the restriction
`I(K) ⟶ j_* j^* I(K)`, which is `s_* s^! I(K)` by
`AlgebraicGeometry.Etale.closedUpperShriekCompLowerStarIso`. The cone of `u` is
`AlgebraicGeometry.Etale.supportsCone`. As throughout the purity chapter (`def-pur-conventions`)
this is formalised on the small étale site. -/
noncomputable def supportsShortComplexOfIsGE
    (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (n : ℤ) [K.IsGE n] :
    ShortComplex (CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :=
  supportsShortComplex A j (injectiveResolutionOfIsGE A K n).I

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: The support-localization triangle of a
complex: the construction

The cone complex `Cone(u)` of the inclusion `u : A(K) ⟶ B(K)`, with
`Cone(u)^m = A(K)^{m+1} ⊕ B(K)^m` and differential `d(a, b) = (-d_A a, u(a) + d_B b)`
(`CochainComplex.mappingCone`; the blueprint lists the summands in the other order). -/
noncomputable def supportsCone
    (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (n : ℤ) [K.IsGE n] :
    CochainComplex (Sheaf X.smallEtaleTopology A) ℤ :=
  CochainComplex.mappingCone (supportsShortComplexOfIsGE A j K n).f

end Resolution

end Etale

end AlgebraicGeometry
