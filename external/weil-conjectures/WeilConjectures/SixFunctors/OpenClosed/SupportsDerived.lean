/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.SupportedSections
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale
public import WeilConjectures.Algebra.Homology.KInjectiveResolution

/-!
# The support-localization triangle computes the exceptional inverse image

Let `s : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. For a K-injective
complex `I` of injective étale sheaves on `X`, the support-localization triangle

`s_* s^! I ⟶ I ⟶ j_* j^* I ⟶ (s_* s^! I)[1]`

of `WeilConjectures.SixFunctors.OpenClosed.Supports` (the triangle of the short exact sequence of
supported sections, `AlgebraicGeometry.Etale.supportLocalizationTriangle`) is isomorphic to the
supported localization triangle `Rs_! Rs^! I ⟶ I ⟶ Rj_* Lj^* I ⟶ [1]` of the exceptional
formalism (`AlgebraicGeometry.Etale.supportedLocalizationTriangle`), by an isomorphism which is the
identity on `I`. So the first term `s_* s^! I` computes `Rs_* Rs^!`, the third `Rj_* Lj^*`.

The comparison rests on two facts:

* `Lj^*` kills the complex `s_* s^! I` of supported sections;
* there are no maps from an object `T` with `Lj^* T = 0` to `j_* j^* I`, which computes
  `Rj_* Lj^* I` since `j^* I` is K-injective.

The first term `Rs_! Rs^! I` of the supported localization triangle has the same two properties,
and both are the fibre of a map out of `I`, so the two are canonically isomorphic.

We also record the étale base change of the supported localization triangle: for an étale
`v : X' ⟶ X`, the pullback `Lv^*` carries the triangle of `L` isomorphically onto the triangle of
`Lv^* L` for the base-changed pair
(`AlgebraicGeometry.Etale.supportedLocalizationTriangleBaseChangeIso`).

## Main statements

- `AlgebraicGeometry.Etale.exists_iso_supportLocalizationTriangle`: canonicality.
- `AlgebraicGeometry.Etale.exists_supportLocalizationTriangle_iso_of_isGE`: the triangle of a
  bounded below complex.
- `AlgebraicGeometry.Etale.exists_triangleHom_supportedLocalizationTriangle`: functoriality.
- `AlgebraicGeometry.Etale.supportedLocalizationTriangleBaseChangeIso`: étale base change.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Canonical

variable {U Z X : Scheme.{u}} (j : U ⟶ X) (s : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion s]

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJZ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [hJX : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

omit [HasSmallSiteSheafify A] in
include hJX hJZ in
/-- `Lj^*` kills the complex `s_* s^! I` of supported sections of a complex `I` of injective
sheaves: `Lj^*` carries the support-localization triangle to a distinguished triangle whose second
map `j^* I ⟶ j^* j_* j^* I` is an isomorphism, `j^*` of the unit of `j^* ⊣ j_*` being invertible.
-/
lemma isZero_leftDerivedUpperStar_obj_supportsShortComplex_X₁
    (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [∀ n, Injective (I.X n)] :
    IsZero ((L((j)^*[A])).obj (DerivedCategory.Q.obj (supportsShortComplex A j I).X₁)) := by
  have hT := (L((j)^*[A])).map_distinguished _
    (supportLocalizationTriangle_distinguished A j s hjs I)
  refine (Triangle.isZero₁_iff_isIso₂ _ hT).2 ?_
  change IsIso ((L((j)^*[A])).map (DerivedCategory.Q.map (supportsUnit A j I)))
  rw [NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory A j)]
  change IsIso ((DerivedCategory.Q ⋙ ((j)^*[A]).mapDerivedCategory).map (supportsUnit A j I))
  rw [NatIso.isIso_map_iff ((j)^*[A]).mapDerivedCategoryFactors]
  have : IsIso ((((j)^*[A]).mapHomologicalComplex _).map (supportsUnit A j I)) := by
    have (n : ℤ) : IsIso (((((j)^*[A]).mapHomologicalComplex _).map (supportsUnit A j I)).f n) := by
      change IsIso ((j)^*[A].map ((upperStarLowerStarAdjunction A j).unit.app (I.X n)))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  dsimp
  infer_instance

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] [IsClosedImmersion s]
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)] in
/-- The complex `j_* j^* I` of a K-injective complex `I` computes `Rj_* Lj^* I`: it is `j_*` of
the K-injective complex `j^* I`, `j^*` being right adjoint to the exact `j_!`. -/
noncomputable def supportsShortComplexX₃Iso (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.obj (supportsShortComplex A j I).X₃ ≅
      (R((j)_*[A])).obj (DerivedCategory.Q.obj ((((j)^*[A]).mapHomologicalComplex _).obj I)) :=
  haveI : ((j)^*[A]).PreservesKInjectiveComplexes :=
    (openImmersionLowerShriekUpperStarAdjunction A j).preservesKInjectiveComplexes
  DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
    (Iso.refl ((j)^*[A] ⋙ (j)_*[A])) _).app I).symm ≪≫
    (((j)_*[A]).rightDerivedFunctorObjQIso _).symm

omit [HasSmallSiteSheafify A] [IsClosedImmersion s]
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)] in
/-- There are no nonzero maps from an object `T` with `Lj^* T = 0` to the complex `j_* j^* I` of
a K-injective complex `I`, which computes `Rj_* Lj^* I`. -/
lemma subsingleton_hom_Q_obj_supportsShortComplex_X₃
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [I.IsKInjective]
    {T : DerivedCategory (Sheaf X.smallEtaleTopology A)} (hT : IsZero ((L((j)^*[A])).obj T)) :
    Subsingleton (T ⟶ DerivedCategory.Q.obj (supportsShortComplex A j I).X₃) := by
  have := subsingleton_hom_rightDerivedLowerStar_of_isZero A j hT
    (DerivedCategory.Q.obj ((((j)^*[A]).mapHomologicalComplex _).obj I))
  exact ((Iso.refl T).homCongr (supportsShortComplexX₃Iso A j I)).subsingleton

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Localization triangle for the exceptional
inverse image

**Canonicality.** For a K-injective complex `I` of injective étale sheaves on `X`, the
support-localization triangle `s_* s^! I ⟶ I ⟶ j_* j^* I ⟶ (s_* s^! I)[1]` built from the short
exact sequence of supported sections is isomorphic to the supported localization triangle
`Rs_! Rs^! I ⟶ I ⟶ Rj_* Lj^* I ⟶ (Rs_! Rs^! I)[1]` of the exceptional inverse image, by an
isomorphism which is the identity on `I`. Here `Rs_! = Rs_*` as `s` is proper.

The first term of either triangle is supported on `Z` (it is killed by `Lj^*`), and the third
term of either triangle receives no maps from objects supported on `Z`. So the inclusion
`s_* s^! I ⟶ I` factors uniquely through the counit `Rs_! Rs^! I ⟶ I`, the counit factors through
`s_* s^! I ⟶ I`, and the two factorisations are inverse to each other. -/
theorem exists_iso_supportLocalizationTriangle (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    [HasCompactification s]
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) [∀ n, Injective (I.X
        n)]
    [I.IsKInjective] :
    ∃ e : supportLocalizationTriangle (ModuleCat.{u + 1} Λ) j s hjs I ≅
        supportedLocalizationTriangle Λ s j (DerivedCategory.Q.obj I)
          (supportedLocalizationBoundary Λ s j hjs (DerivedCategory.Q.obj I)),
      e.hom.hom₂ = 𝟙 _ := by
  have hT₁ := supportLocalizationTriangle_distinguished (ModuleCat.{u + 1} Λ) j s hjs I
  have hT₂ := supportedLocalizationTriangle_mem_distTriang Λ s j hjs (DerivedCategory.Q.obj I)
  let u : DerivedCategory.Q.obj (supportsShortComplex (ModuleCat.{u + 1} Λ) j I).X₁ ⟶
      DerivedCategory.Q.obj I :=
    DerivedCategory.Q.map (supportsShortComplex (ModuleCat.{u + 1} Λ) j I).f
  let ε : (R(s)_![ModuleCat.{u + 1} Λ]).obj ((R(s)^![Λ]).obj (DerivedCategory.Q.obj I)) ⟶
      DerivedCategory.Q.obj I :=
    (rightDerivedUpperShriekAdjunction Λ s).counit.app (DerivedCategory.Q.obj I)
  have hA : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (DerivedCategory.Q.obj (supportsShortComplex
      (ModuleCat.{u + 1} Λ) j I).X₁)) :=
    isZero_leftDerivedUpperStar_obj_supportsShortComplex_X₁ (ModuleCat.{u + 1} Λ) j s hjs I
  have hR : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj
      ((R(s)_![ModuleCat.{u + 1} Λ]).obj ((R(s)^![Λ]).obj (DerivedCategory.Q.obj I)))) :=
    isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) s j
      (by rw [hjs]; exact disjoint_compl_left) j subset_rfl _
  -- the inclusion `s_* s^! I ⟶ I` lifts through the counit
  obtain ⟨ψ, hψ, -⟩ := existsUnique_comp_counit_of_isZero Λ s j hjs hA u
  -- the counit lifts through the inclusion `s_* s^! I ⟶ I`
  have : Subsingleton ((R(s)_![ModuleCat.{u + 1} Λ]).obj ((R(s)^![Λ]).obj (DerivedCategory.Q.obj I))
      ⟶
      (supportLocalizationTriangle (ModuleCat.{u + 1} Λ) j s hjs I).obj₃) :=
    subsingleton_hom_Q_obj_supportsShortComplex_X₃ (ModuleCat.{u + 1} Λ) j I hR
  obtain ⟨φ, hφ⟩ := Triangle.coyoneda_exact₂ _ hT₁ ε (Subsingleton.elim _ _)
  replace hφ : ε = φ ≫ u := hφ
  have : Subsingleton ((DerivedCategory.Q.obj (supportsShortComplex (ModuleCat.{u + 1} Λ) j
      I).X₁)⟦(1 : ℤ)⟧ ⟶
      (supportLocalizationTriangle (ModuleCat.{u + 1} Λ) j s hjs I).obj₃) :=
    subsingleton_hom_Q_obj_supportsShortComplex_X₃ (ModuleCat.{u + 1} Λ) j I
      (((shiftFunctor _ (1 : ℤ)).map_isZero hA).of_iso
        (((L((j)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).app _))
  have h₁ : ψ ≫ φ = 𝟙 _ := Triangle.cancel_mor₁_of_subsingleton hT₁
    (by change (ψ ≫ φ) ≫ u = 𝟙 _ ≫ u; rw [assoc, ← hφ, hψ, id_comp])
  have h₂ : φ ≫ ψ = 𝟙 _ :=
    (existsUnique_comp_counit_of_isZero Λ s j hjs hR ε).unique
      (by change (φ ≫ ψ) ≫ ε = ε; rw [assoc, hψ]; exact hφ.symm) (id_comp _)
  let e₁ : DerivedCategory.Q.obj (supportsShortComplex (ModuleCat.{u + 1} Λ) j I).X₁ ≅
      (R(s)_![ModuleCat.{u + 1} Λ]).obj ((R(s)^![Λ]).obj (DerivedCategory.Q.obj I)) := ⟨ψ, φ, h₁,
          h₂⟩
  obtain ⟨e, -, he₂⟩ := exists_iso_of_arrow_iso _ _ hT₁ hT₂
    (Arrow.isoMk e₁ (Iso.refl _) (by change ψ ≫ ε = u ≫ 𝟙 _; rw [comp_id]; exact hψ))
  exact ⟨e, he₂⟩

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Localization triangle for the exceptional
inverse image

Let `K` be a bounded below complex of étale sheaves on `X`. Its specified resolution `K ≅ I` by a
bounded below complex of injective sheaves gives the support-localization triangle
`s_* s^! I ⟶ I ⟶ j_* j^* I ⟶ (s_* s^! I)[1]`, which is distinguished
(`AlgebraicGeometry.Etale.supportLocalizationTriangle_distinguished`) and is isomorphic to the
supported localization triangle `s_* Rs^! K ⟶ K ⟶ Rj_* j^* K ⟶ (s_* Rs^! K)[1]`, compatibly with
the identification `I ≅ K`. As throughout the purity chapter (`def-pur-conventions`) this is
the étale form; on the pro-étale site the triangle is
`AlgebraicGeometry.ProEtale.exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit`,
with the sequence of supported sections
`AlgebraicGeometry.ProEtale.shortExact_supportsShortComplex`. -/
theorem exists_supportLocalizationTriangle_iso_of_isGE
    (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    [HasCompactification s]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) [K.IsGE n] :
    ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (_ : ∀ n, Injective
        (I.X n))
      (_ : I.IsKInjective) (eK : DerivedCategory.Q.obj I ≅ K)
      (e : supportLocalizationTriangle (ModuleCat.{u + 1} Λ) j s hjs I ≅
        supportedLocalizationTriangle Λ s j K (supportedLocalizationBoundary Λ s j hjs K)),
      e.hom.hom₂ = eK.hom := by
  obtain ⟨L, _, ⟨eL⟩⟩ := K.exists_iso_Q_obj_of_isGE n
  obtain ⟨R, -, hR⟩ := CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE L n
  have : IsIso (DerivedCategory.Q.map R.ι) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let eK : DerivedCategory.Q.obj R.I ≅ K := (asIso (DerivedCategory.Q.map R.ι)).symm ≪≫ eL.symm
  obtain ⟨e₁, he₁⟩ := exists_iso_supportLocalizationTriangle Λ j s hjs R.I
  obtain ⟨e₂, -, he₂⟩ := exists_iso_of_arrow_iso _ _
    (supportedLocalizationTriangle_mem_distTriang Λ s j hjs _)
    (supportedLocalizationTriangle_mem_distTriang Λ s j hjs K)
    (Arrow.isoMk ((R(s)_![ModuleCat.{u + 1} Λ]).mapIso ((R(s)^![Λ]).mapIso eK)) eK
      ((rightDerivedUpperShriekAdjunction Λ s).counit.naturality eK.hom))
  refine ⟨R.I, hR, inferInstance, eK, e₁ ≪≫ e₂, ?_⟩
  simp [he₁, he₂]

end Canonical

section Functorial

variable {U Z X : Scheme.{u}}

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`: Localization triangle for the exceptional
inverse image

**Functoriality.** A morphism `φ : L ⟶ L'` induces the morphism of supported
localization
triangles with components `(s_* Rs^! φ, φ, Rj_* Lj^* φ)`, in the sense of
`def-pur-triangle-meaning`. -/
theorem exists_triangleHom_supportedLocalizationTriangle
    (s : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion s] [HasCompactification s]
 [IsOpenImmersion j]
    (hjs : Set.range s.base = (Set.range j.base)ᶜ)
    {L L' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : L ⟶ L') :
    ∃ τ : supportedLocalizationTriangle Λ s j L (supportedLocalizationBoundary Λ s j hjs L) ⟶
        supportedLocalizationTriangle Λ s j L' (supportedLocalizationBoundary Λ s j hjs L'),
      τ.hom₁ = (R(s)_![ModuleCat.{u + 1} Λ]).map ((R(s)^![Λ]).map φ) ∧ τ.hom₂ = φ ∧
        τ.hom₃ = (R((j)_*[ModuleCat.{u + 1} Λ])).map ((L((j)^*[ModuleCat.{u + 1} Λ])).map φ) :=
  exists_triangleHom_supportedLocalization Λ s j (by rw [hjs]; exact disjoint_compl_left) φ
    (supportedLocalizationTriangle_mem_distTriang Λ s j hjs L)
    (supportedLocalizationTriangle_mem_distTriang Λ s j hjs L')

end Functorial

section BaseChange

variable {X U Z Z' V V' : Scheme.{u}}

/-- The morphism of triangles from the pullback along `e : U ⟶ X` of the supported localization
triangle of `L` (for the closed immersion `i` with open complement `j`) to the supported
localization triangle of `L'` (for the base changes `i'`, `j'`), given an identification
`τ : Le^* L ≅ L'`. Its components are the restriction of supports
(`AlgebraicGeometry.Etale.supportedRestriction`), `τ`, and the derived base change map
`Le^* Rj_* ⟶ Rj'_* Le₁^*`; the compatibility with the boundaries is
`AlgebraicGeometry.Etale.supportedLocalizationBoundary_baseChange`. -/
noncomputable def supportedLocalizationTriangleBaseChange (e : U ⟶ X) (i : Z ⟶ X) (j : V ⟶ X)
    (i' : Z' ⟶ U) (j' : V' ⟶ U) (g : Z' ⟶ Z) (e₁ : V' ⟶ V)
    [IsClosedImmersion i] [IsOpenImmersion j]
    [IsClosedImmersion i'] [IsOpenImmersion j']
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Set.range i'.base = (Set.range j'.base)ᶜ)
    (hg : IsPullback g i' i e) (sq : CommSq e₁ j' j e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (τ :
        (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    (L((e)^*[ModuleCat.{u + 1} Λ])).mapTriangle.obj
        (supportedLocalizationTriangle Λ i j L (supportedLocalizationBoundary Λ i j hij L)) ⟶
      supportedLocalizationTriangle Λ i' j' L' (supportedLocalizationBoundary Λ i' j' hij' L') :=
  Triangle.homMk _ _ (supportedRestriction Λ e i i' g hg L L' τ) τ.hom
    ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app _ ≫
      (R((j')_*[ModuleCat.{u + 1} Λ])).map ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
          sq).inv.app L ≫
        (L((j')^*[ModuleCat.{u + 1} Λ])).map τ.hom))
    (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).exists.choose_spec.symm
    (by
      change (L((e)^*[ModuleCat.{u + 1} Λ])).map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u
          + 1} Λ) j).unit.app L) ≫ _ =
        τ.hom ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j').unit.app L'
      erw [map_unit_derivedBaseChangeMap_app_assoc]
      simp only [Functor.id_obj, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
      exact ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j').unit.naturality
          τ.hom).symm)
    ((assoc _ _ _).trans ((supportedLocalizationBoundary_baseChange Λ e i j i' j' g e₁ hij hij' hg
      sq L L' τ).trans (assoc _ _ _).symm))

/-- Blueprint `def-pur-triangle-meaning`: Canonicality, functoriality and etale base change of the
triangle

**Étale base change of the supported localization triangle.** For an étale morphism
`v : X' ⟶ X`, a closed immersion `s : Z ⟶ X` with open complement `j : U ⟶ X`, their base changes
`s' : Z' ⟶ X'` and `j' : U' ⟶ X'`, and `L ∈ D(X_ét, Λ)`, the pullback `Lv^*` identifies the
supported localization triangle `s_* Rs^! L ⟶ L ⟶ Rj_* j^* L ⟶ [1]` with the triangle for
`Z' = Z ×_X X'`, `U' = U ×_X X'` and `Lv^* L` (through any identification `τ : Lv^* L ≅ L'`).

This is the étale base-change compatibility of the triangle of
`lemma-local-cohomology-right-adjoint--2`. Its *canonicality* — independence of the injective
resolution: the triangle of supported sections of any injective resolution is isomorphic to the
supported localization triangle by an isomorphism which is the identity on the complex — is
`AlgebraicGeometry.Etale.exists_iso_supportLocalizationTriangle`, and its *functoriality* is
`AlgebraicGeometry.Etale.exists_triangleHom_supportedLocalizationTriangle`.

The first component is the restriction of supports, an isomorphism along an étale morphism
(`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_etale`); the second is `τ`; so the third,
the base change map `Lv^* Rj_* ⟶ Rj'_* Lv₁^*`, is an isomorphism as well. -/
noncomputable def supportedLocalizationTriangleBaseChangeIso (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ]
    (v : U ⟶ X) [AlgebraicGeometry.Etale v] (s : Z ⟶ X) (j : V ⟶ X)
    (s' : Z' ⟶ U) (j' : V' ⟶ U) (g : Z' ⟶ Z) (v₁ : V' ⟶ V)
    [IsClosedImmersion s] [IsOpenImmersion j] [IsClosedImmersion s'] [IsOpenImmersion j']
    (hsj : Set.range s.base = (Set.range j.base)ᶜ)
    (hsj' : Set.range s'.base = (Set.range j'.base)ᶜ)
    (hg : IsPullback g s' s v) (sq : CommSq v₁ j' j v)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((v)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    (L((v)^*[ModuleCat.{u + 1} Λ])).mapTriangle.obj
        (supportedLocalizationTriangle _ s j L (supportedLocalizationBoundary _ s j hsj L)) ≅
      supportedLocalizationTriangle _ s' j' L' (supportedLocalizationBoundary _ s' j' hsj' L') :=
  let φ := supportedLocalizationTriangleBaseChange _ v s j s' j' g v₁ hsj hsj' hg sq L L' τ
  haveI h₁ : IsIso φ.hom₁ := isIso_supportedRestriction_of_etale Λ v s s' g hg L L' τ
  haveI h₂ : IsIso φ.hom₂ := by
    change IsIso τ.hom
    infer_instance
  haveI h₃ : IsIso φ.hom₃ := isIso₃_of_isIso₁₂ φ
    ((L((v)^*[ModuleCat.{u + 1} Λ])).map_distinguished _
      (supportedLocalizationTriangle_mem_distTriang _ s j hsj L))
    (supportedLocalizationTriangle_mem_distTriang _ s' j' hsj' L') h₁ h₂
  haveI := Triangle.isIso_of_isIsos φ h₁ h₂ h₃
  asIso φ

end BaseChange

end Etale

end AlgebraicGeometry
