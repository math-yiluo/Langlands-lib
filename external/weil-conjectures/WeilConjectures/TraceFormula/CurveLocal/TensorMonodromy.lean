/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverProd
public import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverPullback

/-!
# Finite `ℓ`-group monodromy of the tensor product of two lisse complexes

This file proves the step "the complex `N' ⊠ Q'` has finite `ℓ`-group monodromy" of blueprint
`lemma-tangent-cones-on-cover` (i). Let `P₁, P₂` be bounded flat complexes on `V₁, V₂` whose
termwise pullbacks to Galois covers `c₁, c₂` with finite `ℓ`-groups `G₁, G₂` are constant
complexes on bounded complexes of finite `Λ`-modules, and let `ψᵢ : W ⟶ Vᵢ`. Then
`E = Lψ₁^* P₁ ⊗ᴸ Lψ₂^* P₂` is bounded and its cohomology sheaves become constant on finite
`Λ`-modules on the Galois cover `W ×_{V₁ × V₂} (c₁ × c₂)` of `W`, with group `G₁ × G₂`.

## Main statements

- `AlgebraicGeometry.Etale.upperStarHomologyDerivedTensorIso`: on a scheme `T` over `W` on
  which both covers split, `Hⁿ(E)|_T` is the constant sheaf on `Hⁿ(C₁ ⊗ C₂)`.
- `AlgebraicGeometry.Etale.exists_galoisCover_homology_derivedTensor_iso_constantSheaf`: the
  finite `ℓ`-group monodromy of `E`, in the format used by
  `AlgebraicGeometry.Etale.CurveLocalModel.exists_restrictionZeroCover`.

The derived tensor product is computed by the tensor product of complexes, the first factor
being bounded flat, hence K-flat; the constant sheaf functor is monoidal and exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

/-- A product of two `p`-groups is a `p`-group. -/
lemma IsPGroup.prod {p : ℕ} {G₁ G₂ : Type*} [Group G₁] [Group G₂] (h₁ : IsPGroup p G₁)
    (h₂ : IsPGroup p G₂) : IsPGroup p (G₁ × G₂) := by
  rintro ⟨g₁, g₂⟩
  obtain ⟨k₁, hk₁⟩ := h₁ g₁
  obtain ⟨k₂, hk₂⟩ := h₂ g₂
  refine ⟨k₁ + k₂, Prod.ext ?_ ?_⟩
  · rw [Prod.pow_fst, pow_add, pow_mul, hk₁, one_pow, Prod.fst_one]
  · rw [Prod.pow_snd, pow_add, mul_comm, pow_mul, hk₂, one_pow, Prod.snd_one]

namespace CochainComplex

variable {Λ : Type u} [CommRing Λ]

/-- The tensor product of a bounded complex of finite `Λ`-modules with a complex of finite
`Λ`-modules has finite terms. -/
lemma finite_tensorObj_X [Finite Λ] (K L : CochainComplex (ModuleCat.{u} Λ) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] (hK : ∀ n, Finite (K.X n)) (hL : ∀ n, Finite (L.X n))
    (n : ℤ) : Finite ((K ⊗ L).X n) := by
  classical
  let s := Finset.Icc a b
  let φ : ((p : s) → (K.X p ⊗ L.X (n - p) : ModuleCat.{u} Λ)) →ₗ[Λ] (K ⊗ L).X n :=
    ∑ p : s, (HomologicalComplex.ιTensorObj K L p (n - p) n (by omega)).hom ∘ₗ LinearMap.proj p
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, ← Submodule.ker_mkQ (LinearMap.range φ)]
    suffices h : ModuleCat.ofHom (LinearMap.range φ).mkQ = 0 by
      rw [← ModuleCat.hom_ofHom (LinearMap.range φ).mkQ, h]
      simp
    refine HomologicalComplex.mapBifunctor.hom_ext (fun p q hpq ↦ ?_)
    have hpq' : p + q = n := hpq
    obtain rfl : q = n - p := by omega
    by_cases hp : p ∈ s
    · ext x
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply, comp_zero]
      refine (Submodule.Quotient.mk_eq_zero _).2 ⟨Pi.single ⟨p, hp⟩ x, ?_⟩
      rw [LinearMap.sum_apply, Finset.sum_eq_single ⟨p, hp⟩]
      · simp
        rfl
      · intro p' _ hp'
        simp [Pi.single_eq_of_ne hp']
      · simp
    · apply IsZero.eq_of_src
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hp
      rcases hp with hp | hp
      · exact ((curriedTensor _).map_isZero (K.isZero_of_isStrictlyGE a p hp)).obj _
      · exact ((curriedTensor _).map_isZero (K.isZero_of_isStrictlyLE b p hp)).obj _
  have (p : s) : Finite (K.X p ⊗ L.X (n - p) : ModuleCat.{u} Λ) := by
    have : Module.Finite Λ (K.X p) := Module.Finite.of_finite
    have : Module.Finite Λ (L.X (n - p)) := Module.Finite.of_finite
    have : Module.Finite Λ (K.X p ⊗ L.X (n - p) : ModuleCat.{u} Λ) :=
      inferInstanceAs (Module.Finite Λ (TensorProduct Λ (K.X p) (L.X (n - p))))
    exact Module.finite_of_finite Λ
  exact Finite.of_surjective φ hφ

/-- A complex of modules whose term in degree `n` is finite has finite `n`-th homology. -/
lemma finite_homology (K : CochainComplex (ModuleCat.{u} Λ) ℤ) (n : ℤ) [Finite (K.X n)] :
    Finite (K.homology n) := by
  have : Finite (K.cycles n) :=
    Finite.of_injective _ ((ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance)
  exact Finite.of_surjective _ ((ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance)

end CochainComplex

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

attribute [local instance] Sheaf.monoidalCategory

/-- Let `P` be a complex of étale sheaves on `V` whose termwise pullback along `π : P' ⟶ V` is
the constant complex on a complex `C` of `Λ`-modules. If `ψ : W ⟶ V` and `r : T ⟶ W` are such
that `r ≫ ψ` factors through `π` (as `q ≫ π`), then the termwise pullback of `P` to `T` is
the constant complex on `C` (blueprint `lemma-tangent-cones-on-cover`). -/
noncomputable def upperStarMapHomologicalComplexConstantIso {V W T P' : Scheme.{u}}
    {π : P' ⟶ V} {ψ : W ⟶ V} (q : T ⟶ P') (r : T ⟶ W) (h : r ≫ ψ = q ≫ π)
    {P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    {C : CochainComplex (ModuleCat.{u + 1} Λ) ℤ}
    (e : ((π)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P ≅
      ((constantSheaf P'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (.up ℤ)).obj C) :
    ((r)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj
        (((ψ)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (.up ℤ)).obj C :=
  (Functor.mapHomologicalComplexCompIso
      ((Etale.upperStarComp _ r ψ).symm ≪≫ Etale.upperStarComp _ q π (r ≫ ψ) h) (.up ℤ)).app P ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app P).symm ≪≫
    ((q)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).mapIso e ≪≫
    (Functor.mapHomologicalComplexCompIso (constantSheafCompUpperStarIso Λ q) (.up ℤ)).app C

/-- The derived pullback of a complex is its termwise pullback, `Lg^*(Q K) ≅ Q(g^* K)`. -/
noncomputable def leftDerivedUpperStarObjQObjIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    L((g)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj K) :=
  (leftDerivedUpperStarIsoMapDerivedCategory _ g).app _ ≪≫
    ((g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryFactors).app K

/-- The termwise pullback of a bounded flat complex is a bounded flat complex in the same
degrees. -/
lemma isBoundedFlatComplex_upperStar {X Y : Scheme.{u}} (g : X ⟶ Y) {a b : ℤ}
    {P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (hP : IsBoundedFlatComplex Λ a b P) :
    IsBoundedFlatComplex Λ a b
      (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [isBoundedFlatComplex_iff] at hP ⊢
  obtain ⟨_, _, hP⟩ := hP
  exact ⟨inferInstance, inferInstance, fun q ↦
    Functor.PreservesFlat.flat_obj (F := (g)^*[ModuleCat.{u + 1} Λ]) (hP q)⟩

/-- For a bounded flat complex `P`, the derived tensor product `P ⊗ᴸ K` is computed by the
tensor product of complexes. -/
noncomputable def derivedTensorQObjIsoOfIsBoundedFlatComplex {X : Scheme.{u}} {a b : ℤ}
    {P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (hP : IsBoundedFlatComplex Λ a b P)
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (P ⊗ K) :=
  haveI := (isBoundedFlatComplex_iff.1 hP).1
  haveI := (isBoundedFlatComplex_iff.1 hP).2.1
  DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P K
    (CochainComplex.kFlat_of_bounded_of_flat P a b (isBoundedFlatComplex_iff.1 hP).2.2)

/-- The homology sheaves of a constant complex are the constant sheaves on the homology
modules: the constant sheaf functor is exact. -/
noncomputable def homologyQObjConstantSheafIso (X : Scheme.{u})
    (C : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).obj (DerivedCategory.Q.obj
      (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (.up ℤ)).obj C)) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (C.homology n) :=
  haveI : PreservesFiniteColimits (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteColimits (Functor.const _) (presheafToSheaf _ _)
  haveI : PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteLimits (Functor.const _) (presheafToSheaf _ _)
  (DerivedCategory.homologyFunctorFactors _ n).app _ ≪≫
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplexHomologyIso
      (.up ℤ) n).app C

/-- **The tensor product of two complexes with constant pullbacks has constant pulled back
cohomology** (blueprint `lemma-tangent-cones-on-cover`, the complex `N' ⊠ Q'`). Let
`P₁, P₂` be complexes on `V₁, V₂`, with `P₁` bounded flat, whose termwise pullbacks along
`π₁ : P₁' ⟶ V₁` and `π₂ : P₂' ⟶ V₂` are the constant complexes on complexes `C₁, C₂` of
`Λ`-modules. Let `ψᵢ : W ⟶ Vᵢ` and `r : T ⟶ W` be such that each `r ≫ ψᵢ` factors through
`πᵢ`. Then the pullback to `T` of `Hⁿ(Lψ₁^* P₁ ⊗ᴸ Lψ₂^* P₂)` is the constant sheaf on
`Hⁿ(C₁ ⊗ C₂)`. -/
noncomputable def upperStarHomologyDerivedTensorIso {W V₁ V₂ T P₁' P₂' : Scheme.{u}}
    (ψ₁ : W ⟶ V₁) (ψ₂ : W ⟶ V₂) {π₁ : P₁' ⟶ V₁} {π₂ : P₂' ⟶ V₂} (r : T ⟶ W)
    (q₁ : T ⟶ P₁') (q₂ : T ⟶ P₂') (h₁ : r ≫ ψ₁ = q₁ ≫ π₁) (h₂ : r ≫ ψ₂ = q₂ ≫ π₂)
    {P₁ : CochainComplex (Sheaf V₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    {P₂ : CochainComplex (Sheaf V₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    {a b : ℤ} (hP₁ : IsBoundedFlatComplex Λ a b P₁)
    {C₁ C₂ : CochainComplex (ModuleCat.{u + 1} Λ) ℤ}
    (e₁ : ((π₁)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P₁ ≅
      ((constantSheaf P₁'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (.up ℤ)).obj C₁)
    (e₂ : ((π₂)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P₂ ≅
      ((constantSheaf P₂'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (.up ℤ)).obj C₂) (n : ℤ) :
    (r)^*[ModuleCat.{u + 1} Λ].obj ((DerivedCategory.homologyFunctor _ n).obj
      (((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).obj
        (L((ψ₁)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj P₁))).obj
          (L((ψ₂)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj P₂)))) ≅
      (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj ((C₁ ⊗ C₂).homology n) :=
  let c := constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let f₁ := L((r)^*[ModuleCat.{u + 1} Λ]).mapIso (leftDerivedUpperStarObjQObjIso ψ₁ P₁) ≪≫
    leftDerivedUpperStarObjQObjIso r _
  let f₂ := L((r)^*[ModuleCat.{u + 1} Λ]).mapIso (leftDerivedUpperStarObjQObjIso ψ₂ P₂) ≪≫
    leftDerivedUpperStarObjQObjIso r _
  (leftDerivedUpperStarHomologyFunctorIso _ r n).app _ ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      (leftDerivedUpperStarTensorIso _ r _ _ ≪≫
        ((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).mapIso f₁).app _ ≪≫
        ((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).obj _).mapIso f₂ ≪≫
        derivedTensorQObjIsoOfIsBoundedFlatComplex
          (isBoundedFlatComplex_upperStar r (isBoundedFlatComplex_upperStar ψ₁ hP₁)) _ ≪≫
        DerivedCategory.Q.mapIso
          (tensorIso (upperStarMapHomologicalComplexConstantIso q₁ r h₁ e₁)
            (upperStarMapHomologicalComplexConstantIso q₂ r h₂ e₂) ≪≫
            c.mapCochainComplexμIso C₁ C₂)) ≪≫
    homologyQObjConstantSheafIso T (C₁ ⊗ C₂) n

/-- The derived tensor product of the pullbacks of two bounded flat complexes in degrees
`[a₁, b₁]` and `[a₂, b₂]` is concentrated in degrees `[a₁ + a₂, b₁ + b₂]`. -/
lemma isGE_isLE_derivedTensor_leftDerivedUpperStar {W V₁ V₂ : Scheme.{u}}
    (ψ₁ : W ⟶ V₁) (ψ₂ : W ⟶ V₂)
    {P₁ : CochainComplex (Sheaf V₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    {P₂ : CochainComplex (Sheaf V₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    {a₁ b₁ a₂ b₂ : ℤ} (hP₁ : IsBoundedFlatComplex Λ a₁ b₁ P₁)
    (hP₂ : IsBoundedFlatComplex Λ a₂ b₂ P₂) :
    (((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).obj
        (L((ψ₁)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj P₁))).obj
          (L((ψ₂)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj P₂))).IsGE (a₁ + a₂) ∧
      (((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).obj
        (L((ψ₁)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj P₁))).obj
          (L((ψ₂)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj P₂))).IsLE (b₁ + b₂) := by
  have hR₁ := isBoundedFlatComplex_upperStar ψ₁ hP₁
  have hR₂ := isBoundedFlatComplex_upperStar ψ₂ hP₂
  obtain ⟨_, _, -⟩ := isBoundedFlatComplex_iff.1 hR₁
  obtain ⟨_, _, -⟩ := isBoundedFlatComplex_iff.1 hR₂
  let e := ((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).mapIso (leftDerivedUpperStarObjQObjIso ψ₁ P₁)).app _ ≪≫
    ((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).obj _).mapIso (leftDerivedUpperStarObjQObjIso ψ₂ P₂) ≪≫
    derivedTensorQObjIsoOfIsBoundedFlatComplex hR₁ _
  have := CochainComplex.isStrictlyGE_tensorObj
    (((ψ₁)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P₁)
    (((ψ₂)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P₂) a₁ a₂
  have := CochainComplex.isStrictlyLE_tensorObj
    (((ψ₁)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P₁)
    (((ψ₂)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P₂) b₁ b₂
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm _,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm _⟩

/-- **The complex `N' ⊠ Q'` has finite `ℓ`-group monodromy** (blueprint
`lemma-tangent-cones-on-cover` (i)). Let `P₁, P₂` be bounded flat complexes of étale sheaves of
`Λ`-modules on `V₁, V₂`, and `c₁, c₂` Galois covers of `V₁, V₂` with finite `ℓ`-groups
`G₁, G₂` such that the termwise pullback of `Pᵢ` to `cᵢ` is (as a complex) the constant complex
on a bounded complex of finite `Λ`-modules. Then for `ψᵢ : W ⟶ Vᵢ`, the derived tensor product
`E = Lψ₁^* P₁ ⊗ᴸ Lψ₂^* P₂` is bounded, and every cohomology sheaf of `E` becomes constant on a
finite `Λ`-module after pullback to the Galois cover `W ×_{V₁ × V₂} (c₁ × c₂)` of `W`, with
group the finite `ℓ`-group `G₁ × G₂`.

The hypothesis on `Pᵢ` asks for an isomorphism of complexes, not only of the terms: the
cohomology of a complex whose terms are constant need not be constant when the base is not
connected. -/
theorem exists_galoisCover_homology_derivedTensor_iso_constantSheaf [Finite Λ] (ℓ : ℕ)
    {W V₁ V₂ : Scheme.{u}} (ψ₁ : W ⟶ V₁) (ψ₂ : W ⟶ V₂)
    {P₁ : CochainComplex (Sheaf V₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    {P₂ : CochainComplex (Sheaf V₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    {a₁ b₁ a₂ b₂ : ℤ} (hP₁ : IsBoundedFlatComplex Λ a₁ b₁ P₁)
    (hP₂ : IsBoundedFlatComplex Λ a₂ b₂ P₂)
    {G₁ G₂ : Type (u + 1)} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    (hG₁ : IsPGroup ℓ G₁) (hG₂ : IsPGroup ℓ G₂)
    (c₁ : GaloisCover G₁ V₁) (c₂ : GaloisCover G₂ V₂)
    (hc₁ : ∃ (C : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ) (_ : C.IsStrictlyGE a)
      (_ : C.IsStrictlyLE b) (_ : ∀ n, Finite (C.X n)),
      Nonempty (((c₁.π)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P₁ ≅
        ((constantSheaf c₁.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (.up ℤ)).obj C))
    (hc₂ : ∃ (C : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ) (_ : C.IsStrictlyGE a)
      (_ : C.IsStrictlyLE b) (_ : ∀ n, Finite (C.X n)),
      Nonempty (((c₂.π)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj P₂ ≅
        ((constantSheaf c₂.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (.up ℤ)).obj C))
    (E : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eE : E ≅ ((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).obj
        (L((ψ₁)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj P₁))).obj
          (L((ψ₂)^*[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Q.obj P₂))) :
    (∃ a b : ℤ, E.IsGE a ∧ E.IsLE b) ∧ ∀ n : ℤ,
      ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G)
        (c : Scheme.GaloisCover G W) (M : ModuleCat.{u + 1} Λ) (_ : Finite M),
        Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj
            ((DerivedCategory.homologyFunctor _ n).obj E) ≅
          (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  obtain ⟨hE₁, hE₂⟩ := isGE_isLE_derivedTensor_leftDerivedUpperStar ψ₁ ψ₂ hP₁ hP₂
  refine ⟨⟨a₁ + a₂, b₁ + b₂, DerivedCategory.TStructure.t.isGE_of_iso eE.symm _,
    DerivedCategory.TStructure.t.isLE_of_iso eE.symm _⟩, fun n ↦ ?_⟩
  obtain ⟨C₁, a, b, _, _, hC₁, ⟨e₁⟩⟩ := hc₁
  obtain ⟨C₂, -, -, -, -, hC₂, ⟨e₂⟩⟩ := hc₂
  let c₁₂ := c₁.prod c₂ (terminal.from V₁) (terminal.from V₂)
  let c := c₁₂.pullback (pullback.lift ψ₁ ψ₂ (terminal.hom_ext _ _))
  have hc := congrArg (· ≫ pullback.fst (terminal.from V₁) (terminal.from V₂))
    (pullback.condition (f := c₁₂.π) (g := pullback.lift ψ₁ ψ₂ (terminal.hom_ext _ _)))
  have hc' := congrArg (· ≫ pullback.snd (terminal.from V₁) (terminal.from V₂))
    (pullback.condition (f := c₁₂.π) (g := pullback.lift ψ₁ ψ₂ (terminal.hom_ext _ _)))
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, c₁₂,
    GaloisCover.prod_π, GaloisCover.prodπ_fst, GaloisCover.prodπ_snd] at hc hc'
  have h₁ : c.π ≫ ψ₁ = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ c₁.π := by
    rw [Category.assoc]
    exact hc.symm
  have h₂ : c.π ≫ ψ₂ = (pullback.fst _ _ ≫ pullback.snd _ _) ≫ c₂.π := by
    rw [Category.assoc]
    exact hc'.symm
  have := CochainComplex.finite_tensorObj_X C₁ C₂ a b hC₁ hC₂ n
  exact ⟨G₁ × G₂, inferInstance, inferInstance, hG₁.prod hG₂, c, (C₁ ⊗ C₂).homology n,
    CochainComplex.finite_homology _ n,
    ⟨(c.π)^*[ModuleCat.{u + 1} Λ].mapIso ((DerivedCategory.homologyFunctor _ n).mapIso eE) ≪≫
      upperStarHomologyDerivedTensorIso ψ₁ ψ₂ c.π _ _ h₁ h₂ hP₁ e₁ e₂ n⟩⟩

end AlgebraicGeometry.Etale

end
