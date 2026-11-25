/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.CokernelPowTower
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import WeilConjectures.CategoryTheory.Sites.MonoidalUnit
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.SeparableClosureCover
public import WeilConjectures.SixFunctors.ProEtale.SupportCohomologyTrianglePullback
public import WeilConjectures.TateTwist.RootsOfUnityTrivialization

/-!
# Pullback of the sheaves of roots of unity along an arbitrary morphism

Let `g : X ⟶ Y` be a morphism of schemes and `N` a natural number. Pulling back `N`-th roots of
unity along the projections `V ×_Y X ⟶ V` defines a map `μ_N ⟶ g_* μ_N` of sheaves on
`Y_proét`, whose adjoint is a comparison map `g^* μ_N ⟶ μ_N` of sheaves on `X_proét`
(`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafHom`). It is compatible with the power
maps `μ_{m N} ⟶ μ_N` and with composition of morphisms.

If `Y` lives over a field `k` in which `N` is invertible, the comparison map is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_upperStarRootsOfUnitySheafHom`,
`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIsoOfInvertible`). This is checked on the
pro-étale cover `X ×_k Spec kˢᵉᵖ ⟶ X`:

* for a weakly étale `g` the pullback is the restriction to the slice site, and the comparison
  map is the identity of `U ↦ μ_N(Γ(U, 𝒪_U))`
  (`AlgebraicGeometry.ProEtale.isIso_upperStarRootsOfUnityComparison_of_weaklyEtale`);
* for a morphism `h : U' ⟶ U` of schemes over a field `K` containing a primitive `N`-th root of
  unity `ζ`, both `μ_N` are the cokernel `ℤ/N` of `N : ℤ ⟶ ℤ` through `a ↦ ζ ^ a`
  (`AlgebraicGeometry.ProEtale.isColimitUnitToRootsOfUnitySheaf`), and the comparison map is the
  identification `h^* ℤ ≅ ℤ` of the units
  (`AlgebraicGeometry.ProEtale.isIso_upperStarRootsOfUnityComparison_of_field`);
* the comparison maps are compatible with composition
  (`AlgebraicGeometry.ProEtale.upperStarRootsOfUnityComparison_comp`), and the base change
  `X ×_k kˢᵉᵖ ⟶ X` of `g` factors as `X ×_k kˢᵉᵖ ⟶ Y ×_k kˢᵉᵖ ⟶ Y`.

The comparison maps are first defined for the sheaf `U ↦ μ_N(Γ(U, 𝒪_U))`
(`AlgebraicGeometry.ProEtale.rootsOfUnityPresheafSheaf`) and then transported to its
sheafification `AlgebraicGeometry.ProEtale.rootsOfUnitySheaf` along
`AlgebraicGeometry.ProEtale.rootsOfUnitySheafIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y Z : Scheme.{u}}

/-! ### The comparison map -/

/-- The sheaf `U ↦ μ_N(Γ(U, 𝒪_U))` on `X_proét`, before sheafification
(`AlgebraicGeometry.ProEtale.isSheaf_rootsOfUnityPresheaf`). -/
noncomputable abbrev rootsOfUnityPresheafSheaf (X : Scheme.{u}) (N : ℕ) :
    Sheaf (ProEt.topology X) Ab.{u + 1} :=
  ⟨rootsOfUnityPresheaf X N, isSheaf_rootsOfUnityPresheaf X N⟩

/-- The map of presheaves `μ_N(Γ(V, 𝒪_V)) ⟶ μ_N(Γ(V ×_Y X, 𝒪))` on `Y_proét`, pulling back roots
of unity along the projection `V ×_Y X ⟶ V`. -/
noncomputable def rootsOfUnityPresheafToPullback (g : X ⟶ Y) (N : ℕ) :
    rootsOfUnityPresheaf Y N ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op ⋙ rootsOfUnityPresheaf X N where
  app V := (CommRingCat.rootsOfUnityFunctor N).map (Scheme.Γ.map (pullback.fst V.unop.hom g).op)
  naturality V W f := by
    rw [rootsOfUnityPresheaf_map, Functor.comp_map, rootsOfUnityPresheaf_map, ← Functor.map_comp,
      ← Functor.map_comp, ← Scheme.Γ_map_op, ← Scheme.Γ_map_op, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp]
    congr 3
    exact (pullback.lift_fst _ _ _).symm

lemma rootsOfUnityPresheafToPullback_app (g : X ⟶ Y) (N : ℕ) (V : Y.ProEtᵒᵖ) :
    (rootsOfUnityPresheafToPullback g N).app V =
      (CommRingCat.rootsOfUnityFunctor N).map (pullback.fst V.unop.hom g).appTop :=
  rfl

/-- The map `μ_N ⟶ g_* μ_N` of sheaves on `Y_proét`, pulling back roots of unity along the
projections `V ×_Y X ⟶ V`. -/
noncomputable def rootsOfUnityToLowerStar (g : X ⟶ Y) (N : ℕ) :
    rootsOfUnityPresheafSheaf Y N ⟶ (g)_*[Ab.{u + 1}].obj (rootsOfUnityPresheafSheaf X N) :=
  ObjectProperty.homMk (rootsOfUnityPresheafToPullback g N)

/-- The comparison map `g^* μ_N ⟶ μ_N` of sheaves on `X_proét`: the adjoint of
`AlgebraicGeometry.ProEtale.rootsOfUnityToLowerStar`. -/
noncomputable def upperStarRootsOfUnityComparison (g : X ⟶ Y) (N : ℕ) :
    (g)^*[Ab.{u + 1}].obj (rootsOfUnityPresheafSheaf Y N) ⟶ rootsOfUnityPresheafSheaf X N :=
  ((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).symm (rootsOfUnityToLowerStar g N)

lemma homEquiv_upperStarRootsOfUnityComparison (g : X ⟶ Y) (N : ℕ) :
    (upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _
      (upperStarRootsOfUnityComparison g N) = rootsOfUnityToLowerStar g N :=
  Equiv.apply_symm_apply _ _

@[reassoc]
lemma unit_app_comp_lowerStar_map_upperStarRootsOfUnityComparison (g : X ⟶ Y) (N : ℕ) :
    (upperStarLowerStarAdjunction Ab.{u + 1} g).unit.app _ ≫
        (g)_*[Ab.{u + 1}].map (upperStarRootsOfUnityComparison g N) =
      rootsOfUnityToLowerStar g N := by
  rw [← homEquiv_upperStarRootsOfUnityComparison, Adjunction.homEquiv_unit]

/-! ### Compatibility with composition and with the power maps -/

/-- The maps `μ_N ⟶ g_* μ_N` are compatible with composition: for `a : X ⟶ Y` and `b : Y ⟶ Z`,
the map for `a ≫ b` is `μ_N ⟶ b_* μ_N ⟶ b_* a_* μ_N ≅ (a ≫ b)_* μ_N`. -/
lemma rootsOfUnityToLowerStar_comp (a : X ⟶ Y) (b : Y ⟶ Z) (N : ℕ) :
    rootsOfUnityToLowerStar b N ≫ (b)_*[Ab.{u + 1}].map (rootsOfUnityToLowerStar a N) ≫
        (lowerStarComp Ab.{u + 1} a b).hom.app _ =
      rootsOfUnityToLowerStar (a ≫ b) N := by
  apply Sheaf.hom_ext
  ext V : 2
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app, lowerStarComp_hom_app_hom_app, lowerStar_map_hom_app]
  simp only [rootsOfUnityToLowerStar, ObjectProperty.homMk_hom, rootsOfUnityPresheafToPullback_app,
    rootsOfUnityPresheaf_map, ← Functor.map_comp, ← Scheme.Hom.comp_appTop]
  congr 2
  exact MorphismProperty.Over.pullbackComp_left_fst_fst a b V.unop

/-- The comparison maps `g^* μ_N ⟶ μ_N` are compatible with composition: for `a : X ⟶ Y` and
`b : Y ⟶ Z`, the comparison map of `a ≫ b` is `(a ≫ b)^* μ_N ≅ a^* b^* μ_N ⟶ a^* μ_N ⟶ μ_N`. -/
lemma upperStarRootsOfUnityComparison_comp (a : X ⟶ Y) (b : Y ⟶ Z) (N : ℕ) :
    (upperStarComp Ab.{u + 1} a b).hom.app _ ≫
        (a)^*[Ab.{u + 1}].map (upperStarRootsOfUnityComparison b N) ≫
          upperStarRootsOfUnityComparison a N =
      upperStarRootsOfUnityComparison (a ≫ b) N := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} (a ≫ b)).homEquiv _ _).injective
  rw [homEquiv_upperStarRootsOfUnityComparison, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, upperStarComp_hom_app_unit_app, Category.assoc,
    ← rootsOfUnityToLowerStar_comp, ← NatTrans.naturality, Adjunction.comp_unit_app]
  have h : (upperStarLowerStarAdjunction Ab.{u + 1} a).unit.app _ ≫
      (a)_*[Ab.{u + 1}].map ((a)^*[Ab.{u + 1}].map (upperStarRootsOfUnityComparison b N) ≫
        upperStarRootsOfUnityComparison a N) =
      upperStarRootsOfUnityComparison b N ≫ rootsOfUnityToLowerStar a N := by
    rw [Functor.map_comp, ← Functor.comp_map,
      ← (upperStarLowerStarAdjunction Ab.{u + 1} a).unit.naturality_assoc, Functor.id_map,
      unit_app_comp_lowerStar_map_upperStarRootsOfUnityComparison]
  rw [Functor.comp_map, Category.assoc, ← Functor.map_comp_assoc, h, Functor.map_comp_assoc,
    unit_app_comp_lowerStar_map_upperStarRootsOfUnityComparison_assoc]

lemma rootsOfUnityToLowerStar_pow (g : X ⟶ Y) (N m : ℕ) :
    ObjectProperty.homMk (rootsOfUnityPresheafPow Y N m) ≫ rootsOfUnityToLowerStar g N =
      rootsOfUnityToLowerStar g (m * N) ≫
        (g)_*[Ab.{u + 1}].map (ObjectProperty.homMk (rootsOfUnityPresheafPow X N m)) := by
  apply Sheaf.hom_ext
  ext V : 2
  exact ((CommRingCat.rootsOfUnityPow N m).naturality _).symm

/-- The comparison maps `g^* μ_N ⟶ μ_N` are compatible with the power maps `μ_{m N} ⟶ μ_N`. -/
@[reassoc]
lemma upperStar_map_pow_comp_upperStarRootsOfUnityComparison (g : X ⟶ Y) (N m : ℕ) :
    (g)^*[Ab.{u + 1}].map (ObjectProperty.homMk (rootsOfUnityPresheafPow Y N m)) ≫
        upperStarRootsOfUnityComparison g N =
      upperStarRootsOfUnityComparison g (m * N) ≫
        ObjectProperty.homMk (rootsOfUnityPresheafPow X N m) := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_upperStarRootsOfUnityComparison, homEquiv_upperStarRootsOfUnityComparison,
    rootsOfUnityToLowerStar_pow]

/-! ### The weakly étale case -/

/-- For a weakly étale `g`, the adjoint of `μ_N ⟶ g_* μ_N` for the restriction to the slice site
is the identity of `U ↦ μ_N(Γ(U, 𝒪_U))`. -/
lemma localizationRestrictionLowerStarAdjunction_homEquiv_symm_rootsOfUnityToLowerStar
    (g : X ⟶ Y) [hg : WeaklyEtale g] (N : ℕ) :
    ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} g hg).homEquiv _ _).symm
      (rootsOfUnityToLowerStar g N) = (localizationRestrictionRootsOfUnityIso g N).hom := by
  apply Sheaf.hom_ext
  ext V : 2
  simp only [localizationRestrictionLowerStarAdjunction, Adjunction.homEquiv_counit,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.sheafPushforwardContinuous_counit_app_hom_app,
    MorphismProperty.Over.mapPullbackAdj_unit_app]
  rw [localizationRestriction_map_hom_app]
  simp only [rootsOfUnityToLowerStar, ObjectProperty.homMk_hom, rootsOfUnityPresheafToPullback_app,
    rootsOfUnityPresheaf_map, ← Functor.map_comp, ← Scheme.Hom.comp_appTop]
  erw [Quiver.Hom.unop_op, pullback.lift_fst, Scheme.Hom.id_appTop, CategoryTheory.Functor.map_id]
  rfl

/-- For a weakly étale `g`, the comparison map `g^* μ_N ⟶ μ_N` is an isomorphism: `g^*` is the
restriction to the slice site, under which the comparison map is the identity. -/
theorem isIso_upperStarRootsOfUnityComparison_of_weaklyEtale (g : X ⟶ Y) [hg : WeaklyEtale g]
    (N : ℕ) : IsIso (upperStarRootsOfUnityComparison g N) := by
  have h : upperStarRootsOfUnityComparison g N =
      (upperStarIsoLocalizationRestriction Ab.{u + 1} g hg).hom.app _ ≫
        ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} g hg).homEquiv _ _).symm
          (rootsOfUnityToLowerStar g N) := by
    rw [upperStarRootsOfUnityComparison, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      upperStarIsoLocalizationRestriction,
      ← Adjunction.leftAdjointUniq_hom_app_counit _
        (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g hg),
      NatTrans.naturality_assoc]
  rw [h, localizationRestrictionLowerStarAdjunction_homEquiv_symm_rootsOfUnityToLowerStar]
  infer_instance

/-! ### Over a field containing a primitive root of unity -/

section Field

variable {K : Type u} [Field K] {U U' : Scheme.{u}}

/-- On underlying presheaves, the map `ℤ ⟶ μ_N`, `a ↦ ζ ^ a`, read after the unit of
`sheafToPresheaf`, is the map of presheaves `a ↦ ζ ^ a`. -/
lemma ε_comp_map_unitToRootsOfUnitySheaf_comp_hom (f : U ⟶ Spec (.of K)) {N : ℕ} [NeZero N]
    {ζ : K} (hζ : ζ ^ N = 1) :
    ε (sheafToPresheaf (ProEt.topology U) Ab.{u + 1}) ≫
      (sheafToPresheaf (ProEt.topology U) Ab.{u + 1}).map
        (unitToRootsOfUnitySheaf f hζ ≫ (rootsOfUnitySheafIso U N).hom) =
      unitToRootsOfUnityPresheaf f (rootsOfUnity.mkOfPowEq ζ hζ) := by
  rw [ε_sheafToPresheaf_eq_toSheafify, unitToRootsOfUnitySheaf_eq, Functor.map_comp]
  have h := toSheafify_naturality (ProEt.topology U)
    (unitToRootsOfUnityPresheaf f (rootsOfUnity.mkOfPowEq ζ hζ))
  have h' : toSheafify (ProEt.topology U) (rootsOfUnityPresheaf U N) ≫
      (sheafToPresheaf (ProEt.topology U) Ab.{u + 1}).map (rootsOfUnitySheafIso U N).hom = 𝟙 _ :=
    congrArg (·.hom) (sheafificationIso
      ⟨rootsOfUnityPresheaf U N, isSheaf_rootsOfUnityPresheaf U N⟩).hom_inv_id
  erw [← reassoc_of% h, h', Category.comp_id]

/-- The unit comparison `η : h^* ℤ ⟶ ℤ` of the pullback is the adjoint of the unit comparison
`ε : ℤ ⟶ h_* ℤ` of the pushforward. -/
lemma homEquiv_η_upperStar (h : U' ⟶ U) :
    (upperStarLowerStarAdjunction Ab.{u + 1} h).homEquiv _ _ (η (h)^*[Ab.{u + 1}]) =
      ε (h)_*[Ab.{u + 1}] :=
  Equiv.apply_symm_apply _ _

/-- For a morphism `h : U' ⟶ U` of schemes over a field `K` and `ζ ∈ K` with `ζ ^ N = 1`, the
comparison map `h^* μ_N ⟶ μ_N` corresponds to the identification `h^* ℤ ≅ ℤ` through the maps
`ℤ ⟶ μ_N`, `a ↦ ζ ^ a`. -/
lemma upperStar_map_unitToRootsOfUnitySheaf_comp_upperStarRootsOfUnityComparison (h : U' ⟶ U)
    (fU : U ⟶ Spec (.of K)) (fU' : U' ⟶ Spec (.of K)) (hh : h ≫ fU = fU') {N : ℕ} [NeZero N]
    {ζ : K} (hζ : ζ ^ N = 1) :
    (h)^*[Ab.{u + 1}].map (unitToRootsOfUnitySheaf fU hζ ≫ (rootsOfUnitySheafIso U N).hom) ≫
        upperStarRootsOfUnityComparison h N =
      η (h)^*[Ab.{u + 1}] ≫ unitToRootsOfUnitySheaf fU' hζ ≫ (rootsOfUnitySheafIso U' N).hom := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} h).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, homEquiv_upperStarRootsOfUnityComparison,
    Adjunction.homEquiv_naturality_right, homEquiv_η_upperStar]
  apply Sheaf.hom_ext_of_ε_comp
  rw [(sheafToPresheaf _ _).map_comp (unitToRootsOfUnitySheaf fU hζ ≫ _), ← Category.assoc,
    ε_comp_map_unitToRootsOfUnitySheaf_comp_hom, Functor.map_comp, ← Category.assoc]
  ext V : 2
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app]
  have h₁ := congr_app (ε_comp_map_unitToRootsOfUnitySheaf_comp_hom fU' hζ)
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).op.obj V)
  rw [NatTrans.comp_app] at h₁
  erw [h₁]
  simp only [unitToRootsOfUnityPresheaf, rootsOfUnityToLowerStar, ObjectProperty.ι_map,
    ObjectProperty.homMk_hom, rootsOfUnityPresheafToPullback_app, Category.assoc,
    ← Functor.map_comp]
  congr 2
  rw [fieldToSections, fieldToSections, Category.assoc, ← Scheme.Hom.comp_appTop,
    pullback.condition_assoc, hh]
  rfl

/-- For a morphism `h : U' ⟶ U` of schemes over a field `K` containing a primitive `N`-th root of
unity, the comparison map `h^* μ_N ⟶ μ_N` is an isomorphism: both `μ_N` are the cokernel of
`N : ℤ ⟶ ℤ`, and `h^*` preserves cokernels. -/
theorem isIso_upperStarRootsOfUnityComparison_of_field (h : U' ⟶ U) (fU : U ⟶ Spec (.of K))
    (fU' : U' ⟶ Spec (.of K)) (hh : h ≫ fU = fU') {N : ℕ} [NeZero N] {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) : IsIso (upperStarRootsOfUnityComparison h N) := by
  have key := upperStar_map_unitToRootsOfUnitySheaf_comp_upperStarRootsOfUnityComparison h fU fU'
    hh hζ.pow_eq_one
  have : IsIso ((h)^*[Ab.{u + 1}].map (rootsOfUnitySheafIso U N).hom ≫
      upperStarRootsOfUnityComparison h N ≫ (rootsOfUnitySheafIso U' N).inv) := by
    refine Cofork.IsColimit.isIso_of_π_comp_eq
      (isColimitCoforkMapOfIsColimit' (h)^*[Ab.{u + 1}] _
        (isColimitUnitToRootsOfUnitySheaf fU hζ))
      (isColimitCokernelCoforkOfIsoHomComp (asIso (η (h)^*[Ab.{u + 1}])) ?_ _
        (isColimitUnitToRootsOfUnitySheaf fU' hζ)) _ ?_
    · rw [Functor.map_zsmul, CategoryTheory.Functor.map_id, Preadditive.zsmul_comp,
        Preadditive.comp_zsmul, Category.id_comp, Category.comp_id]
    · simp only [Cofork.π_ofπ, asIso_hom]
      rw [← Functor.map_comp_assoc, reassoc_of% key]
      simp
  have e : upperStarRootsOfUnityComparison h N =
      (h)^*[Ab.{u + 1}].map (rootsOfUnitySheafIso U N).inv ≫
        ((h)^*[Ab.{u + 1}].map (rootsOfUnitySheafIso U N).hom ≫
          upperStarRootsOfUnityComparison h N ≫ (rootsOfUnitySheafIso U' N).inv) ≫
        (rootsOfUnitySheafIso U' N).hom := by
    simp [← Functor.map_comp_assoc]
  rw [e]
  infer_instance

end Field

/-! ### The general case -/

/-- **The pullback of `μ_N` is `μ_N`** (before sheafification): for `g : X' ⟶ X` with `X` over a
field `k` in which `N` is invertible, the comparison map `g^* μ_N ⟶ μ_N` is an isomorphism. It is
checked after the pro-étale cover `X' ×_k Spec kˢᵉᵖ ⟶ X'`, through which `g` factors as
`X' ×_k kˢᵉᵖ ⟶ X ×_k kˢᵉᵖ ⟶ X`. -/
theorem isIso_upperStarRootsOfUnityComparison {k : Type u} [Field k] {X X' : Scheme.{u}}
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (N : ℕ) [NeZero (N : k)] :
    IsIso (upperStarRootsOfUnityComparison g N) := by
  have : NeZero N := NeZero.of_neZero_natCast k
  have : NeZero (N : SeparableClosure k) :=
    ‹NeZero (N : k)›.of_injective (algebraMap k (SeparableClosure k)).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure k) N
  let w := pullback.fst f (specSepClosureHom k)
  let w' := pullback.fst (g ≫ f) (specSepClosureHom k)
  let a : pullback (g ≫ f) (specSepClosureHom k) ⟶ pullback f (specSepClosureHom k) :=
    pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (by simp) (by simp)
  have ha : a ≫ w = w' ≫ g := pullback.lift_fst _ _ _
  have := isIso_upperStarRootsOfUnityComparison_of_field a (pullback.snd _ _) (pullback.snd _ _)
    ((pullback.lift_snd _ _ _).trans (Category.comp_id _)) hζ
  have := isIso_upperStarRootsOfUnityComparison_of_weaklyEtale w N
  have := isIso_upperStarRootsOfUnityComparison_of_weaklyEtale w' N
  have h₁ : IsIso (upperStarRootsOfUnityComparison (w' ≫ g) N) := by
    rw [← ha, ← upperStarRootsOfUnityComparison_comp]
    infer_instance
  rw [← upperStarRootsOfUnityComparison_comp, ← Category.assoc] at h₁
  have h₂ : IsIso ((w')^*[Ab.{u + 1}].map (upperStarRootsOfUnityComparison g N)) := by
    have := IsIso.of_isIso_comp_right (((upperStarComp Ab.{u + 1} w' g).hom.app _ ≫
      (w')^*[Ab.{u + 1}].map (upperStarRootsOfUnityComparison g N)))
      (upperStarRootsOfUnityComparison w' N)
    exact IsIso.of_isIso_comp_left ((upperStarComp Ab.{u + 1} w' g).hom.app _) _
  let 𝒰 := sepClosureCover (g ≫ f)
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  refine isIso_of_isIso_localizationRestriction Ab.{u + 1} _ 𝒰.f 𝒰.mem₀ fun i ↦ ?_
  exact (NatIso.isIso_map_iff
    (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) inferInstance) _).1 h₂

/-! ### The sheaves `μ_N` -/

/-- The comparison map `g^* μ_N ⟶ μ_N` of the sheaves of `N`-th roots of unity, for an arbitrary
morphism `g : X ⟶ Y`. -/
noncomputable def upperStarRootsOfUnitySheafHom (g : X ⟶ Y) (N : ℕ) :
    (g)^*[Ab.{u + 1}].obj (rootsOfUnitySheaf Y N) ⟶ rootsOfUnitySheaf X N :=
  (g)^*[Ab.{u + 1}].map (rootsOfUnitySheafIso Y N).hom ≫ upperStarRootsOfUnityComparison g N ≫
    (rootsOfUnitySheafIso X N).inv

/-- The comparison maps `g^* μ_N ⟶ μ_N` are compatible with the power maps `μ_{m N} ⟶ μ_N`. -/
@[reassoc]
lemma upperStar_map_rootsOfUnitySheafPow_comp_upperStarRootsOfUnitySheafHom (g : X ⟶ Y)
    (N m : ℕ) :
    (g)^*[Ab.{u + 1}].map (rootsOfUnitySheafPow Y N m) ≫ upperStarRootsOfUnitySheafHom g N =
      upperStarRootsOfUnitySheafHom g (m * N) ≫ rootsOfUnitySheafPow X N m := by
  rw [upperStarRootsOfUnitySheafHom, upperStarRootsOfUnitySheafHom, ← Functor.map_comp_assoc,
    rootsOfUnitySheafPow_comp_rootsOfUnitySheafIso_hom, Functor.map_comp_assoc,
    upperStar_map_pow_comp_upperStarRootsOfUnityComparison_assoc, Category.assoc,
    Category.assoc, rootsOfUnitySheafIso_inv_comp_rootsOfUnitySheafPow]

/-- **The pullback of `μ_N` is `μ_N`**: for `g : X' ⟶ X` with `X` over a field `k` in which `N`
is invertible, the comparison map `g^* μ_N ⟶ μ_N` is an isomorphism. -/
theorem isIso_upperStarRootsOfUnitySheafHom {k : Type u} [Field k] {X X' : Scheme.{u}}
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (N : ℕ) [NeZero (N : k)] :
    IsIso (upperStarRootsOfUnitySheafHom g N) := by
  have := isIso_upperStarRootsOfUnityComparison g f N
  rw [upperStarRootsOfUnitySheafHom]
  infer_instance

/-- **The pullback of `μ_N` is `μ_N`**: the isomorphism `g^* μ_N ≅ μ_N` for `g : X' ⟶ X` with
`X` over a field `k` in which `N` is invertible. -/
noncomputable def upperStarRootsOfUnitySheafIsoOfInvertible {k : Type u} [Field k]
    {X X' : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (N : ℕ) [NeZero (N : k)] :
    (g)^*[Ab.{u + 1}].obj (rootsOfUnitySheaf X N) ≅ rootsOfUnitySheaf X' N :=
  have := isIso_upperStarRootsOfUnitySheafHom g f N
  asIso (upperStarRootsOfUnitySheafHom g N)

lemma upperStarRootsOfUnitySheafIsoOfInvertible_hom {k : Type u} [Field k] {X X' : Scheme.{u}}
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (N : ℕ) [NeZero (N : k)] :
    (upperStarRootsOfUnitySheafIsoOfInvertible g f N).hom = upperStarRootsOfUnitySheafHom g N :=
  rfl

end AlgebraicGeometry.ProEtale
