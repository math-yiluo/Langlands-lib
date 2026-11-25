/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.ExtendScalarsInjective
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-!
# Extension of scalars from a finite extension `E` of `ℚ_ℓ` to `ℚ̄_ℓ`

Let `Λ` be a field with an ultrametric norm which is a finite-dimensional `ℚ_ℓ`-algebra, with a
continuous `ℚ_ℓ`-algebra embedding `e : Λ → ℚ̄_ℓ`; the case of interest is a finite extension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (blueprint `definition-weil-structure`, `def-weil-algebraically-closed-
coefficients`). This file constructs the extension of scalars

`ℚ̄_ℓ ⊗_Λ - : Sh(X_proét, Λ_X) ⥤ Sh(X_proét, ℚ̄_ℓ,X)`

from sheaves of modules over the constant sheaf `Λ_X : U ↦ C(U, Λ)`
(`AlgebraicGeometry.ProEtale.FieldSheaf`) to `ℓ`-adic sheaves, modules over the constant sheaf
`ℚ̄_ℓ,X` of locally finite functions (`AlgebraicGeometry.ProEtale.AdicSheaf`)
(`AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdic`).

Composing with `e` sends continuous `Λ`-valued functions to locally finite `ℚ̄_ℓ`-valued ones,
a morphism of sheaves of rings `Λ_X ⟶ ℚ̄_ℓ,X` (seen in sheaves of `Λ`-modules,
`AlgebraicGeometry.ProEtale.fieldConstantSheafToRestrictScalars`). Its adjoint
`ℚ̄_ℓ ⊗_Λ Λ_X ⟶ ℚ̄_ℓ,X`, from the extension of scalars of sheaves along `Λ → ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.sheafExtendScalars`), is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_extendScalarsFieldConstantSheafHom`): it is injective on
sections, `ℚ̄_ℓ` being free over the field `Λ`, and locally surjective, a locally finite function
taking near every point values in a finite-dimensional `ℚ_ℓ`-subspace of `ℚ̄_ℓ`, so that it is
locally a finite sum `∑ₖ vₖ · cₖ` of constants `vₖ ∈ ℚ̄_ℓ` times continuous `ℚ_ℓ`-valued
coordinate functions `cₖ`. The extension of scalars of modules is then the functor induced by the
monoidal adjunction `ℚ̄_ℓ ⊗_Λ - ⊣ res` on module objects (`CategoryTheory.Adjunction.modLeft`).

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldConstantSheafToRestrictScalars`: `Λ_X ⟶ res ℚ̄_ℓ,X`.
- `AlgebraicGeometry.ProEtale.extendScalarsFieldConstantSheafHom`: `ℚ̄_ℓ ⊗_Λ Λ_X ≅ ℚ̄_ℓ,X`.
- `AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdic`: `ℚ̄_ℓ ⊗_Λ -`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] (e : Λ →ₐ[ℚ_[l]] PadicAlgCl l)

/-- The embedding `e : Λ → ℚ̄_ℓ`, as a ring morphism between the universe lifts. -/
noncomputable def fieldToAdicRingHom : ULift.{u + 1} Λ →+* ULift.{u + 1} (PadicAlgCl l) :=
  (ULift.ringEquiv (R := PadicAlgCl l)).symm.toRingHom.comp
    ((e : Λ →+* PadicAlgCl l).comp (ULift.ringEquiv (R := Λ)).toRingHom)

variable {e} (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
include he

omit [IsUltrametricDist Λ] in
/-- Composing a continuous `Λ`-valued function with `e` gives a locally finite function: its
values lie in the finite-dimensional `ℚ_ℓ`-subspace `e(Λ)`. -/
lemma comp_mem_locallyFiniteFunctions_of_algHom {T : Type u} [TopologicalSpace T] (f : C(T, Λ)) :
    (ContinuousMap.mk e he).comp f ∈ PadicAlgCl.locallyFiniteFunctions l T :=
  PadicAlgCl.mem_locallyFiniteFunctions_of_finiteDimensional
    (Submodule.finiteDimensional_of_le (S₂ := LinearMap.range e.toLinearMap)
      (Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact ⟨f x, rfl⟩)))

variable (X : Scheme.{u})

/-- Composition with `e`, from continuous `Λ`-valued functions to locally finite
`ℚ̄_ℓ`-valued functions, as a `Λ`-linear map. -/
noncomputable def fieldFunctionsToLocallyFinite (T : Type u) [TopologicalSpace T] :
    ULift.{u + 1} (fieldFunctions Λ T) →ₗ[ULift.{u + 1} Λ]
      (ModuleCat.restrictScalars.{u + 1} (fieldToAdicRingHom.{u} e)).obj
        (ModuleCat.of (ULift.{u + 1} (PadicAlgCl l))
          (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l T))) where
  toFun s := ULift.up ⟨(ContinuousMap.mk e he).comp s.down.1,
    comp_mem_locallyFiniteFunctions_of_algHom he _⟩
  map_add' s t :=
    ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ map_add e (s.down.1 x) (t.down.1 x)))
  map_smul' c s :=
    ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ map_mul e c.down (s.down.1 x)))

/-- The morphism of sheaves of rings `Λ_X ⟶ ℚ̄_ℓ,X`, composing functions with `e`, as a morphism
of sheaves of `Λ`-modules into the restriction of scalars of `ℚ̄_ℓ,X`. -/
noncomputable def fieldConstantSheafToRestrictScalars :
    fieldConstantSheaf Λ X ⟶ (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} (fieldToAdicRingHom.{u} e))).obj (adicConstantSheaf l X) :=
  ⟨{ app U := ModuleCat.ofHom
      (X := ModuleCat.of (ULift.{u + 1} Λ) (ULift.{u + 1} (fieldFunctions Λ U.unop.left)))
      (Y := (ModuleCat.restrictScalars.{u + 1} (fieldToAdicRingHom.{u} e)).obj
          (ModuleCat.of (ULift.{u + 1} (PadicAlgCl l))
            (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l U.unop.left))))
      (fieldFunctionsToLocallyFinite he U.unop.left)
     naturality _ _ _ := rfl }⟩

-- the pointwise computation goes through `erw` in tensor products of `ModuleCat` objects
/-- Composing functions with `e` is a morphism of sheaves of rings: on sections, both
multiplications are pointwise. -/
instance isMonHom_fieldConstantSheafToRestrictScalars :
    IsMonHom (fieldConstantSheafToRestrictScalars he X) := by
  have : IsMonHom ((sheafToPresheaf _ _).map (fieldConstantSheafToRestrictScalars he X)) :=
    { one_hom := by
        have h := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (fieldToAdicRingHom.{u} e))
        change (ε _ ≫ (sheafToPresheaf _ _).map η[fieldConstantSheaf Λ X]) ≫ _ =
          ε _ ≫ (sheafToPresheaf _ _).map (ε (sheafCompose _ _) ≫
            (sheafCompose _ _).map η[adicConstantSheaf l X])
        rw [fieldConstantSheaf_ε_comp_map_one', Functor.map_comp, ← Category.assoc, h,
          Category.assoc]
        rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
            (fieldToAdicRingHom.{u} e))).map η[adicConstantSheaf l X]) =
            ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1}
              (fieldToAdicRingHom.{u} e))).map ((sheafToPresheaf _ _).map η[adicConstantSheaf l X])
            from rfl, ← Functor.map_comp, adicConstantSheaf_ε_comp_map_one']
        ext U
        apply ULift.ext; apply Subtype.ext; ext x
        simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [ModuleCat.restrictScalars_η, fieldConstantSheaf_one_app, adicConstantSheaf_one_app]
        exact (map_one e).trans (map_one e).symm
      mul_hom := by
        have h := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (fieldToAdicRingHom.{u} e))
          (adicConstantSheaf l X) (adicConstantSheaf l X)
        change («μ» _ _ _ ≫ (sheafToPresheaf _ _).map μ[fieldConstantSheaf Λ X]) ≫ _ =
          _ ≫ «μ» _ _ _ ≫ (sheafToPresheaf _ _).map
            («μ» (sheafCompose _ _) _ _ ≫ (sheafCompose _ _).map μ[adicConstantSheaf l X])
        rw [fieldConstantSheaf_μ_comp_map_mul', Functor.map_comp, reassoc_of% h]
        rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
            (fieldToAdicRingHom.{u} e))).map μ[adicConstantSheaf l X]) =
            ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1}
              (fieldToAdicRingHom.{u} e))).map ((sheafToPresheaf _ _).map μ[adicConstantSheaf l X])
            from rfl, ← Functor.map_comp, adicConstantSheaf_μ_comp_map_mul']
        refine NatTrans.ext (funext fun U ↦ ?_)
        refine ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ ?_
        apply ULift.ext; apply Subtype.ext; ext x
        simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [ModuleCat.restrictScalars_μ_tmul, fieldConstantSheaf_mul_app_tmul,
          adicConstantSheaf_mul_app_tmul]
        exact map_mul e _ _ }
  exact Sheaf.isMonHom_of_isMonHom_map _


/-- The adjoint of `fieldConstantSheafToRestrictScalars`, the comparison `ℚ̄_ℓ ⊗_Λ Λ_X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def extendScalarsFieldConstantSheafHom :
    (sheafExtendScalars (fieldToAdicRingHom.{u} e) X).obj (fieldConstantSheaf Λ X) ⟶
      adicConstantSheaf l X :=
  ((sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).homEquiv _ _).symm
    (fieldConstantSheafToRestrictScalars he X)

/-- The presheaf-level comparison `ℚ̄_ℓ ⊗_Λ Λ_X(U) ⟶ ℚ̄_ℓ,X(U)`, `q ⊗ f ↦ q · e ∘ f`. -/
noncomputable def extendScalarsFieldConstantPresheafHom :
    (fieldConstantSheaf Λ X).obj ⋙
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (fieldToAdicRingHom.{u} e)
      ⟶ (adicConstantSheaf l X).obj :=
  Functor.whiskerRight (fieldConstantSheafToRestrictScalars he X).hom
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (fieldToAdicRingHom.{u} e)) ≫
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (fieldToAdicRingHom.{u} e)).whiskerRight X.ProEtᵒᵖ).counit.app (adicConstantSheaf l X).obj

omit [IsUltrametricDist Λ] in
/-- The comparison `ℚ̄_ℓ ⊗_Λ Λ_X ⟶ ℚ̄_ℓ,X` is the sheafification of the presheaf-level one. -/
lemma toSheafify_comp_extendScalarsFieldConstantSheafHom :
    toSheafify _ _ ≫ (extendScalarsFieldConstantSheafHom he X).hom =
      extendScalarsFieldConstantPresheafHom he X := by
  rw [extendScalarsFieldConstantSheafHom, Adjunction.homEquiv_counit]
  change toSheafify _ _ ≫ sheafifyMap _ _ ≫ _ = _
  rw [sheafExtendScalarsAdjunction, Sheaf.adjunction_counit_app_hom, ← toSheafify_naturality_assoc,
    toSheafify_sheafifyLift]
  rfl


omit [IsUltrametricDist Λ] in
/-- On sections over `U`, the presheaf-level comparison is the adjoint of composition with
`e`. -/
lemma extendScalarsFieldConstantPresheafHom_app (U : X.ProEtᵒᵖ) :
    (extendScalarsFieldConstantPresheafHom he X).app U =
      ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (fieldToAdicRingHom.{u} e)).homEquiv _ _).symm
        ((fieldConstantSheafToRestrictScalars he X).hom.app U) := by
  change (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} _).map _ ≫
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} _).counit.app _ = _
  exact ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (fieldToAdicRingHom.{u} e)).homEquiv_counit
    (g := (fieldConstantSheafToRestrictScalars he X).hom.app U)).symm

/-- The comparison `ℚ̄_ℓ ⊗_Λ C(U, Λ) ⟶ ℚ̄_ℓ,X(U)` is injective, `ℚ̄_ℓ` being free over the field
`Λ` (`ModuleCat.injective_homEquiv_symm_of_eval`). -/
instance : Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
    (extendScalarsFieldConstantPresheafHom he X) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun U ↦ by
    rw [extendScalarsFieldConstantPresheafHom_app]
    refine ModuleCat.injective_homEquiv_symm_of_eval _ _ (T := U.unop.left)
      (fun t ↦
        { toFun x := ULift.up (x.down.1 t)
          map_add' _ _ := rfl
          map_smul' _ _ := rfl })
      (fun t ↦
        { toFun y := ULift.up (y.down.1 t)
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }) (fun x hx ↦ ?_) (fun _ _ ↦ rfl)
    exact ULift.ext (Subtype.ext (ContinuousMap.ext fun t ↦ congrArg ULift.down (hx t)))


omit [IsUltrametricDist Λ] in
include hc in
/-- The comparison `ℚ̄_ℓ ⊗_Λ Λ_X(U) ⟶ ℚ̄_ℓ,X(U)` is locally surjective: a locally finite function
`s` on `U` takes, near every point, values in a finite-dimensional `ℚ_ℓ`-subspace `V` of `ℚ̄_ℓ`,
and there `s = ∑ₖ vₖ · cₖ ∘ s` for a basis `(vₖ)` of `V` with coordinates `cₖ`, which are
continuous `ℚ_ℓ`-valued, hence `Λ`-valued, functions. -/
lemma isLocallySurjective_extendScalarsFieldConstantPresheafHom :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      (extendScalarsFieldConstantPresheafHom he X) where
  imageSieve_mem {U} s := by
    choose N hN hfin using s.down.2
    refine Scheme.ProEt.mem_topology_of_openImmersion _
      (fun x ↦ Scheme.Opens.ι (X := U.left) ⟨interior (N x), isOpen_interior⟩)
      (fun x ↦ ⟨x, by simpa using mem_interior_iff_mem_nhds.2 (hN x)⟩) fun x ↦ ?_
    let O : U.left.Opens := ⟨interior (N x), isOpen_interior⟩
    let V := Submodule.span ℚ_[l] (⇑s.down.1 '' N x)
    have := hfin x
    let b := Module.finBasis ℚ_[l] V
    have hsV (y : (O : Scheme)) : s.down.1 (O.ι y) ∈ V :=
      Submodule.subset_span ⟨O.ι y, interior_subset (by simp), rfl⟩
    let σ : C((O : Scheme), V) := ⟨fun y ↦ ⟨s.down.1 (O.ι y), hsV y⟩,
      (s.down.1.continuous.comp (O.ι).base.hom.continuous).subtype_mk _⟩
    let c (k : Fin (Module.finrank ℚ_[l] V)) : C((O : Scheme), ℚ_[l]) :=
      ⟨fun y ↦ b.coord k (σ y), (LinearMap.continuous_of_finiteDimensional _).comp σ.continuous⟩
    let a (k : Fin (Module.finrank ℚ_[l] V)) : C((O : Scheme), Λ) :=
      ⟨fun y ↦ algebraMap ℚ_[l] Λ (c k y), hc.comp (c k).continuous⟩
    refine ⟨∑ k, (ULift.up (b k : PadicAlgCl l) : ULift.{u + 1} (PadicAlgCl l)) ⊗ₜ[ULift.{u + 1} Λ]
      (ULift.up ⟨a k, Algebra.mem_top⟩ : ULift.{u + 1} (fieldFunctions Λ (O : Scheme))), ?_⟩
    apply ULift.ext; apply Subtype.ext; ext y
    rw [extendScalarsFieldConstantPresheafHom_app]
    let ev : ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l (O : Scheme)) →+ PadicAlgCl l :=
      { toFun f := f.down.1 y, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    change ev _ = s.down.1 (O.ι y)
    rw [map_sum, map_sum]
    have h2 := congrArg Subtype.val (b.sum_repr (σ y))
    rw [Submodule.coe_sum] at h2
    refine Eq.trans (Finset.sum_congr rfl fun k _ ↦ ?_) h2
    change (b k : PadicAlgCl l) * e (algebraMap ℚ_[l] Λ (c k y)) = _
    rw [AlgHom.commutes, mul_comm, ← Algebra.smul_def]
    rfl


omit [IsUltrametricDist Λ] in
include hc in
/-- **The extension of scalars of `Λ_X` to `ℚ̄_ℓ` is `ℚ̄_ℓ,X`**: the comparison
`ℚ̄_ℓ ⊗_Λ Λ_X ⟶ ℚ̄_ℓ,X` is an isomorphism, being locally injective and locally surjective. -/
lemma isIso_extendScalarsFieldConstantSheafHom :
    IsIso (extendScalarsFieldConstantSheafHom he X) := by
  have := isLocallySurjective_extendScalarsFieldConstantPresheafHom he hc X
  have := Presheaf.isLocallySurjective_toSheafify' (Scheme.ProEt.topology X)
    (((Functor.whiskeringRight _ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (fieldToAdicRingHom.{u} e))).obj
        ((sheafToPresheaf _ _).obj (fieldConstantSheaf Λ X)))
  have : Sheaf.IsLocallyInjective (extendScalarsFieldConstantSheafHom he X) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _
      (extendScalarsFieldConstantPresheafHom he X)
      (toSheafify_comp_extendScalarsFieldConstantSheafHom he X)
  have : Sheaf.IsLocallySurjective (extendScalarsFieldConstantSheafHom he X) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (toSheafify_comp_extendScalarsFieldConstantSheafHom he X)
  exact (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨inferInstance, inferInstance⟩


/-- The counit of `ℚ̄_ℓ ⊗_Λ - ⊣ res` at `ℚ̄_ℓ,X` is a morphism of sheaves of rings. -/
instance isMonHom_sheafExtendScalarsCounit_app :
    IsMonHom (show (sheafExtendScalars (fieldToAdicRingHom.{u} e) X).obj ((sheafCompose _
        (ModuleCat.restrictScalars.{u + 1} (fieldToAdicRingHom.{u} e))).obj
          (adicConstantSheaf l X)) ⟶
        adicConstantSheaf l X from
      (sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).counit.app
        (adicConstantSheaf l X)) := by
  have h := NatTrans.isMonHom_app (sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).counit
    (adicConstantSheaf l X)
  constructor
  · simpa only [Functor.obj.η_def, Functor.LaxMonoidal.comp_ε, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_ε, Functor.id_map,
      Category.id_comp] using h.one_hom
  · simpa only [Functor.obj.μ_def, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_μ, Functor.id_map,
      Category.id_comp] using h.mul_hom

/-- The comparison `ℚ̄_ℓ ⊗_Λ Λ_X ⟶ ℚ̄_ℓ,X` is a morphism of sheaves of rings, being the adjoint of
one for the monoidal adjunction `ℚ̄_ℓ ⊗_Λ - ⊣ res`. -/
instance isMonHom_extendScalarsFieldConstantSheafHom :
    IsMonHom (extendScalarsFieldConstantSheafHom he X) := by
  rw [extendScalarsFieldConstantSheafHom, Adjunction.homEquiv_counit]
  have : IsMonHom ((sheafExtendScalars (fieldToAdicRingHom.{u} e) X).map
      (fieldConstantSheafToRestrictScalars he X)) :=
    Functor.map.instIsMonHom (F := sheafExtendScalars (fieldToAdicRingHom.{u} e) X) _ _
      (fieldConstantSheafToRestrictScalars he X)
  exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ this
    (isMonHom_sheafExtendScalarsCounit_app (e := e) X)

/-- The extension of scalars `ℚ̄_ℓ ⊗_Λ -` from sheaves of `Λ_X`-modules to `ℓ`-adic sheaves:
the extension of scalars of the underlying sheaves along `Λ → ℚ̄_ℓ`, a module over
`ℚ̄_ℓ ⊗_Λ Λ_X ≅ ℚ̄_ℓ,X`. -/
noncomputable def fieldExtendScalarsToAdic : FieldSheaf Λ X ⥤ AdicSheaf l X :=
  haveI : IsIso (((sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalars he X)) :=
    isIso_extendScalarsFieldConstantSheafHom he hc X
  haveI : IsMonHom (((sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalars he X)) :=
    isMonHom_extendScalarsFieldConstantSheafHom he X
  (sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).modLeft
    (fieldConstantSheafToRestrictScalars he X)

end AlgebraicGeometry.ProEtale
