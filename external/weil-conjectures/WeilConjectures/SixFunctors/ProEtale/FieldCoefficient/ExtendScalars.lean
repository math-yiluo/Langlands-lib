/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension

/-!
# Extension of scalars between finite extensions of `ℚ_ℓ`

Let `Λ`, `Λ'` be fields with an ultrametric norm which are `ℚ_ℓ`-algebras, `Λ'` being
finite-dimensional over `ℚ_ℓ`, and let `e : Λ → Λ'` be a continuous `ℚ_ℓ`-algebra map; the case
of interest is an inclusion `E ⊆ E'` of finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, the transition
functors of the `2`-colimit `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)` of blueprint
`definition-weil-structure`. This file constructs the extension of scalars

`Λ' ⊗_Λ - : Sh(X_proét, Λ_X) ⥤ Sh(X_proét, Λ'_X)`

between sheaves of modules over the constant sheaves `Λ_X : U ↦ C(U, Λ)` and
`Λ'_X : U ↦ C(U, Λ')` (`AlgebraicGeometry.ProEtale.fieldExtendScalars`), exactly as the
extension of scalars to `ℚ̄_ℓ` of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension`.

Composing with `e` is a morphism of sheaves of rings `Λ_X ⟶ Λ'_X`
(`AlgebraicGeometry.ProEtale.fieldConstantSheafToRestrictScalarsField`), whose adjoint
`Λ' ⊗_Λ Λ_X ⟶ Λ'_X` is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_extendScalarsFieldConstantSheafHomField`): it is injective on
sections, `Λ'` being free over the field `Λ`, and surjective on sections, a continuous function
`f : U → Λ'` being the finite sum `∑ₖ bₖ · cₖ ∘ f` for a `ℚ_ℓ`-basis `(bₖ)` of `Λ'` with
(continuous) coordinate functions `cₖ`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] (e : Λ →ₐ[ℚ_[l]] Λ')

/-- The map `e : Λ → Λ'`, as a ring morphism between the universe lifts. -/
noncomputable def fieldRingHom : ULift.{u + 1} Λ →+* ULift.{u + 1} Λ' :=
  (ULift.ringEquiv (R := Λ')).symm.toRingHom.comp
    ((e : Λ →+* Λ').comp (ULift.ringEquiv (R := Λ)).toRingHom)

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] [FiniteDimensional ℚ_[l] Λ'] in
/-- The ring maps between the universe lifts compose. -/
lemma fieldToAdicRingHom_comp_fieldRingHom (e' : Λ' →ₐ[ℚ_[l]] PadicAlgCl l) :
    (fieldToAdicRingHom.{u} e').comp (fieldRingHom.{u} e) = fieldToAdicRingHom.{u} (e'.comp e) :=
  rfl

variable {e} (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
include he

variable (X : Scheme.{u})

/-- Composition with `e`, from continuous `Λ`-valued functions to continuous `Λ'`-valued
functions, as a `Λ`-linear map. -/
noncomputable def fieldFunctionsToFieldFunctions (T : Type u) [TopologicalSpace T] :
    ULift.{u + 1} (fieldFunctions Λ T) →ₗ[ULift.{u + 1} Λ]
      (ModuleCat.restrictScalars.{u + 1} (fieldRingHom.{u} e)).obj
        (ModuleCat.of (ULift.{u + 1} Λ') (ULift.{u + 1} (fieldFunctions Λ' T))) where
  toFun s := ULift.up ⟨(ContinuousMap.mk e he).comp s.down.1, Algebra.mem_top⟩
  map_add' s t :=
    ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ map_add e (s.down.1 x) (t.down.1 x)))
  map_smul' c s :=
    ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ map_mul e c.down (s.down.1 x)))

/-- The morphism of sheaves of rings `Λ_X ⟶ Λ'_X`, composing functions with `e`, as a morphism
of sheaves of `Λ`-modules into the restriction of scalars of `Λ'_X`. -/
noncomputable def fieldConstantSheafToRestrictScalarsField :
    fieldConstantSheaf Λ X ⟶ (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} (fieldRingHom.{u} e))).obj (fieldConstantSheaf Λ' X) :=
  ⟨{ app U := ModuleCat.ofHom
      (X := ModuleCat.of (ULift.{u + 1} Λ) (ULift.{u + 1} (fieldFunctions Λ U.unop.left)))
      (Y := (ModuleCat.restrictScalars.{u + 1} (fieldRingHom.{u} e)).obj
          (ModuleCat.of (ULift.{u + 1} Λ') (ULift.{u + 1} (fieldFunctions Λ' U.unop.left))))
      (fieldFunctionsToFieldFunctions he U.unop.left)
     naturality _ _ _ := rfl }⟩

-- the pointwise computation goes through `erw` in tensor products of `ModuleCat` objects
/-- Composing functions with `e` is a morphism of sheaves of rings: on sections, both
multiplications are pointwise. -/
instance isMonHom_fieldConstantSheafToRestrictScalarsField :
    IsMonHom (fieldConstantSheafToRestrictScalarsField he X) := by
  have : IsMonHom ((sheafToPresheaf _ _).map (fieldConstantSheafToRestrictScalarsField he X)) :=
    { one_hom := by
        have h := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (fieldRingHom.{u} e))
        change (ε _ ≫ (sheafToPresheaf _ _).map η[fieldConstantSheaf Λ X]) ≫ _ =
          ε _ ≫ (sheafToPresheaf _ _).map (ε (sheafCompose _ _) ≫
            (sheafCompose _ _).map η[fieldConstantSheaf Λ' X])
        rw [fieldConstantSheaf_ε_comp_map_one', Functor.map_comp, ← Category.assoc, h,
          Category.assoc]
        rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
            (fieldRingHom.{u} e))).map η[fieldConstantSheaf Λ' X]) =
            ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1}
              (fieldRingHom.{u} e))).map ((sheafToPresheaf _ _).map η[fieldConstantSheaf Λ' X])
            from rfl, ← Functor.map_comp, fieldConstantSheaf_ε_comp_map_one']
        ext U
        apply ULift.ext; apply Subtype.ext; ext x
        simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [ModuleCat.restrictScalars_η, fieldConstantSheaf_one_app]
        rfl
      mul_hom := by
        have h := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (fieldRingHom.{u} e))
          (fieldConstantSheaf Λ' X) (fieldConstantSheaf Λ' X)
        change («μ» _ _ _ ≫ (sheafToPresheaf _ _).map μ[fieldConstantSheaf Λ X]) ≫ _ =
          _ ≫ «μ» _ _ _ ≫ (sheafToPresheaf _ _).map
            («μ» (sheafCompose _ _) _ _ ≫ (sheafCompose _ _).map μ[fieldConstantSheaf Λ' X])
        rw [fieldConstantSheaf_μ_comp_map_mul', Functor.map_comp, reassoc_of% h]
        rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
            (fieldRingHom.{u} e))).map μ[fieldConstantSheaf Λ' X]) =
            ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1}
              (fieldRingHom.{u} e))).map ((sheafToPresheaf _ _).map μ[fieldConstantSheaf Λ' X])
            from rfl, ← Functor.map_comp, fieldConstantSheaf_μ_comp_map_mul']
        refine NatTrans.ext (funext fun U ↦ ?_)
        refine ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ ?_
        apply ULift.ext; apply Subtype.ext; ext x
        simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [ModuleCat.restrictScalars_μ_tmul, fieldConstantSheaf_mul_app_tmul,
          fieldConstantSheaf_mul_app_tmul]
        exact map_mul e _ _ }
  exact Sheaf.isMonHom_of_isMonHom_map _

/-- The adjoint of `fieldConstantSheafToRestrictScalarsField`, the comparison
`Λ' ⊗_Λ Λ_X ⟶ Λ'_X`. -/
noncomputable def extendScalarsFieldConstantSheafHomField :
    (sheafExtendScalars (fieldRingHom.{u} e) X).obj (fieldConstantSheaf Λ X) ⟶
      fieldConstantSheaf Λ' X :=
  ((sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).homEquiv _ _).symm
    (fieldConstantSheafToRestrictScalarsField he X)

/-- The presheaf-level comparison `Λ' ⊗_Λ Λ_X(U) ⟶ Λ'_X(U)`, `q ⊗ f ↦ q · e ∘ f`. -/
noncomputable def extendScalarsFieldConstantPresheafHomField :
    (fieldConstantSheaf Λ X).obj ⋙
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (fieldRingHom.{u} e)
      ⟶ (fieldConstantSheaf Λ' X).obj :=
  Functor.whiskerRight (fieldConstantSheafToRestrictScalarsField he X).hom
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (fieldRingHom.{u} e)) ≫
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (fieldRingHom.{u} e)).whiskerRight X.ProEtᵒᵖ).counit.app (fieldConstantSheaf Λ' X).obj

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] [FiniteDimensional ℚ_[l] Λ'] in
/-- The comparison `Λ' ⊗_Λ Λ_X ⟶ Λ'_X` is the sheafification of the presheaf-level one. -/
lemma toSheafify_comp_extendScalarsFieldConstantSheafHomField :
    toSheafify _ _ ≫ (extendScalarsFieldConstantSheafHomField he X).hom =
      extendScalarsFieldConstantPresheafHomField he X := by
  rw [extendScalarsFieldConstantSheafHomField, Adjunction.homEquiv_counit]
  change toSheafify _ _ ≫ sheafifyMap _ _ ≫ _ = _
  rw [sheafExtendScalarsAdjunction, Sheaf.adjunction_counit_app_hom, ← toSheafify_naturality_assoc,
    toSheafify_sheafifyLift]
  rfl

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] [FiniteDimensional ℚ_[l] Λ'] in
/-- On sections over `U`, the presheaf-level comparison is the adjoint of composition with
`e`. -/
lemma extendScalarsFieldConstantPresheafHomField_app (U : X.ProEtᵒᵖ) :
    (extendScalarsFieldConstantPresheafHomField he X).app U =
      ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (fieldRingHom.{u} e)).homEquiv _ _).symm
        ((fieldConstantSheafToRestrictScalarsField he X).hom.app U) := by
  change (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} _).map _ ≫
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} _).counit.app _ = _
  exact ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (fieldRingHom.{u} e)).homEquiv_counit
    (g := (fieldConstantSheafToRestrictScalarsField he X).hom.app U)).symm

/-- The comparison `Λ' ⊗_Λ C(U, Λ) ⟶ C(U, Λ')` is injective, `Λ'` being free over the field
`Λ` (`ModuleCat.injective_homEquiv_symm_of_eval`). -/
instance : Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
    (extendScalarsFieldConstantPresheafHomField he X) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun U ↦ by
    rw [extendScalarsFieldConstantPresheafHomField_app]
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

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] in
include hc in
/-- The comparison `Λ' ⊗_Λ C(U, Λ) ⟶ C(U, Λ')` is surjective: a continuous function `f` with
values in `Λ'` is `∑ₖ bₖ · cₖ ∘ f` for a `ℚ_ℓ`-basis `(bₖ)` of `Λ'` with coordinates `cₖ`, which
are continuous `ℚ_ℓ`-valued, hence `Λ`-valued, functions. -/
lemma surjective_extendScalarsFieldConstantPresheafHomField_app (U : X.ProEtᵒᵖ) :
    Function.Surjective ((extendScalarsFieldConstantPresheafHomField he X).app U) := by
  intro s
  have hc' : Continuous (algebraMap ℚ_[l] Λ') := by
    rw [← e.comp_algebraMap]
    exact he.comp hc
  have : ContinuousSMul ℚ_[l] Λ' :=
    ⟨by simp_rw [Algebra.smul_def]; exact (hc'.comp continuous_fst).mul continuous_snd⟩
  let b := Module.finBasis ℚ_[l] Λ'
  let c (k : Fin (Module.finrank ℚ_[l] Λ')) : C(U.unop.left, ℚ_[l]) :=
    ⟨fun y ↦ b.coord k (s.down.1 y),
      (LinearMap.continuous_of_finiteDimensional _).comp s.down.1.continuous⟩
  let a (k : Fin (Module.finrank ℚ_[l] Λ')) : C(U.unop.left, Λ) :=
    ⟨fun y ↦ algebraMap ℚ_[l] Λ (c k y), hc.comp (c k).continuous⟩
  refine ⟨∑ k, (ULift.up (b k) : ULift.{u + 1} Λ') ⊗ₜ[ULift.{u + 1} Λ]
    (ULift.up ⟨a k, Algebra.mem_top⟩ : ULift.{u + 1} (fieldFunctions Λ U.unop.left)), ?_⟩
  apply ULift.ext; apply Subtype.ext; ext y
  rw [extendScalarsFieldConstantPresheafHomField_app]
  let ev : ULift.{u + 1} (fieldFunctions Λ' U.unop.left) →+ Λ' :=
    { toFun f := f.down.1 y, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  change ev _ = s.down.1 y
  rw [map_sum, map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun k _ ↦ ?_) (b.sum_repr (s.down.1 y))
  change b k * e (algebraMap ℚ_[l] Λ (c k y)) = _
  rw [AlgHom.commutes, mul_comm, ← Algebra.smul_def]
  rfl

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] in
include hc in
/-- **The extension of scalars of `Λ_X` to `Λ'` is `Λ'_X`**: the comparison
`Λ' ⊗_Λ Λ_X ⟶ Λ'_X` is an isomorphism, being locally injective and locally surjective. -/
lemma isIso_extendScalarsFieldConstantSheafHomField :
    IsIso (extendScalarsFieldConstantSheafHomField he X) := by
  have := Presheaf.isLocallySurjective_of_surjective (Scheme.ProEt.topology X) _
    (surjective_extendScalarsFieldConstantPresheafHomField_app he hc X)
  have := Presheaf.isLocallySurjective_toSheafify' (Scheme.ProEt.topology X)
    (((Functor.whiskeringRight _ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (fieldRingHom.{u} e))).obj
        ((sheafToPresheaf _ _).obj (fieldConstantSheaf Λ X)))
  have : Sheaf.IsLocallyInjective (extendScalarsFieldConstantSheafHomField he X) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _
      (extendScalarsFieldConstantPresheafHomField he X)
      (toSheafify_comp_extendScalarsFieldConstantSheafHomField he X)
  have : Sheaf.IsLocallySurjective (extendScalarsFieldConstantSheafHomField he X) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (toSheafify_comp_extendScalarsFieldConstantSheafHomField he X)
  exact (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨inferInstance, inferInstance⟩

omit he in
/-- The counit of `Λ' ⊗_Λ - ⊣ res` at `Λ'_X` is a morphism of sheaves of rings. -/
instance isMonHom_sheafExtendScalarsCounit_app_field :
    IsMonHom (show (sheafExtendScalars (fieldRingHom.{u} e) X).obj ((sheafCompose _
        (ModuleCat.restrictScalars.{u + 1} (fieldRingHom.{u} e))).obj
          (fieldConstantSheaf Λ' X)) ⟶
        fieldConstantSheaf Λ' X from
      (sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).counit.app
        (fieldConstantSheaf Λ' X)) := by
  have h := NatTrans.isMonHom_app (sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).counit
    (fieldConstantSheaf Λ' X)
  constructor
  · simpa only [Functor.obj.η_def, Functor.LaxMonoidal.comp_ε, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_ε, Functor.id_map,
      Category.id_comp] using h.one_hom
  · simpa only [Functor.obj.μ_def, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
      Functor.map_comp, Category.assoc, Functor.LaxMonoidal.id_μ, Functor.id_map,
      Category.id_comp] using h.mul_hom

/-- The comparison `Λ' ⊗_Λ Λ_X ⟶ Λ'_X` is a morphism of sheaves of rings, being the adjoint of
one for the monoidal adjunction `Λ' ⊗_Λ - ⊣ res`. -/
instance isMonHom_extendScalarsFieldConstantSheafHomField :
    IsMonHom (extendScalarsFieldConstantSheafHomField he X) := by
  rw [extendScalarsFieldConstantSheafHomField, Adjunction.homEquiv_counit]
  have : IsMonHom ((sheafExtendScalars (fieldRingHom.{u} e) X).map
      (fieldConstantSheafToRestrictScalarsField he X)) :=
    Functor.map.instIsMonHom (F := sheafExtendScalars (fieldRingHom.{u} e) X) _ _
      (fieldConstantSheafToRestrictScalarsField he X)
  exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ this
    (isMonHom_sheafExtendScalarsCounit_app_field (e := e) X)

/-- The extension of scalars `Λ' ⊗_Λ -` from sheaves of `Λ_X`-modules to sheaves of
`Λ'_X`-modules: the extension of scalars of the underlying sheaves along `e : Λ → Λ'`, a module
over `Λ' ⊗_Λ Λ_X ≅ Λ'_X`. -/
noncomputable def fieldExtendScalars : FieldSheaf Λ X ⥤ FieldSheaf Λ' X :=
  haveI : IsIso (((sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalarsField he X)) :=
    isIso_extendScalarsFieldConstantSheafHomField he hc X
  haveI : IsMonHom (((sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalarsField he X)) :=
    isMonHom_extendScalarsFieldConstantSheafHomField he X
  (sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).modLeft
    (fieldConstantSheafToRestrictScalarsField he X)

/-- Restriction of scalars from sheaves of `Λ'_X`-modules to sheaves of `Λ_X`-modules. -/
noncomputable def fieldRestrictScalars : FieldSheaf Λ' X ⥤ FieldSheaf Λ X :=
  (sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).modRight
    (fieldConstantSheafToRestrictScalarsField he X)

/-- The extension of scalars `Λ' ⊗_Λ -` is left adjoint to the restriction of scalars. -/
noncomputable def fieldExtendScalarsAdjunction :
    fieldExtendScalars he hc X ⊣ fieldRestrictScalars he X :=
  haveI : IsIso (((sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalarsField he X)) :=
    isIso_extendScalarsFieldConstantSheafHomField he hc X
  haveI : IsMonHom (((sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalarsField he X)) :=
    isMonHom_extendScalarsFieldConstantSheafHomField he X
  (sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).modAdjunction _

/-- The extension of scalars of the constant sheaf `Λ_X` is the constant sheaf `Λ'_X`. -/
noncomputable def fieldExtendScalarsUnitIso :
    (fieldExtendScalars he hc X).obj (FieldSheaf.unit Λ X) ≅ FieldSheaf.unit Λ' X :=
  haveI : IsIso (extendScalarsFieldConstantSheafHomField he X) :=
    isIso_extendScalarsFieldConstantSheafHomField he hc X
  Mod.regularIsoOfIsIso (extendScalarsFieldConstantSheafHomField he X)

end AlgebraicGeometry.ProEtale
