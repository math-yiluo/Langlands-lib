/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalars

/-!
# Extension of scalars between finite extensions of `ℚ_ℓ` is exact and preserves
constructibility

Let `e : Λ → Λ'` be a continuous map of finite extensions of `ℚ_ℓ` and
`Λ' ⊗_Λ - : Sh(X_proét, Λ_X) ⥤ Sh(X_proét, Λ'_X)` the extension of scalars of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalars`. As for the
extension of scalars to `ℚ̄_ℓ`
(`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible`):

- it is exact, its underlying functor being the extension of scalars of sheaves along the flat
  `Λ → Λ'`;
- it commutes with pullbacks
  (`AlgebraicGeometry.ProEtale.fieldUpperStarCompExtendScalarsIso`), being the left adjoint of
  the restriction of scalars, which commutes with pushforwards
  (`AlgebraicGeometry.ProEtale.fieldLowerStarCompRestrictScalarsIso`);
- hence it preserves lisse, stratified lisse and constructible sheaves
  (`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.extendScalars`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] [FiniteDimensional ℚ_[l] Λ'] in
/-- The two ring maps `Λ_X ⟶ Λ'_X ⟶ g_* Λ'_Y` and `Λ_X ⟶ g_* Λ_Y ⟶ g_* Λ'_Y` agree: both
compose functions with `e` and with the projections. -/
lemma fieldConstantSheafToRestrictScalarsField_comp_map :
    fieldConstantSheafToRestrictScalarsField he X ≫
        (sheafCompose _ (ModuleCat.restrictScalars.{u + 1} (fieldRingHom.{u} e))).map
          (fieldConstantSheafToLowerStar Λ' g) ≫
        (lowerStarCompSheafComposeRestrictScalarsIso (fieldRingHom.{u} e) g).hom.app
          (fieldConstantSheaf Λ' Y) =
      fieldConstantSheafToLowerStar Λ g ≫
        (lowerStar (FieldCoefficients.{u} Λ) g).map
          (fieldConstantSheafToRestrictScalarsField he Y) := by
  rfl

/-- Restriction of scalars from `Λ'` to `Λ` commutes with the pushforward `g_*`: the underlying
sheaves agree, and so do the module structures. -/
noncomputable def fieldLowerStarCompRestrictScalarsIso :
    (g)_*ᶠ[Λ'] ⋙ fieldRestrictScalars he X ≅ fieldRestrictScalars he Y ⋙ (g)_*ᶠ[Λ] :=
  NatIso.ofComponents (fun N ↦ Mod.isoMk
      (M := (fieldRestrictScalars he X).obj ((g)_*ᶠ[Λ'].obj N))
      (N := (g)_*ᶠ[Λ].obj ((fieldRestrictScalars he Y).obj N)) (Iso.refl _) (by
        have : IsMonHom (fieldConstantSheafToLowerStar Λ g ≫
            (g)_*[FieldCoefficients.{u} Λ].map (fieldConstantSheafToRestrictScalarsField he Y)) :=
          @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ inferInstance
            (Functor.map.instIsMonHom (F := (g)_*[FieldCoefficients.{u} Λ]) _ _
              (fieldConstantSheafToRestrictScalarsField he Y))
        have h := Functor.act_comp_app_of_isMonoidal
          (lowerStarCompSheafComposeRestrictScalarsIso (fieldRingHom.{u} e) g).hom
          (fieldConstantSheafToLowerStar Λ' g) (fieldConstantSheafToRestrictScalarsField he X) _
          (fieldConstantSheafToRestrictScalarsField_comp_map he g) N
        refine Eq.trans rfl (h.trans ?_)
        simp only [fieldRestrictScalars, fieldLowerStar, Adjunction.modRight,
          Functor.comp_obj, Mod.act_comap_obj, Functor.act_mapMod_obj,
          Functor.LaxMonoidal.comp_μ, Functor.comp_map, comp_whiskerRight, Category.assoc,
          Functor.map_comp]
        have key := Functor.LaxMonoidal.μ_natural_left ((g)_*[FieldCoefficients.{u} Λ])
          (fieldConstantSheafToRestrictScalarsField he Y)
          ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} (fieldRingHom.{u} e))).obj N.X)
        erw [reassoc_of% key]
        rfl))
    fun f ↦ Mod.hom_ext _ _ (by simp; rfl)

/-- The extension of scalars commutes with pullbacks: `g^* (Λ' ⊗_Λ F) ≅ Λ' ⊗_Λ g^* F`, the
conjugate of `AlgebraicGeometry.ProEtale.fieldLowerStarCompRestrictScalarsIso`. -/
noncomputable def fieldUpperStarCompExtendScalarsIso :
    (g)^*ᶠ[Λ] ⋙ fieldExtendScalars he hc Y ≅ fieldExtendScalars he hc X ⋙ (g)^*ᶠ[Λ'] :=
  (conjugateIsoEquiv ((fieldExtendScalarsAdjunction he hc X).comp
      (fieldUpperStarLowerStarAdjunction Λ' g))
    ((fieldUpperStarLowerStarAdjunction Λ g).comp
      (fieldExtendScalarsAdjunction he hc Y))).symm
    (fieldLowerStarCompRestrictScalarsIso he g)

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts

variable (X)

instance : (fieldRestrictScalars he X).Additive :=
  inferInstanceAs (Functor.mapMod _ _ ⋙ Mod.comap _).Additive

instance : (fieldExtendScalars he hc X).Additive :=
  (fieldExtendScalarsAdjunction he hc X).left_adjoint_additive

instance : PreservesFiniteColimits (fieldExtendScalars he hc X) :=
  have : PreservesColimitsOfSize.{0, 0} (fieldExtendScalars he hc X) :=
    (fieldExtendScalarsAdjunction he hc X).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] [FiniteDimensional ℚ_[l] Λ'] in
lemma flat_fieldRingHom : (fieldRingHom.{u} e).Flat := by
  let := (fieldRingHom.{u} e).toAlgebra
  exact inferInstanceAs (Module.Flat (ULift.{u + 1} Λ) (ULift.{u + 1} Λ'))

/-- The extension of scalars `Λ' ⊗_Λ -` is exact: its underlying functor on sheaves is the
extension of scalars along the flat field extension `Λ ⟶ Λ'`. -/
instance : PreservesFiniteLimits (fieldExtendScalars he hc X) :=
  have := preservesFiniteLimits_sheafExtendScalars X (flat_fieldRingHom (e := e))
  have : PreservesFiniteLimits (fieldExtendScalars he hc X ⋙ FieldSheaf.forget X) :=
    inferInstanceAs (PreservesFiniteLimits
      (FieldSheaf.forget X ⋙ sheafExtendScalars (fieldRingHom.{u} e) X))
  preservesFiniteLimits_of_reflects_of_preserves _ (FieldSheaf.forget X)

variable {X}

/-- The extension of scalars of a lisse `Λ`-adic sheaf is lisse. -/
lemma IsFieldLisseSheaf.extendScalars {F : FieldSheaf Λ X} (hF : IsFieldLisseSheaf F) :
    IsFieldLisseSheaf ((fieldExtendScalars he hc X).obj F) := by
  obtain ⟨R, hR, h⟩ := hF
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, ⟨i⟩⟩ := h f hf
  exact ⟨n, ⟨((fieldUpperStarCompExtendScalarsIso he hc f).app F).symm ≪≫
    (fieldExtendScalars he hc V).mapIso i ≪≫
    (fieldExtendScalars he hc V).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ fieldExtendScalarsUnitIso he hc V⟩⟩

/-- The extension of scalars of a stratified lisse `Λ`-adic sheaf is stratified lisse. -/
lemma IsFieldStratifiedLisseSheaf.extendScalars {F : FieldSheaf Λ X}
    (hF : IsFieldStratifiedLisseSheaf F) :
    IsFieldStratifiedLisseSheaf ((fieldExtendScalars he hc X).obj F) := by
  obtain ⟨I, hI, Z, i, hi, hc', hcover, h⟩ := hF
  exact ⟨I, hI, Z, i, hi, hc', hcover, fun k ↦ ((h k).extendScalars he hc).of_iso
    ((fieldUpperStarCompExtendScalarsIso he hc (i k)).app F)⟩

/-- The extension of scalars of a constructible `Λ`-adic sheaf is constructible. -/
lemma IsFieldConstructibleSheaf.extendScalars {F : FieldSheaf Λ X}
    (hF : IsFieldConstructibleSheaf F) :
    IsFieldConstructibleSheaf ((fieldExtendScalars he hc X).obj F) := by
  intro x
  obtain ⟨W, j, hj, hx, h⟩ := hF x
  exact ⟨W, j, hj, hx, (h.extendScalars he hc).of_iso
    ((fieldUpperStarCompExtendScalarsIso he hc j).app F)⟩

end AlgebraicGeometry.ProEtale
