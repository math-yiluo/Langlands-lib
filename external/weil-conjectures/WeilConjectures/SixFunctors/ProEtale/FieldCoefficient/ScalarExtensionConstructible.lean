/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension

/-!
# Extension of scalars to `ℚ̄_ℓ` is exact and preserves constructibility

Let `Λ` be a finite extension of `ℚ_ℓ` with a continuous embedding `e : Λ → ℚ̄_ℓ`, and
`ℚ̄_ℓ ⊗_Λ - : Sh(X_proét, Λ_X) ⥤ Sh(X_proét, ℚ̄_ℓ,X)` the extension of scalars of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension`. This file shows:

- it is left adjoint to the restriction of scalars
  (`AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdicAdjunction`), and exact, its underlying
  functor being the extension of scalars of sheaves along the flat `Λ → ℚ̄_ℓ`;
- it sends `Λ_X` to `ℚ̄_ℓ,X` (`AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdicUnitIso`);
- it commutes with pullbacks
  (`AlgebraicGeometry.ProEtale.fieldUpperStarCompExtendScalarsToAdicIso`),
  being the left adjoint of the restriction of scalars, which commutes with pushforwards
  (`AlgebraicGeometry.ProEtale.adicLowerStarCompFieldRestrictScalarsIso`);
- hence it sends lisse, stratified lisse and constructible `Λ`-adic sheaves to lisse, stratified
  lisse and constructible `ℓ`-adic sheaves
  (`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.extendScalarsToAdic`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ)) (X : Scheme.{u})

/-- Restriction of scalars from `ℓ`-adic sheaves to sheaves of `Λ_X`-modules. -/
noncomputable def fieldRestrictScalarsFromAdic : AdicSheaf l X ⥤ FieldSheaf Λ X :=
  (sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).modRight
    (fieldConstantSheafToRestrictScalars he X)

/-- The extension of scalars `ℚ̄_ℓ ⊗_Λ -` is left adjoint to the restriction of scalars. -/
noncomputable def fieldExtendScalarsToAdicAdjunction :
    fieldExtendScalarsToAdic he hc X ⊣ fieldRestrictScalarsFromAdic he X :=
  haveI : IsIso (((sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalars he X)) :=
    isIso_extendScalarsFieldConstantSheafHom he hc X
  haveI : IsMonHom (((sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalars he X)) :=
    isMonHom_extendScalarsFieldConstantSheafHom he X
  (sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).modAdjunction _

/-- The extension of scalars of the constant sheaf `Λ_X` is the constant `ℓ`-adic sheaf. -/
noncomputable def fieldExtendScalarsToAdicUnitIso :
    (fieldExtendScalarsToAdic he hc X).obj (FieldSheaf.unit Λ X) ≅ AdicSheaf.unit l X :=
  haveI : IsIso (extendScalarsFieldConstantSheafHom he X) :=
    isIso_extendScalarsFieldConstantSheafHom he hc X
  Mod.regularIsoOfIsIso (extendScalarsFieldConstantSheafHom he X)

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

omit [IsUltrametricDist Λ] in
/-- The two ring maps `Λ_X ⟶ ℚ̄_ℓ,X ⟶ g_* ℚ̄_ℓ,Y` and `Λ_X ⟶ g_* Λ_Y ⟶ g_* ℚ̄_ℓ,Y` agree: both
compose functions with `e` and with the projections. -/
lemma fieldConstantSheafToRestrictScalars_comp_map :
    fieldConstantSheafToRestrictScalars he X ≫
        (sheafCompose _ (ModuleCat.restrictScalars.{u + 1} (fieldToAdicRingHom.{u} e))).map
          (adicConstantSheafToLowerStar l g) ≫
        (lowerStarCompSheafComposeRestrictScalarsIso (fieldToAdicRingHom.{u} e) g).hom.app
          (adicConstantSheaf l Y) =
      fieldConstantSheafToLowerStar Λ g ≫
        (lowerStar (FieldCoefficients.{u} Λ) g).map (fieldConstantSheafToRestrictScalars he Y) := by
  rfl


/-- Restriction of scalars from `ℓ`-adic sheaves commutes with the pushforward `g_*`: the
underlying sheaves agree, and so do the module structures, the ring maps
`Λ_X ⟶ ℚ̄_ℓ,X ⟶ g_* ℚ̄_ℓ,Y` and `Λ_X ⟶ g_* Λ_Y ⟶ g_* ℚ̄_ℓ,Y` being equal. -/
noncomputable def adicLowerStarCompFieldRestrictScalarsIso :
    (g)_*ᵃ[l] ⋙ fieldRestrictScalarsFromAdic he X ≅
      fieldRestrictScalarsFromAdic he Y ⋙ (g)_*ᶠ[Λ] :=
  NatIso.ofComponents (fun N ↦ Mod.isoMk
      (M := (fieldRestrictScalarsFromAdic he X).obj ((g)_*ᵃ[l].obj N))
      (N := (g)_*ᶠ[Λ].obj ((fieldRestrictScalarsFromAdic he Y).obj N)) (Iso.refl _) (by
        have : IsMonHom (fieldConstantSheafToLowerStar Λ g ≫
            (g)_*[FieldCoefficients.{u} Λ].map (fieldConstantSheafToRestrictScalars he Y)) :=
          @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ inferInstance
            (Functor.map.instIsMonHom (F := (g)_*[FieldCoefficients.{u} Λ]) _ _
              (fieldConstantSheafToRestrictScalars he Y))
        have h := Functor.act_comp_app_of_isMonoidal
          (lowerStarCompSheafComposeRestrictScalarsIso (fieldToAdicRingHom.{u} e) g).hom
          (adicConstantSheafToLowerStar l g) (fieldConstantSheafToRestrictScalars he X) _
          (fieldConstantSheafToRestrictScalars_comp_map he g) N
        refine Eq.trans rfl (h.trans ?_)
        simp only [fieldRestrictScalarsFromAdic, fieldLowerStar, Adjunction.modRight,
          Functor.comp_obj, Mod.act_comap_obj, Functor.act_mapMod_obj,
          Functor.LaxMonoidal.comp_μ, Functor.comp_map, comp_whiskerRight, Category.assoc,
          Functor.map_comp]
        have key := Functor.LaxMonoidal.μ_natural_left ((g)_*[FieldCoefficients.{u} Λ])
          (fieldConstantSheafToRestrictScalars he Y)
          ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} (fieldToAdicRingHom.{u} e))).obj N.X)
        erw [reassoc_of% key]
        rfl))
    fun f ↦ Mod.hom_ext _ _ (by simp; rfl)


/-- The extension of scalars commutes with pullbacks: `g^* (ℚ̄_ℓ ⊗_Λ F) ≅ ℚ̄_ℓ ⊗_Λ g^* F`, the
conjugate of `AlgebraicGeometry.ProEtale.adicLowerStarCompFieldRestrictScalarsIso`. -/
noncomputable def fieldUpperStarCompExtendScalarsToAdicIso :
    (g)^*ᶠ[Λ] ⋙ fieldExtendScalarsToAdic he hc Y ≅ fieldExtendScalarsToAdic he hc X ⋙ (g)^*ᵃ[l] :=
  (conjugateIsoEquiv ((fieldExtendScalarsToAdicAdjunction he hc X).comp
      (adicUpperStarLowerStarAdjunction l g))
    ((fieldUpperStarLowerStarAdjunction Λ g).comp
      (fieldExtendScalarsToAdicAdjunction he hc Y))).symm
    (adicLowerStarCompFieldRestrictScalarsIso he g)


attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts

instance : (fieldRestrictScalarsFromAdic he X).Additive :=
  inferInstanceAs (Functor.mapMod _ _ ⋙ Mod.comap _).Additive

instance : (fieldExtendScalarsToAdic he hc X).Additive :=
  (fieldExtendScalarsToAdicAdjunction he hc X).left_adjoint_additive

instance : PreservesFiniteColimits (fieldExtendScalarsToAdic he hc X) :=
  have : PreservesColimitsOfSize.{0, 0} (fieldExtendScalarsToAdic he hc X) :=
    (fieldExtendScalarsToAdicAdjunction he hc X).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

omit [IsUltrametricDist Λ] [FiniteDimensional ℚ_[l] Λ] in
lemma flat_fieldToAdicRingHom : (fieldToAdicRingHom.{u} e).Flat := by
  let := (fieldToAdicRingHom.{u} e).toAlgebra
  exact inferInstanceAs (Module.Flat (ULift.{u + 1} Λ) (ULift.{u + 1} (PadicAlgCl l)))

/-- The extension of scalars `ℚ̄_ℓ ⊗_Λ -` is exact: its underlying functor on sheaves is the
extension of scalars along the flat field extension `Λ ⟶ ℚ̄_ℓ`. -/
instance : PreservesFiniteLimits (fieldExtendScalarsToAdic he hc X) :=
  have := preservesFiniteLimits_sheafExtendScalars X (flat_fieldToAdicRingHom (e := e))
  have : PreservesFiniteLimits (fieldExtendScalarsToAdic he hc X ⋙ AdicSheaf.forget X) :=
    inferInstanceAs (PreservesFiniteLimits
      (FieldSheaf.forget X ⋙ sheafExtendScalars (fieldToAdicRingHom.{u} e) X))
  preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.forget X)

/-- The extension of scalars of a lisse `Λ`-adic sheaf is lisse. -/
lemma IsFieldLisseSheaf.extendScalarsToAdic {F : FieldSheaf Λ X} (hF : IsFieldLisseSheaf F) :
    IsAdicLisseSheaf ((fieldExtendScalarsToAdic he hc X).obj F) := by
  obtain ⟨R, hR, h⟩ := hF
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, ⟨i⟩⟩ := h f hf
  exact ⟨n, ⟨((fieldUpperStarCompExtendScalarsToAdicIso he hc f).app F).symm ≪≫
    (fieldExtendScalarsToAdic he hc V).mapIso i ≪≫
    (fieldExtendScalarsToAdic he hc V).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ fieldExtendScalarsToAdicUnitIso he hc V⟩⟩

/-- The extension of scalars of a stratified lisse `Λ`-adic sheaf is stratified lisse. -/
lemma IsFieldStratifiedLisseSheaf.extendScalarsToAdic {F : FieldSheaf Λ X}
    (hF : IsFieldStratifiedLisseSheaf F) :
    IsAdicStratifiedLisseSheaf ((fieldExtendScalarsToAdic he hc X).obj F) := by
  obtain ⟨I, hI, Z, i, hi, hc', hcover, h⟩ := hF
  exact ⟨I, hI, Z, i, hi, hc', hcover, fun k ↦ ((h k).extendScalarsToAdic he hc).of_iso
    ((fieldUpperStarCompExtendScalarsToAdicIso he hc (i k)).app F)⟩

/-- The extension of scalars of a constructible `Λ`-adic sheaf is constructible. -/
lemma IsFieldConstructibleSheaf.extendScalarsToAdic {F : FieldSheaf Λ X}
    (hF : IsFieldConstructibleSheaf F) :
    IsAdicConstructibleSheaf ((fieldExtendScalarsToAdic he hc X).obj F) := by
  intro x
  obtain ⟨W, j, hj, hx, h⟩ := hF x
  exact ⟨W, j, hj, hx, (h.extendScalarsToAdic he hc).of_iso
    ((fieldUpperStarCompExtendScalarsToAdicIso he hc j).app F)⟩

end AlgebraicGeometry.ProEtale
