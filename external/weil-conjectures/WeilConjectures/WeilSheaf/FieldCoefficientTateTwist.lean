/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.WeilSheaf.FieldCoefficientCohomology
public import WeilConjectures.WeilSheaf.FieldCoefficientTransition
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# Tate twists commute with extension of scalars

Following blueprint `proposition-weights-under-usual-operations--13`, the Tate twist `(-)(m)`
commutes with finite scalar extension: for finite extensions `E ⊆ F` of `ℚ_ℓ` inside `ℚ̄_ℓ` and
`m ∈ ℤ`,

`F ⊗_E E_X(m) ≅ F_X(m)`

compatibly with the Weil structures, and similarly `ℚ̄_ℓ ⊗_E E_X(m) ≅ ℚ̄_ℓ(m)`. Here
`E_X(m)` is the constant `E`-Weil sheaf `E_X` whose Weil structure is multiplied by the
cyclotomic unit `χ_ℓ(σ)ᵐ` (`AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant`).

The proof has three steps.

- The extension of scalars of the constant sheaf is the constant sheaf,
  `Λ' ⊗_Λ Λ_X̄ ≅ Λ'_X̄` (`AlgebraicGeometry.ProEtale.fieldExtendScalarsUnitIso`), and this
  identification is compatible with the canonical Weil structures
  `Fr^* Λ_X̄ = (Fr⁻¹)_* Λ_X̄ ≅ Λ_X̄`. Both identifications are adjoint to the maps on functions
  (composition with `e : Λ → Λ'` and pullback along `Fr`), which commute.
- Extension of scalars along `e` turns multiplication by `b ∈ Λˣ` into multiplication by
  `e(b)`, so it commutes with constant twists.
- The inclusion `E → F` is a `ℚ_ℓ`-algebra map, so it sends the cyclotomic unit of `E` to that
  of `F`.

## Main declarations

- `AlgebraicGeometry.ProEtale.fieldExtendScalars_map_smul`: `Λ' ⊗_Λ (c • -) = e(c) • -`.
- `AlgebraicGeometry.ProEtaleFieldWeilSheaf.constantTwist`: the constant twist of a pro-étale
  `Λ`-Weil sheaf.
- `AlgebraicGeometry.ProEtaleFieldWeilSheaf.extendScalarsConstantTwistIso` and
  `AlgebraicGeometry.ProEtaleFieldWeilSheaf.extendScalarsToAdicConstantTwistIso`: extension of
  scalars commutes with constant twists.
- `AlgebraicGeometry.FieldWeilSheaf.extendScalarsConstantIso`: `Λ' ⊗_Λ Λ_X ≅ Λ'_X` as Weil
  sheaves.
- `AlgebraicGeometry.FieldWeilSheaf.extendScalarsToAdicConstantIso`: `ℚ̄_ℓ ⊗_Λ Λ_X ≅ ℚ̄_ℓ` as
  Weil sheaves.
- `AlgebraicGeometry.FieldWeilSheaf.extendScalarsTateTwistConstantIso`: `F ⊗_E E_X(m) ≅ F_X(m)`.
- `AlgebraicGeometry.FieldWeilSheaf.extendScalarsToAdicTateTwistConstantIso`:
  `ℚ̄_ℓ ⊗_E E_X(m) ≅ ℚ̄_ℓ(m)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- The adjoint of a morphism out of `F c` precomposed with the comparison
`F c ≅ F' c` of two left adjoints of `G` is the unit of `F' ⊣ G` followed by `G` of the
morphism. -/
lemma Adjunction.homEquiv_leftAdjointUniq_hom_app_comp {F F' : C ⥤ D} {G : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G) {c : C} {d : D} (f : F'.obj c ⟶ d) :
    adj1.homEquiv _ _ ((adj1.leftAdjointUniq adj2).hom.app c ≫ f) =
      adj2.unit.app c ≫ G.map f := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]

/-- **Extensions of scalars and pullbacks of units.** Let `E₁ ⊣ R₁`, `E₂ ⊣ R₂`, `U ⊣ U'`,
`V ⊣ V'` be adjunctions forming a square (extensions of scalars `E₁`, `E₂` and pullbacks `U`,
`V`), and let `γ : U ⋙ E₂ ≅ E₁ ⋙ V` be the conjugate of an isomorphism
`β : V' ⋙ R₁ ≅ R₂ ⋙ U'`. Then morphisms `u₁ : E₁ A₁ ⟶ B₁`, `u₂ : E₂ A₂ ⟶ B₂`, `v : U A₁ ⟶ A₂`,
`v' : V B₁ ⟶ B₂` satisfy `γ ≫ V u₁ ≫ v' = E₂ v ≫ u₂` as soon as their adjoints satisfy the
corresponding identity. -/
lemma conjugateIsoEquiv_symm_hom_app_comp_map_comp {C₁ C₂ D₁ D₂ : Type*} [Category C₁]
    [Category C₂] [Category D₁] [Category D₂] {E₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {E₂ : C₂ ⥤ D₂}
    {R₂ : D₂ ⥤ C₂} {U : C₁ ⥤ C₂} {U' : C₂ ⥤ C₁} {V : D₁ ⥤ D₂} {V' : D₂ ⥤ D₁}
    (adjE₁ : E₁ ⊣ R₁) (adjE₂ : E₂ ⊣ R₂) (adjU : U ⊣ U') (adjV : V ⊣ V')
    (β : V' ⋙ R₁ ≅ R₂ ⋙ U') {A₁ : C₁} {B₁ : D₁} {A₂ : C₂} {B₂ : D₂} (u₁ : E₁.obj A₁ ⟶ B₁)
    (u₂ : E₂.obj A₂ ⟶ B₂) (v : U.obj A₁ ⟶ A₂) (v' : V.obj B₁ ⟶ B₂)
    (h : adjE₁.homEquiv _ _ u₁ ≫ R₁.map (adjV.homEquiv _ _ v') ≫ β.hom.app B₂ =
      adjU.homEquiv _ _ v ≫ U'.map (adjE₂.homEquiv _ _ u₂)) :
    ((conjugateIsoEquiv (adjE₁.comp adjV) (adjU.comp adjE₂)).symm β).hom.app A₁ ≫
        V.map u₁ ≫ v' = E₂.map v ≫ u₂ := by
  apply ((adjU.comp adjE₂).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Functor.map_comp, conjugateIsoEquiv_symm_apply_hom]
  erw [← reassoc_of% (unit_conjugateEquiv_symm (adjE₁.comp adjV) (adjU.comp adjE₂) β.hom A₁)]
  rw [← β.hom.naturality, ← Category.assoc,
    ← (adjE₁.comp adjV).homEquiv_unit, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.trans_apply]
  erw [adjV.homEquiv_naturality_left, adjE₁.homEquiv_naturality_right,
    adjE₂.homEquiv_naturality_left, adjU.homEquiv_naturality_right]
  simpa only [Functor.comp_map, Category.assoc] using h

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

section Field

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

omit [IsUltrametricDist Λ] in
/-- Pulling back functions along equal morphisms agrees with the congruence isomorphism of
pushforwards. -/
lemma fieldConstantSheafToLowerStar_comp_lowerStarCongr_inv {W Y : Scheme.{u}} {f f' : W ⟶ Y}
    (h : f = f') :
    fieldConstantSheafToLowerStar Λ f' ≫
        (lowerStarCongr (FieldCoefficients.{u} Λ) h).inv.app (FieldSheaf.unit Λ W).X =
      fieldConstantSheafToLowerStar Λ f := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_inv, NatTrans.id_app]
  exact Category.comp_id _

omit [IsUltrametricDist Λ] in
/-- Pulling back functions along the identity is the identification `𝟭 ≅ (𝟙 Y)_*`. -/
lemma fieldConstantSheafToLowerStar_id_eq (Y : Scheme.{u}) :
    fieldConstantSheafToLowerStar Λ (𝟙 Y) =
      (lowerStarId (FieldCoefficients.{u} Λ) Y).inv.app (FieldSheaf.unit Λ Y).X := by
  rw [← Category.comp_id (fieldConstantSheafToLowerStar Λ (𝟙 Y)),
    ← Iso.hom_inv_id_app (lowerStarId (FieldCoefficients.{u} Λ) Y),
    reassoc_of% (fieldConstantSheafToLowerStar_id Λ Y)]
  rfl

omit [IsUltrametricDist Λ] in
/-- For `a ≫ b = 𝟙`, pulling back functions along `b` and then along `a` is the identification
`𝟭 ≅ (𝟙 Y)_* = (a ≫ b)_* ≅ b_* a_*`. (Stated for arbitrary `a`, `b`, `h`: for the components of
an isomorphism the kernel is slow to check the same proof.) -/
lemma fieldConstantSheafToLowerStar_comp_map_of_comp_eq_id {X Y : Scheme.{u}} (a : Y ⟶ X)
    (b : X ⟶ Y) (h : a ≫ b = 𝟙 Y) :
    fieldConstantSheafToLowerStar Λ b ≫
        (b)_*[FieldCoefficients.{u} Λ].map (fieldConstantSheafToLowerStar Λ a) =
      (lowerStarId (FieldCoefficients.{u} Λ) Y).inv.app (FieldSheaf.unit Λ Y).X ≫
        (lowerStarCongr (FieldCoefficients.{u} Λ) h).inv.app (FieldSheaf.unit Λ Y).X ≫
          (lowerStarComp (FieldCoefficients.{u} Λ) a b).inv.app (FieldSheaf.unit Λ Y).X := by
  rw [← fieldConstantSheafToLowerStar_id_eq,
    reassoc_of% (fieldConstantSheafToLowerStar_comp_lowerStarCongr_inv h),
    ← fieldConstantSheafToLowerStar_comp Λ a b, Category.assoc, Category.assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]

/-- The adjoint of the identification `g^* Λ_Y ≅ Λ_X` is the pullback of functions
`Λ_Y ⟶ g_* Λ_X`. -/
lemma fieldUpperStarLowerStarAdjunction_homEquiv_fieldUpperStarUnitIso_hom_hom
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ((fieldUpperStarLowerStarAdjunction Λ g).homEquiv _ _ (fieldUpperStarUnitIso Λ g).hom).hom =
      fieldConstantSheafToLowerStar Λ g :=
  (Adjunction.modAdjunction_homEquiv_apply_hom _ _ _).trans (Equiv.apply_symm_apply _ _)

omit [IsUltrametricDist Λ] in
lemma fieldLowerStarId_inv_app_hom (X : Scheme.{u}) (M : FieldSheaf Λ X) :
    ((fieldLowerStarId Λ X).inv.app M).hom =
      (lowerStarId (FieldCoefficients.{u} Λ) X).inv.app M.X :=
  Category.id_comp _

omit [IsUltrametricDist Λ] in
lemma fieldLowerStarCongr_inv_app_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (M : FieldSheaf Λ Z) :
    ((fieldLowerStarCongr Λ h).inv.app M).hom =
      (lowerStarCongr (FieldCoefficients.{u} Λ) h).inv.app M.X :=
  rfl

omit [IsUltrametricDist Λ] in
/-- For `a ≫ b = 𝟙`, the inverse of the identification `b_* a_* ≅ (a ≫ b)_* = (𝟙 Y)_* ≅ 𝟭` is
that of the underlying sheaves. -/
lemma fieldLowerStarComp_trans_inv_app_hom {X Y : Scheme.{u}} (a : Y ⟶ X) (b : X ⟶ Y)
    (h : a ≫ b = 𝟙 Y) (M : FieldSheaf Λ Y) :
    ((fieldLowerStarComp Λ a b ≪≫ fieldLowerStarCongr Λ h ≪≫ fieldLowerStarId Λ Y).inv.app
        M).hom =
      (lowerStarId (FieldCoefficients.{u} Λ) Y).inv.app M.X ≫
        (lowerStarCongr (FieldCoefficients.{u} Λ) h).inv.app M.X ≫
          (lowerStarComp (FieldCoefficients.{u} Λ) a b).inv.app M.X := by
  rw [Iso.trans_inv, Iso.trans_inv, NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom',
    Mod.comp_hom', fieldLowerStarId_inv_app_hom, fieldLowerStarCongr_inv_app_hom,
    fieldLowerStarComp_inv_app_hom, Category.assoc]

/-- The identification `g^* Λ_Y ≅ (g⁻¹)_* Λ_Y ≅ Λ_X` along an isomorphism `g : X ≅ Y` is the
identification `g^* Λ_Y ≅ Λ_X` of the pullback of the constant sheaf. -/
lemma fieldUpperStarIsoLowerStarInv_hom_app_unit_comp {X Y : Scheme.{u}} (g : X ≅ Y) :
    (fieldUpperStarIsoLowerStarInv Λ g).hom.app (FieldSheaf.unit Λ Y) ≫
        (fieldLowerStarUnitIso Λ g.symm).hom =
      (fieldUpperStarUnitIso Λ g.hom).hom := by
  apply ((fieldUpperStarLowerStarAdjunction Λ g.hom).homEquiv _ _).injective
  apply Mod.hom_ext
  rw [fieldUpperStarLowerStarAdjunction_homEquiv_fieldUpperStarUnitIso_hom_hom,
    fieldUpperStarIsoLowerStarInv, Adjunction.homEquiv_leftAdjointUniq_hom_app_comp, Mod.comp_hom',
    fieldLowerStar_map_hom, fieldLowerStarUnitIso_hom_hom,
    ← Functor.mapIso_hom (g.hom)_*[FieldCoefficients.{u} Λ], ← Iso.eq_comp_inv,
    Functor.mapIso_inv]
  exact (fieldLowerStarComp_trans_inv_app_hom g.inv g.hom g.inv_hom_id _).trans
    (fieldConstantSheafToLowerStar_comp_map_of_comp_eq_id g.inv g.hom g.inv_hom_id).symm

end Field

section ExtendScalars

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] in
/-- The adjoint `Λ_X ⟶ Λ'_X` of the identification `Λ' ⊗_Λ Λ_X ≅ Λ'_X` is the composition of
functions with `e`. -/
lemma fieldExtendScalarsAdjunction_homEquiv_fieldExtendScalarsUnitIso_hom_hom
    (X : Scheme.{u}) :
    ((fieldExtendScalarsAdjunction he hc X).homEquiv _ _
      (fieldExtendScalarsUnitIso he hc X).hom).hom =
      fieldConstantSheafToRestrictScalarsField he X := by
  have : IsIso (((sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalarsField he X)) :=
    isIso_extendScalarsFieldConstantSheafHomField he hc X
  have : IsMonHom (((sheafExtendScalarsAdjunction (fieldRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalarsField he X)) :=
    isMonHom_extendScalarsFieldConstantSheafHomField he X
  exact (Adjunction.modAdjunction_homEquiv_apply_hom _ _ _).trans (Equiv.apply_symm_apply _ _)

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] [FiniteDimensional ℚ_[l] Λ'] in
lemma fieldRestrictScalars_map_hom {X : Scheme.{u}} {M N : FieldSheaf Λ' X} (f : M ⟶ N) :
    ((fieldRestrictScalars he X).map f).hom =
      (sheafCompose _ (ModuleCat.restrictScalars.{u + 1} (fieldRingHom.{u} e))).map f.hom :=
  rfl

/-- The identifications `Λ' ⊗_Λ Λ_X ≅ Λ'_X` and `g^* Λ_X ≅ Λ_Y` are compatible with the
commutation `g^* (Λ' ⊗_Λ -) ≅ Λ' ⊗_Λ g^*` of extension of scalars with pullbacks. -/
lemma fieldUpperStarCompExtendScalarsIso_hom_app_unit_comp {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (fieldUpperStarCompExtendScalarsIso he hc g).hom.app (FieldSheaf.unit Λ X) ≫
        (g)^*ᶠ[Λ'].map (fieldExtendScalarsUnitIso he hc X).hom ≫
          (fieldUpperStarUnitIso Λ' g).hom =
      (fieldExtendScalars he hc Y).map (fieldUpperStarUnitIso Λ g).hom ≫
        (fieldExtendScalarsUnitIso he hc Y).hom :=
  conjugateIsoEquiv_symm_hom_app_comp_map_comp _ _ _ _ _ _ _ _ _ <| Mod.hom_ext _ _ <| by
    rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom', fieldRestrictScalars_map_hom,
      fieldLowerStar_map_hom,
      fieldExtendScalarsAdjunction_homEquiv_fieldExtendScalarsUnitIso_hom_hom,
      fieldUpperStarLowerStarAdjunction_homEquiv_fieldUpperStarUnitIso_hom_hom,
      fieldUpperStarLowerStarAdjunction_homEquiv_fieldUpperStarUnitIso_hom_hom,
      fieldExtendScalarsAdjunction_homEquiv_fieldExtendScalarsUnitIso_hom_hom]
    exact fieldConstantSheafToRestrictScalarsField_comp_map he g

/-- The identification `Λ' ⊗_Λ Λ_Y ≅ Λ'_Y` is compatible with the identifications
`(g⁻¹)_* Λ_Y ≅ Λ_X` and `(g⁻¹)_* Λ'_Y ≅ Λ'_X` along an isomorphism `g : X ≅ Y`, through the
commutation `(g⁻¹)_* (Λ' ⊗_Λ -) ≅ g^* (Λ' ⊗_Λ -) ≅ Λ' ⊗_Λ g^* ≅ Λ' ⊗_Λ (g⁻¹)_*`. -/
lemma fieldLowerStar_map_fieldExtendScalarsUnitIso_hom_comp {X Y : Scheme.{u}} (g : X ≅ Y) :
    (g.inv)_*ᶠ[Λ'].map (fieldExtendScalarsUnitIso he hc Y).hom ≫
        (fieldLowerStarUnitIso Λ' g.symm).hom =
      (((fieldUpperStarIsoLowerStarInv Λ' g).inv.app _ ≫
          (fieldUpperStarCompExtendScalarsIso he hc g.hom).inv.app _ ≫
            (fieldExtendScalars he hc X).map
              ((fieldUpperStarIsoLowerStarInv Λ g).hom.app (FieldSheaf.unit Λ Y))) ≫
        (fieldExtendScalars he hc X).map (fieldLowerStarUnitIso Λ g.symm).hom) ≫
          (fieldExtendScalarsUnitIso he hc X).hom := by
  simp only [Category.assoc]
  rw [(Iso.eq_inv_comp ((fieldUpperStarIsoLowerStarInv Λ' g).app _)).2
      (fieldUpperStarIsoLowerStarInv_hom_app_unit_comp (Λ := Λ') g), Iso.app_inv,
    (fieldUpperStarIsoLowerStarInv Λ' g).inv.naturality_assoc, ← Functor.map_comp_assoc,
    fieldUpperStarIsoLowerStarInv_hom_app_unit_comp, cancel_epi, ← Iso.app_inv,
    Iso.eq_inv_comp, Iso.app_hom]
  exact fieldUpperStarCompExtendScalarsIso_hom_app_unit_comp he hc g.hom

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] [FiniteDimensional ℚ_[l] Λ'] in
/-- Restriction of scalars along `e` turns multiplication by `e(c)` into multiplication by
`c`. -/
lemma fieldRestrictScalars_map_smul {X : Scheme.{u}} (c : ULift.{u + 1} Λ)
    (N : FieldSheaf Λ' X) :
    (fieldRestrictScalars he X).map (FieldSheaf.smul (fieldRingHom.{u} e c) N) =
      FieldSheaf.smul c ((fieldRestrictScalars he X).obj N) :=
  Mod.hom_ext _ _ (by ext : 3; rfl)

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] in
/-- Extension of scalars along `e` turns multiplication by `c` into multiplication by
`e(c)`. -/
lemma fieldExtendScalars_map_smul {X : Scheme.{u}} (c : ULift.{u + 1} Λ) (M : FieldSheaf Λ X) :
    (fieldExtendScalars he hc X).map (FieldSheaf.smul c M) =
      FieldSheaf.smul (fieldRingHom.{u} e c) ((fieldExtendScalars he hc X).obj M) := by
  apply ((fieldExtendScalarsAdjunction he hc X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, fieldRestrictScalars_map_smul]
  exact ((fieldExtendScalarsAdjunction he hc X).unit.naturality _).symm.trans
    (FieldSheaf.smul_comp c _)

omit [IsUltrametricDist Λ] [IsUltrametricDist Λ'] in
/-- Extension of scalars along `e` turns multiplication by a unit `b` into multiplication by
`e(b)`. -/
lemma fieldExtendScalars_map_smulIso_hom {X : Scheme.{u}} (b : Λˣ) (M : FieldSheaf Λ X) :
    (fieldExtendScalars he hc X).map (FieldSheaf.smulIso b M).hom =
      (FieldSheaf.smulIso (Units.map (e : Λ →* Λ') b) ((fieldExtendScalars he hc X).obj M)).hom :=
  fieldExtendScalars_map_smul he hc _ M

end ExtendScalars

section Adic

variable (l : ℕ) [Fact l.Prime]

/-- Pulling back functions along equal morphisms agrees with the congruence isomorphism of
pushforwards. -/
lemma adicConstantSheafToLowerStar_comp_lowerStarCongr_inv {W Y : Scheme.{u}} {f f' : W ⟶ Y}
    (h : f = f') :
    adicConstantSheafToLowerStar l f' ≫
        (lowerStarCongr (WeilCoefficients.{u} l) h).inv.app (AdicSheaf.unit l W).X =
      adicConstantSheafToLowerStar l f := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_inv, NatTrans.id_app]
  exact Category.comp_id _

/-- Pulling back functions along the identity is the identification `𝟭 ≅ (𝟙 Y)_*`. -/
lemma adicConstantSheafToLowerStar_id_eq (Y : Scheme.{u}) :
    adicConstantSheafToLowerStar l (𝟙 Y) =
      (lowerStarId (WeilCoefficients.{u} l) Y).inv.app (AdicSheaf.unit l Y).X := by
  rw [← Category.comp_id (adicConstantSheafToLowerStar l (𝟙 Y)),
    ← Iso.hom_inv_id_app (lowerStarId (WeilCoefficients.{u} l) Y),
    reassoc_of% (adicConstantSheafToLowerStar_id l Y)]
  rfl

/-- For `a ≫ b = 𝟙`, pulling back functions along `b` and then along `a` is the identification
`𝟭 ≅ (𝟙 Y)_* = (a ≫ b)_* ≅ b_* a_*`. (Stated for arbitrary `a`, `b`, `h`: for the components of
an isomorphism the kernel is slow to check the same proof.) -/
lemma adicConstantSheafToLowerStar_comp_map_of_comp_eq_id {X Y : Scheme.{u}} (a : Y ⟶ X)
    (b : X ⟶ Y) (h : a ≫ b = 𝟙 Y) :
    adicConstantSheafToLowerStar l b ≫
        (b)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l a) =
      (lowerStarId (WeilCoefficients.{u} l) Y).inv.app (AdicSheaf.unit l Y).X ≫
        (lowerStarCongr (WeilCoefficients.{u} l) h).inv.app (AdicSheaf.unit l Y).X ≫
          (lowerStarComp (WeilCoefficients.{u} l) a b).inv.app (AdicSheaf.unit l Y).X := by
  rw [← adicConstantSheafToLowerStar_id_eq,
    reassoc_of% (adicConstantSheafToLowerStar_comp_lowerStarCongr_inv l h),
    ← adicConstantSheafToLowerStar_comp l a b, Category.assoc, Category.assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]

/-- The adjoint of the identification `g^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X` is the pullback of functions
`ℚ̄_ℓ,Y ⟶ g_* ℚ̄_ℓ,X`. -/
lemma adicUpperStarLowerStarAdjunction_homEquiv_adicUpperStarUnitIso_hom_hom
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ((adicUpperStarLowerStarAdjunction l g).homEquiv _ _ (adicUpperStarUnitIso l g).hom).hom =
      adicConstantSheafToLowerStar l g :=
  (Adjunction.modAdjunction_homEquiv_apply_hom _ _ _).trans (Equiv.apply_symm_apply _ _)

/-- For `a ≫ b = 𝟙`, the inverse of the identification `b_* a_* ≅ (a ≫ b)_* = (𝟙 Y)_* ≅ 𝟭` is
that of the underlying sheaves. -/
lemma adicLowerStarComp_trans_inv_app_hom {X Y : Scheme.{u}} (a : Y ⟶ X) (b : X ⟶ Y)
    (h : a ≫ b = 𝟙 Y) (M : AdicSheaf l Y) :
    ((adicLowerStarComp l a b ≪≫ adicLowerStarCongr l h ≪≫ adicLowerStarId l Y).inv.app M).hom =
      (lowerStarId (WeilCoefficients.{u} l) Y).inv.app M.X ≫
        (lowerStarCongr (WeilCoefficients.{u} l) h).inv.app M.X ≫
          (lowerStarComp (WeilCoefficients.{u} l) a b).inv.app M.X := by
  rw [Iso.trans_inv, Iso.trans_inv, NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom',
    Mod.comp_hom', adicLowerStarId_inv_app_hom, adicLowerStarCongr_inv_app_hom,
    adicLowerStarComp_inv_app_hom, Category.assoc]

/-- The identification `g^* ℚ̄_ℓ,Y ≅ (g⁻¹)_* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X` along an isomorphism `g : X ≅ Y`
is the identification `g^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X` of the pullback of the constant sheaf. -/
lemma adicUpperStarIsoLowerStarInv_hom_app_unit_comp {X Y : Scheme.{u}} (g : X ≅ Y) :
    (adicUpperStarIsoLowerStarInv l g).hom.app (AdicSheaf.unit l Y) ≫
        (adicLowerStarUnitIso l g.symm).hom =
      (adicUpperStarUnitIso l g.hom).hom := by
  apply ((adicUpperStarLowerStarAdjunction l g.hom).homEquiv _ _).injective
  apply Mod.hom_ext
  rw [adicUpperStarLowerStarAdjunction_homEquiv_adicUpperStarUnitIso_hom_hom,
    adicUpperStarIsoLowerStarInv, Adjunction.homEquiv_leftAdjointUniq_hom_app_comp, Mod.comp_hom',
    adicLowerStar_map_hom, adicLowerStarUnitIso_hom_hom,
    ← Functor.mapIso_hom (g.hom)_*[WeilCoefficients.{u} l], ← Iso.eq_comp_inv,
    Functor.mapIso_inv]
  exact (adicLowerStarComp_trans_inv_app_hom l g.inv g.hom g.inv_hom_id _).trans
    (adicConstantSheafToLowerStar_comp_map_of_comp_eq_id l g.inv g.hom g.inv_hom_id).symm

end Adic

section ExtendScalarsToAdic

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))

omit [IsUltrametricDist Λ] in
/-- The adjoint `Λ_X ⟶ ℚ̄_ℓ,X` of the identification `ℚ̄_ℓ ⊗_Λ Λ_X ≅ ℚ̄_ℓ,X` is the composition of
functions with `e`. -/
lemma fieldExtendScalarsToAdicAdjunction_homEquiv_fieldExtendScalarsToAdicUnitIso_hom_hom
    (X : Scheme.{u}) :
    ((fieldExtendScalarsToAdicAdjunction he hc X).homEquiv _ _
      (fieldExtendScalarsToAdicUnitIso he hc X).hom).hom =
      fieldConstantSheafToRestrictScalars he X := by
  have : IsIso (((sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalars he X)) :=
    isIso_extendScalarsFieldConstantSheafHom he hc X
  have : IsMonHom (((sheafExtendScalarsAdjunction (fieldToAdicRingHom.{u} e) X).homEquiv _ _).symm
      (fieldConstantSheafToRestrictScalars he X)) :=
    isMonHom_extendScalarsFieldConstantSheafHom he X
  exact (Adjunction.modAdjunction_homEquiv_apply_hom _ _ _).trans (Equiv.apply_symm_apply _ _)

omit [IsUltrametricDist Λ] in
lemma fieldRestrictScalarsFromAdic_map_hom {X : Scheme.{u}} {M N : AdicSheaf l X} (f : M ⟶ N) :
    ((fieldRestrictScalarsFromAdic he X).map f).hom =
      (sheafCompose _ (ModuleCat.restrictScalars.{u + 1} (fieldToAdicRingHom.{u} e))).map f.hom :=
  rfl

/-- The identifications `ℚ̄_ℓ ⊗_Λ Λ_X ≅ ℚ̄_ℓ,X` and `g^* Λ_X ≅ Λ_Y` are compatible with the
commutation `g^* (ℚ̄_ℓ ⊗_Λ -) ≅ ℚ̄_ℓ ⊗_Λ g^*` of extension of scalars with pullbacks. -/
lemma fieldUpperStarCompExtendScalarsToAdicIso_hom_app_unit_comp {X Y : Scheme.{u}}
    (g : Y ⟶ X) :
    (fieldUpperStarCompExtendScalarsToAdicIso he hc g).hom.app (FieldSheaf.unit Λ X) ≫
        (g)^*ᵃ[l].map (fieldExtendScalarsToAdicUnitIso he hc X).hom ≫
          (adicUpperStarUnitIso l g).hom =
      (fieldExtendScalarsToAdic he hc Y).map (fieldUpperStarUnitIso Λ g).hom ≫
        (fieldExtendScalarsToAdicUnitIso he hc Y).hom :=
  conjugateIsoEquiv_symm_hom_app_comp_map_comp _ _ _ _ _ _ _ _ _ <| Mod.hom_ext _ _ <| by
    rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom', fieldRestrictScalarsFromAdic_map_hom,
      fieldLowerStar_map_hom,
      fieldExtendScalarsToAdicAdjunction_homEquiv_fieldExtendScalarsToAdicUnitIso_hom_hom,
      adicUpperStarLowerStarAdjunction_homEquiv_adicUpperStarUnitIso_hom_hom,
      fieldUpperStarLowerStarAdjunction_homEquiv_fieldUpperStarUnitIso_hom_hom,
      fieldExtendScalarsToAdicAdjunction_homEquiv_fieldExtendScalarsToAdicUnitIso_hom_hom]
    exact fieldConstantSheafToRestrictScalars_comp_map he g

/-- The identification `ℚ̄_ℓ ⊗_Λ Λ_Y ≅ ℚ̄_ℓ,Y` is compatible with the identifications
`(g⁻¹)_* Λ_Y ≅ Λ_X` and `(g⁻¹)_* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X` along an isomorphism `g : X ≅ Y`. -/
lemma adicLowerStar_map_fieldExtendScalarsToAdicUnitIso_hom_comp {X Y : Scheme.{u}}
    (g : X ≅ Y) :
    (g.inv)_*ᵃ[l].map (fieldExtendScalarsToAdicUnitIso he hc Y).hom ≫
        (adicLowerStarUnitIso l g.symm).hom =
      (((adicUpperStarIsoLowerStarInv l g).inv.app _ ≫
          (fieldUpperStarCompExtendScalarsToAdicIso he hc g.hom).inv.app _ ≫
            (fieldExtendScalarsToAdic he hc X).map
              ((fieldUpperStarIsoLowerStarInv Λ g).hom.app (FieldSheaf.unit Λ Y))) ≫
        (fieldExtendScalarsToAdic he hc X).map (fieldLowerStarUnitIso Λ g.symm).hom) ≫
          (fieldExtendScalarsToAdicUnitIso he hc X).hom := by
  simp only [Category.assoc]
  rw [(Iso.eq_inv_comp ((adicUpperStarIsoLowerStarInv l g).app _)).2
      (adicUpperStarIsoLowerStarInv_hom_app_unit_comp l g), Iso.app_inv,
    (adicUpperStarIsoLowerStarInv l g).inv.naturality_assoc, ← Functor.map_comp_assoc,
    fieldUpperStarIsoLowerStarInv_hom_app_unit_comp, cancel_epi, ← Iso.app_inv,
    Iso.eq_inv_comp, Iso.app_hom]
  exact fieldUpperStarCompExtendScalarsToAdicIso_hom_app_unit_comp he hc g.hom

omit [IsUltrametricDist Λ] in
/-- Restriction of scalars from `ℚ̄_ℓ` along `e` turns multiplication by `e(c)` into
multiplication by `c`. -/
lemma fieldRestrictScalarsFromAdic_map_smul {X : Scheme.{u}} (c : ULift.{u + 1} Λ)
    (N : AdicSheaf l X) :
    (fieldRestrictScalarsFromAdic he X).map (AdicSheaf.smul (fieldToAdicRingHom.{u} e c) N) =
      FieldSheaf.smul c ((fieldRestrictScalarsFromAdic he X).obj N) :=
  Mod.hom_ext _ _ (by ext : 3; rfl)

omit [IsUltrametricDist Λ] in
/-- Extension of scalars to `ℚ̄_ℓ` along `e` turns multiplication by `c` into multiplication by
`e(c)`. -/
lemma fieldExtendScalarsToAdic_map_smul {X : Scheme.{u}} (c : ULift.{u + 1} Λ)
    (M : FieldSheaf Λ X) :
    (fieldExtendScalarsToAdic he hc X).map (FieldSheaf.smul c M) =
      AdicSheaf.smul (fieldToAdicRingHom.{u} e c) ((fieldExtendScalarsToAdic he hc X).obj M) := by
  apply ((fieldExtendScalarsToAdicAdjunction he hc X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, fieldRestrictScalarsFromAdic_map_smul]
  exact ((fieldExtendScalarsToAdicAdjunction he hc X).unit.naturality _).symm.trans
    (FieldSheaf.smul_comp c _)

end ExtendScalarsToAdic

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open ProEtale


namespace ProEtaleFieldWeilSheaf

section ConstantTwist

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]

/-- The constant twist `K ⊗ 𝓑_b` of a pro-étale `Λ`-Weil sheaf by a unit `b` of `Λ`: the same
sheaf, with its Weil structure multiplied by `b`. -/
noncomputable def constantTwist (K : ProEtaleFieldWeilSheaf k₀ Λ X) (b : Λˣ) :
    ProEtaleFieldWeilSheaf k₀ Λ X :=
  .mk K.carrier (K.str ≪≫ FieldSheaf.smulIso b K.carrier)

omit [IsUltrametricDist Λ] in
lemma constantTwist_obj_str (K : ProEtaleFieldWeilSheaf k₀ Λ X) (b : Λˣ) :
    (K.constantTwist b).obj.str = K.obj.str ≫ FieldSheaf.smul (ULift.up (b : Λ)) K.carrier :=
  rfl

/-- Constant twists of isomorphic pro-étale Weil sheaves are isomorphic. -/
noncomputable def constantTwistMapIso {K K' : ProEtaleFieldWeilSheaf k₀ Λ X} (φ : K ≅ K')
    (b : Λˣ) : K.constantTwist b ≅ K'.constantTwist b :=
  IsoAlgebra.isoMk ((IsoAlgebra.forget _).mapIso φ) (by
    rw [constantTwist_obj_str, constantTwist_obj_str, Functor.mapIso_hom, IsoAlgebra.forget_map,
      φ.hom.hom.h_assoc, Category.assoc, FieldSheaf.smul_comp]
    rfl)

end ConstantTwist

section ExtendScalars

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

lemma extendScalars_obj_obj_str (K : ProEtaleFieldWeilSheaf k₀ Λ X) :
    ((extendScalars he hc k₀ X).obj K).obj.str =
      (fieldExtendScalarsFrobeniusIso he hc k₀ X).hom.app K.carrier ≫
        (fieldExtendScalars he hc _).map K.obj.str :=
  rfl

/-- Extension of scalars along `e` commutes with constant twists: the twist by `b` becomes the
twist by `b' = e(b)`. -/
noncomputable def extendScalarsConstantTwistIso (K : ProEtaleFieldWeilSheaf k₀ Λ X) {b : Λˣ}
    {b' : Λ'ˣ} (hb : Units.map (e : Λ →* Λ') b = b') :
    (extendScalars he hc k₀ X).obj (K.constantTwist b) ≅
      ((extendScalars he hc k₀ X).obj K).constantTwist b' :=
  IsoAlgebra.isoMk (Iso.refl _) (by
    subst hb
    rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      constantTwist_obj_str, extendScalars_obj_obj_str, extendScalars_obj_obj_str,
      constantTwist_obj_str, Functor.map_comp, fieldExtendScalars_map_smul, Category.assoc]
    rfl)

end ExtendScalars

section ExtendScalarsToAdic

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

lemma extendScalarsToAdic_obj_obj_str (K : ProEtaleFieldWeilSheaf k₀ Λ X) :
    ((extendScalarsToAdic he hc k₀ X).obj K).obj.str =
      (fieldExtendScalarsToAdicFrobeniusIso he hc k₀ X).hom.app K.carrier ≫
        (fieldExtendScalarsToAdic he hc _).map K.obj.str :=
  rfl

/-- Extension of scalars to `ℚ̄_ℓ` along `e` commutes with constant twists: the twist by `b`
becomes the twist by `b' = e(b)`. -/
noncomputable def extendScalarsToAdicConstantTwistIso (K : ProEtaleFieldWeilSheaf k₀ Λ X)
    {b : Λˣ} {b' : (PadicAlgCl l)ˣ} (hb : Units.map (e : Λ →* PadicAlgCl l) b = b') :
    (extendScalarsToAdic he hc k₀ X).obj (K.constantTwist b) ≅
      (ProEtaleWeilSheaf.constantTwist k₀ l X b').obj ((extendScalarsToAdic he hc k₀ X).obj K) :=
  IsoAlgebra.isoMk (K' := IsoAlgebra.mk ((extendScalarsToAdic he hc k₀ X).obj K).carrier
      (((extendScalarsToAdic he hc k₀ X).obj K).str ≪≫ WeilCoefficients.smulIso b' _))
    (Iso.refl _) (by
      subst hb
      rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
        ← IsoAlgebra.str_hom (IsoAlgebra.mk _ _), IsoAlgebra.mk_str, Iso.trans_hom,
        IsoAlgebra.str_hom, extendScalarsToAdic_obj_obj_str,
        extendScalarsToAdic_obj_obj_str, constantTwist_obj_str, Functor.map_comp,
        fieldExtendScalarsToAdic_map_smul, Category.assoc]
      rfl) ≪≫
    ProEtaleWeilSheaf.mkConstantTwistIso k₀ l X _ b'

end ExtendScalarsToAdic

end ProEtaleFieldWeilSheaf

namespace FieldWeilSheaf

lemma constant_obj_obj_str {k₀ : Type u} [Field k₀] [Finite k₀] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] (Λ : Type) [NormedField Λ] [IsUltrametricDist Λ] :
    (constant k₀ Λ X).obj.obj.str =
      (fieldLowerStarUnitIso Λ
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).hom :=
  rfl

section ExtendScalars

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

lemma _root_.AlgebraicGeometry.fieldExtendScalarsFrobeniusIso_hom_app
    (M : FieldSheaf Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (fieldExtendScalarsFrobeniusIso he hc k₀ X).hom.app M =
      (fieldUpperStarIsoLowerStarInv Λ'
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app _ ≫
        (fieldUpperStarCompExtendScalarsIso he hc
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).inv.app M ≫
          (fieldExtendScalars he hc _).map ((fieldUpperStarIsoLowerStarInv Λ
            (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.app M) :=
  rfl

/-- The identification `Λ' ⊗_Λ Λ_X̄ ≅ Λ'_X̄` is compatible with the Weil structures. -/
lemma frobeniusPullback_map_fieldExtendScalarsUnitIso_hom_comp_str :
    (frobeniusPullback k₀ Λ' X).map (fieldExtendScalarsUnitIso he hc _).hom ≫
        (constant k₀ Λ' X).obj.obj.str =
      ((ProEtaleFieldWeilSheaf.extendScalars he hc k₀ X).obj (constant k₀ Λ X).obj).obj.str ≫
        (fieldExtendScalarsUnitIso he hc _).hom := by
  rw [ProEtaleFieldWeilSheaf.extendScalars_obj_obj_str, constant_obj_obj_str,
    constant_obj_obj_str, fieldExtendScalarsFrobeniusIso_hom_app]
  exact fieldLowerStar_map_fieldExtendScalarsUnitIso_hom_comp he hc
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso

/-- The extension of scalars `Λ' ⊗_Λ Λ_X` of the constant `Λ`-Weil sheaf is the constant
`Λ'`-Weil sheaf `Λ'_X`, compatibly with the Weil structures. -/
noncomputable def extendScalarsConstantIso :
    (ProEtaleFieldWeilSheaf.extendScalars he hc k₀ X).obj (constant k₀ Λ X).obj ≅
      (constant k₀ Λ' X).obj :=
  IsoAlgebra.isoMk (fieldExtendScalarsUnitIso he hc _)
    (frobeniusPullback_map_fieldExtendScalarsUnitIso_hom_comp_str he hc k₀ X)

end ExtendScalars

section ExtendScalarsToAdic

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

lemma _root_.AlgebraicGeometry.fieldExtendScalarsToAdicFrobeniusIso_hom_app
    (M : FieldSheaf Λ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (fieldExtendScalarsToAdicFrobeniusIso he hc k₀ X).hom.app M =
      (adicUpperStarIsoLowerStarInv l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app _ ≫
        (fieldUpperStarCompExtendScalarsToAdicIso he hc
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).inv.app M ≫
          (fieldExtendScalarsToAdic he hc _).map ((fieldUpperStarIsoLowerStarInv Λ
            (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.app M) :=
  rfl

/-- The identification `ℚ̄_ℓ ⊗_Λ Λ_X̄ ≅ ℚ̄_ℓ,X̄` is compatible with the Weil structures. -/
lemma frobeniusPullback_map_fieldExtendScalarsToAdicUnitIso_hom_comp_str :
    (WeilSheaf.frobeniusPullback k₀ l X).map (fieldExtendScalarsToAdicUnitIso he hc _).hom ≫
        (ProEtaleWeilSheaf.adicConstant k₀ l X).obj.str =
      ((ProEtaleFieldWeilSheaf.extendScalarsToAdic he hc k₀ X).obj
          (constant k₀ Λ X).obj).obj.str ≫
        (fieldExtendScalarsToAdicUnitIso he hc _).hom := by
  rw [ProEtaleFieldWeilSheaf.extendScalarsToAdic_obj_obj_str, constant_obj_obj_str,
    fieldExtendScalarsToAdicFrobeniusIso_hom_app]
  exact adicLowerStar_map_fieldExtendScalarsToAdicUnitIso_hom_comp he hc
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso

/-- The extension of scalars `ℚ̄_ℓ ⊗_Λ Λ_X` of the constant `Λ`-Weil sheaf is the constant
`ℚ̄_ℓ`-Weil sheaf, compatibly with the Weil structures. -/
noncomputable def extendScalarsToAdicConstantIso :
    (ProEtaleFieldWeilSheaf.extendScalarsToAdic he hc k₀ X).obj (constant k₀ Λ X).obj ≅
      ProEtaleWeilSheaf.adicConstant k₀ l X :=
  IsoAlgebra.isoMk (fieldExtendScalarsToAdicUnitIso he hc _)
    (frobeniusPullback_map_fieldExtendScalarsToAdicUnitIso_hom_comp_str he hc k₀ X)

end ExtendScalarsToAdic

section TateTwist

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [Fact (ringChar k₀ ≠ l)]

/-- The inclusion `E ⊆ F` of subfields of `ℚ̄_ℓ` is a `ℚ_ℓ`-algebra map, so it sends the image
in `Eˣ` of a unit of `ℤ_ℓ` to its image in `Fˣ`. -/
lemma _root_.PadicAlgCl.units_map_inclusion_units_map_zpow
    {E F : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : E ≤ F) (x : ℤ_[l]ˣ) (m : ℤ) :
    Units.map (IntermediateField.inclusion h : E →* F)
        (Units.map ((algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom).toMonoidHom x ^ m) =
      Units.map ((algebraMap ℚ_[l] F).comp PadicInt.Coe.ringHom).toMonoidHom x ^ m := by
  rw [map_zpow, ← MonoidHom.comp_apply, ← Units.map_comp]
  rfl

/-- Blueprint `proposition-weights-under-usual-operations--13`: the Tate twist commutes with finite
scalar extension.

For finite extensions `E ⊆ F` of `ℚ_ℓ` inside `ℚ̄_ℓ` and `m ∈ ℤ`, the extension of scalars
`F ⊗_E E_X(m)` of the Tate twisted constant `E`-Weil sheaf is `F_X(m)`, compatibly with the
Weil structures: `F ⊗_E E_X ≅ F_X` (`AlgebraicGeometry.FieldWeilSheaf.extendScalarsConstantIso`),
and the inclusion `E → F`, a `ℚ_ℓ`-algebra map, sends the cyclotomic unit `χ_ℓ(σ)ᵐ` of `E` to
that of `F`. -/
noncomputable def extendScalarsTateTwistConstantIso {E F : FiniteIntermediateField l}
    (h : E ≤ F) (m : ℤ) :
    (ProEtaleFieldWeilSheaf.extendScalars (continuous_inclusion_finiteIntermediateField h)
        (continuous_algebraMap_intermediateField E.1) k₀ X).obj
        (tateTwistConstant k₀ X E.1 m).obj ≅
      (tateTwistConstant k₀ X F.1 m).obj :=
  ProEtaleFieldWeilSheaf.extendScalarsConstantTwistIso _ _ k₀ X _
      (units_map_inclusion_units_map_zpow (show E.1 ≤ F.1 from h) _ m) ≪≫
    ProEtaleFieldWeilSheaf.constantTwistMapIso (extendScalarsConstantIso _ _ k₀ X) _


/-- The inclusion `E ⊆ ℚ̄_ℓ` is a `ℚ_ℓ`-algebra map, so it sends the image in `Eˣ` of a unit of
`ℤ_ℓ` to its image in `ℚ̄_ℓˣ`. -/
lemma _root_.PadicAlgCl.units_map_val_units_map_zpow (E : IntermediateField ℚ_[l] (PadicAlgCl l))
    (x : ℤ_[l]ˣ) (m : ℤ) :
    Units.map (E.val : E →* PadicAlgCl l)
        (Units.map ((algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom).toMonoidHom x ^ m) =
      Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
        x ^ m := by
  rw [map_zpow, ← MonoidHom.comp_apply, ← Units.map_comp]
  rfl

/-- Blueprint `proposition-weights-under-usual-operations--13`: the Tate twist commutes with scalar
extension to `ℚ̄_ℓ`.

For a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and `m ∈ ℤ`, the extension of scalars
`ℚ̄_ℓ ⊗_E E_X(m)` of the Tate twisted constant `E`-Weil sheaf is the Tate sheaf `ℚ̄_ℓ(m)`,
compatibly with the Weil structures: `ℚ̄_ℓ ⊗_E E_X ≅ ℚ̄_ℓ`
(`AlgebraicGeometry.FieldWeilSheaf.extendScalarsToAdicConstantIso`), the inclusion `E → ℚ̄_ℓ`
sends the cyclotomic unit of `E` to `χ_ℓ(σ)` (`AlgebraicGeometry.WeilSheaf.cyclotomicUnit`), and
`ℚ̄_ℓ(m) ≅ ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ}` (`AlgebraicGeometry.WeilSheaf.tateTwistSheafObjIso`). -/
noncomputable def extendScalarsToAdicTateTwistConstantIso
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E] (m : ℤ) :
    (ProEtaleFieldWeilSheaf.extendScalarsToAdic (e := E.val) continuous_subtype_val
        (continuous_algebraMap_intermediateField E) k₀ X).obj
        (tateTwistConstant k₀ X E m).obj ≅
      (WeilSheaf.tateTwistSheaf k₀ l X m).obj :=
  ProEtaleFieldWeilSheaf.extendScalarsToAdicConstantTwistIso _ _ k₀ X _
      (units_map_val_units_map_zpow E _ m) ≪≫
    (ProEtaleWeilSheaf.constantTwist k₀ l X _).mapIso
      (extendScalarsToAdicConstantIso _ _ k₀ X) ≪≫
    (WeilSheaf.tateTwistSheafObjIso k₀ l X m).symm

end TateTwist

end FieldWeilSheaf

end AlgebraicGeometry
