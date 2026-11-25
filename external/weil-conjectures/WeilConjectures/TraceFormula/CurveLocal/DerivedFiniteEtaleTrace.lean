/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.CategoryTheory.Linear.FunctorCategory
import WeilConjectures.CategoryTheory.Sites.Point.Linear
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceData

/-!
# The finite étale trace on derived global sections

Let `π : Y' ⟶ Y` be a finite étale morphism of schemes all of whose geometric fibres have `d`
points, and `Λ` a commutative ring. For a complex `M` of étale sheaves of `Λ`-modules on `Y`, the
pullback `RΓ(Y, M) ⟶ RΓ(Y', π^* M)` of derived global sections
(`CategoryTheory.Functor.rightDerivedPullback` along `π^*` and
`AlgebraicGeometry.Etale.ΓPullback`) admits a trace `RΓ(Y', π^* M) ⟶ RΓ(Y, M)` such that the
composite is multiplication by `d` (blueprint `lemma-descent-vanishing-finite-etale`).

The trace is `RΓ(Y', π^* M) ⟶ RΓ(Y, π_* π^* M) ⟶ RΓ(Y, M)`: the pullback map of derived global
sections along the exact functor `π_*`, followed by the counit `π_* π^* ⟶ 𝟭` of `π_* ⊣ π^*`. The
composite of the two pullback maps is the pullback map along `π^* ⋙ π_*` for the unit
`Γ ⟶ Γ ∘ π_* π^*` (`CategoryTheory.Functor.rightDerivedPullback_comp`), and the unit followed by
the counit is multiplication by `d` on sheaves.

## Main statements

- `CategoryTheory.Functor.rightDerivedPullback_app_comp_map_mapDerivedCategoryToId_app`: if
  `α : F ⟶ P ⋙ F` followed by `F(τ)` for `τ : P ⟶ 𝟭` is multiplication by `n`, so is the induced
  map of right derived functors.
- `AlgebraicGeometry.Etale.unit_app_comp_lowerStarUpperStarAdjunctionOfIsFinite_counit_app`: the
  unit of `π^* ⊣ π_*` followed by the counit of `π_* ⊣ π^*` is multiplication by `d`.
- `AlgebraicGeometry.Etale.exists_rightDerivedPullback_app_comp_eq_smul`: the finite étale trace
  on derived global sections, with the bounded below variant
  `AlgebraicGeometry.Etale.exists_sectionsWithSupportTrianglePullback_app_hom₂_comp_eq_smul`
  stated for the middle term of `AlgebraicGeometry.Etale.sectionsWithSupportTrianglePullback`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite DerivedCategory

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

namespace Functor

variable {P : C ⥤ C} [P.Additive]

/-- The morphism of cochain complexes `P(K) ⟶ K` induced by a natural transformation
`τ : P ⟶ 𝟭 C`, natural in `K`. -/
noncomputable def mapHomologicalComplexToId (τ : P ⟶ 𝟭 C) :
    P.mapHomologicalComplex (ComplexShape.up ℤ) ⟶ 𝟭 _ where
  app K :=
    { f m := τ.app (K.X m)
      comm' i j _ := (τ.naturality (K.d i j)).symm }
  naturality K L φ := by
    ext m
    exact τ.naturality (φ.f m)

@[simp]
lemma mapHomologicalComplexToId_app_f (τ : P ⟶ 𝟭 C) (K : CochainComplex C ℤ) (m : ℤ) :
    ((mapHomologicalComplexToId τ).app K).f m = τ.app (K.X m) :=
  rfl

variable [HasDerivedCategory C] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

variable (P) in
/-- The natural transformation `D(P) ⟶ 𝟭` induced by a natural transformation
`τ : P ⟶ 𝟭 C` from an exact functor `P` to the identity. -/
noncomputable def mapDerivedCategoryToId (τ : P ⟶ 𝟭 C) : P.mapDerivedCategory ⟶ 𝟭 _ :=
  Localization.liftNatTrans Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q) Q P.mapDerivedCategory (𝟭 _)
    (whiskerRight (mapHomologicalComplexToId τ) Q ≫ Q.leftUnitor.hom)

lemma mapDerivedCategoryFactors_inv_app_comp_mapDerivedCategoryToId_app (τ : P ⟶ 𝟭 C)
    (K : CochainComplex C ℤ) :
    P.mapDerivedCategoryFactors.inv.app K ≫ (mapDerivedCategoryToId P τ).app (Q.obj K) =
      Q.map ((mapHomologicalComplexToId τ).app K) := by
  have hP : Localization.Lifting.iso Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q)
      P.mapDerivedCategory = P.mapDerivedCategoryFactors := rfl
  simp [mapDerivedCategoryToId, Localization.liftNatTrans_app, hP]

variable [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C] {F : C ⥤ D} [F.Additive]

/-- If `α : F ⟶ P ⋙ F` followed by `F(τ)` is multiplication by an integer `n`, then so is the
pullback map `RF ⟶ RF ∘ D(P)` followed by `RF(D(τ))`. -/
lemma rightDerivedPullback_app_comp_map_mapDerivedCategoryToId_app (α : F ⟶ P ⋙ F)
    (τ : P ⟶ 𝟭 C) (n : ℤ) (h : α ≫ whiskerRight τ F = n • 𝟙 F)
    (M : DerivedCategory C) :
    (rightDerivedPullback P α).app M ≫
        F.rightDerivedFunctor.map ((mapDerivedCategoryToId P τ).app M) = n • 𝟙 _ := by
  have := rightDerivedFunctor_hom_ext
    (rightDerivedPullback P α ≫ whiskerRight (mapDerivedCategoryToId P τ) _)
    (n • 𝟙 F.rightDerivedFunctor) (fun K ↦ by
      have hK : (NatTrans.mapHomologicalComplex α _).app K ≫
          (F.mapHomologicalComplex _).map ((mapHomologicalComplexToId τ).app K) =
            n • 𝟙 _ := by
        ext m
        simp only [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f]
        exact congr_app h (K.X m)
      simp only [NatTrans.comp_app, whiskerRight_app, NatTrans.app_zsmul, NatTrans.id_app]
      rw [rightDerivedFunctorUnitQ_rightDerivedPullback_app'_assoc, ← Functor.map_comp,
        mapDerivedCategoryFactors_inv_app_comp_mapDerivedCategoryToId_app]
      erw [← rightDerivedFunctorUnitQ_naturality F ((mapHomologicalComplexToId τ).app K)]
      erw [← Q.map_comp_assoc, hK]
      simp)
  simpa using congr_app this M

end Functor

namespace Sheaf

/-- On a site with a terminal object `T`, the identification of the global sections with the
sections over `T` is the restriction map. -/
lemma ΓNatIsoSheafSections_hom_app_eq_ΓRes {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] {T : C} (hT : IsTerminal T) (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  erw [Equiv.symm_trans_apply, Equiv.symm_symm, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

end Sheaf

end CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

section GlobalSections

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X X' : Scheme.{u}} (e : X' ⟶ X)

/-- The pullback of global sections `Γ(X, F) ⟶ Γ(X', e^* F)`, followed by the identification
`Γ(X', e^* F) ≅ Γ(X, e_* e^* F)`, is the map induced on global sections by the unit
`F ⟶ e_* e^* F`. -/
@[reassoc]
lemma ΓPullback_app_comp_lowerStarCompGlobalSectionsIso_inv_app
    (F : Sheaf X.smallEtaleTopology A) :
    (ΓPullback A e).app F ≫ (lowerStarCompGlobalSectionsIso A e).inv.app ((e)^*[A].obj F) =
      (Sheaf.Γ _ A).map ((upperStarLowerStarAdjunction A e).unit.app F) := by
  have := isIso_terminal_hom X
  rw [← cancel_mono ((lowerStarCompGlobalSectionsIso A e).hom.app _), assoc, Iso.inv_hom_id_app,
    ← cancel_mono ((Sheaf.ΓNatIsoSheafSections _ A terminalIsTerminal).hom.app
    ((e)^*[A].obj F))]
  have h := ΓPullback_app_comp_ΓRes A e (V := ⊤_ X.Etale) (W := ⊤_ X'.Etale)
    ((⊤_ X'.Etale).hom ≫ e ≫ inv (⊤_ X.Etale).hom) (by simp) F
  erw [comp_id]
  rw [Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes, h]
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, assoc]
  rw [← Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes _ _ terminalIsTerminal ((e)^*[A].obj F),
    Iso.inv_hom_id_app]
  erw [(Sheaf.ΓNatIsoSheafSections _ A terminalIsTerminal).hom.naturality_assoc]
  rw [Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes, sectionsPullback_app]
  congr 1
  simp only [Category.comp_id]
  congr 1
  let P := PreservesTerminal.iso e.Etale
  have h₃ : (lowerStarCompSheafSectionsTerminalIso A e).hom.app ((e)^*[A].obj F) =
      ((e)^*[A].obj F).obj.map P.inv.op := rfl
  rw [h₃]
  congr 2
  exact (cancel_mono P.hom).1 (terminal.hom_ext _ _)

end GlobalSections


section DerivedTrace

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {Λ : Type (u + 1)} [CommRing Λ] {Y Y' : Scheme.{u}} (π : Y' ⟶ Y) [IsFinite π]
  [Etale π] (d : ℕ)

/-- **The finite étale trace on derived global sections** (blueprint
`lemma-descent-vanishing-finite-etale`): for a finite étale `π : Y' ⟶ Y` all of whose
geometric fibres have `d` points, the pullback `RΓ(Y, M) ⟶ RΓ(Y', π^* M)` of derived global
sections admits a trace `RΓ(Y', π^* M) ⟶ RΓ(Y, M)` whose composite with it is multiplication by
`d`. -/
theorem exists_rightDerivedPullback_app_comp_eq_smul
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nat.card (π.GeometricFiber s) = d)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ t, (Functor.rightDerivedPullback (π)^*[ModuleCat.{u + 1} Λ]
        (ΓPullback (ModuleCat.{u + 1} Λ) π)).app M ≫ t = (d : ℤ) • 𝟙 _ := by
  let A := ModuleCat.{u + 1} Λ
  have : PreservesLimitsOfSize.{0, 0} (π)_*[A] :=
    (upperStarLowerStarAdjunction A π).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (π)_*[A] := PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  have : PreservesColimitsOfSize.{0, 0} (π)_*[A] :=
    (lowerStarUpperStarAdjunctionOfIsFinite A π).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (π)_*[A] :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _
  let τ := (lowerStarUpperStarAdjunctionOfIsFinite A π).counit
  let α := (lowerStarCompGlobalSectionsIso A π).inv
  have hτ : (ΓPullback A π ≫ Functor.whiskerLeft _ α) ≫
      Functor.whiskerRight τ (Sheaf.Γ _ A) = (d : ℤ) • 𝟙 _ := by
    refine NatTrans.ext (funext fun G ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, assoc, α,
      ΓPullback_app_comp_lowerStarCompGlobalSectionsIso_inv_app_assoc, ← Functor.map_comp,
      τ]
    rw [unit_app_comp_lowerStarUpperStarAdjunctionOfIsFinite_counit_app Λ π G d hdeg,
      Nat.cast_smul_eq_nsmul, Functor.map_nsmul, CategoryTheory.Functor.map_id,
      NatTrans.app_zsmul, NatTrans.id_app, natCast_zsmul]
  have hcomp := Functor.rightDerivedPullback_comp (π)^*[A] (π)_*[A] ((π)^*[A] ⋙ (π)_*[A])
    (Iso.refl _) (ΓPullback A π) α (ΓPullback A π ≫ Functor.whiskerLeft _ α) (by simp) M
  refine ⟨(Functor.rightDerivedPullback (π)_*[A] α).app _ ≫
    (Sheaf.Γ _ A).rightDerivedFunctor.map ((Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).inv.app M ≫
        (Functor.mapDerivedCategoryToId _ τ).app M), ?_⟩
  rw [← assoc, ← hcomp, assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  exact Functor.rightDerivedPullback_app_comp_map_mapDerivedCategoryToId_app _ τ d hτ M

/-- The bounded below version of
`AlgebraicGeometry.Etale.exists_rightDerivedPullback_app_comp_eq_smul`. -/
theorem exists_rightDerivedPullback_app_obj_comp_eq_smul
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nat.card (π.GeometricFiber s) = d)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ t : (Sheaf.Γ Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj
        ((Functor.mapDerivedCategoryPlus (π)^*[ModuleCat.{u + 1} Λ]).obj M).obj ⟶
          (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj M.obj,
      (Functor.rightDerivedPullback (π)^*[ModuleCat.{u + 1} Λ]
        (ΓPullback (ModuleCat.{u + 1} Λ) π)).app M.obj ≫ t = (d : ℤ) • 𝟙 _ :=
  exists_rightDerivedPullback_app_comp_eq_smul π d hdeg M.obj

/-- The finite étale trace on the middle term of the morphism of localization triangles
`AlgebraicGeometry.Etale.sectionsWithSupportTrianglePullback`: the pullback
`RΓ(Y, M) ⟶ RΓ(Y', π^* M)` composed with the trace is multiplication by the degree `d`. -/
theorem exists_sectionsWithSupportTrianglePullback_app_hom₂_comp_eq_smul
    {Z Z' : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (i' : Z' ⟶ Y')
    [IsClosedImmersion i'] (h : i'.openComplement ≤ π ⁻¹ᵁ i.openComplement)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nat.card (π.GeometricFiber s) = d)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ t, ((sectionsWithSupportTrianglePullback (ModuleCat.{u + 1} Λ) π i i' h).app M).hom₂ ≫
      t = (d : ℤ) • 𝟙 _ :=
  exists_rightDerivedPullback_app_obj_comp_eq_smul π d hdeg M

end DerivedTrace

section Pair

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X X' Z Z' : Scheme.{u}} (e : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
  (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : i'.openComplement ≤ e ⁻¹ᵁ i.openComplement)

/-- The middle component of the morphism of localization triangles
`AlgebraicGeometry.Etale.sectionsWithSupportTrianglePullback` is the pullback
`RΓ(X, K) ⟶ RΓ(X', e^* K)` of derived global sections. -/
lemma sectionsWithSupportTrianglePullback_app_hom₂
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ((sectionsWithSupportTrianglePullback A e i i' h).app K).hom₂ =
      (Functor.rightDerivedPullback (e)^*[A] (ΓPullback A e)).app K.obj :=
  rfl

end Pair

end AlgebraicGeometry.Etale

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [HasDerivedCategory C]
  [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]

lemma rightDerivedFunctorNatTrans_id (F : C ⥤ D) [F.Additive] :
    rightDerivedFunctorNatTrans (𝟙 F) = 𝟙 _ := by
  simp only [rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_id,
    Functor.whiskerRight_id', rightDerivedNatTrans_id]


end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {Y Y' : Scheme.{u}} (π : Y' ⟶ Y) [IsFinite π]
  [Etale π] (d : ℕ)

/-- **The finite étale trace on the restriction of derived sections** (blueprint
`lemma-descent-vanishing-finite-etale`): for a finite étale `π : Y' ⟶ Y` all of whose geometric
fibres have `d` points, the restriction `RΓ(Y, M) ⟶ RΓ(Y', π^* M)` of derived sections over the
terminal étale schemes, followed by a trace, is multiplication by `d`. -/
theorem exists_sectionsRestriction_app_comp_eq_smul
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nat.card (π.GeometricFiber s) = d)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ t, (sectionsRestriction _ π (V := Scheme.Etale.mk (𝟙 Y)) (W := Scheme.Etale.mk (𝟙 Y'))
      π rfl).app M ≫ t = (d : ℤ) • 𝟙 _ := by
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨t, ht⟩ := exists_rightDerivedPullback_app_comp_eq_smul π d hdeg M
  let τ := Sheaf.natTransΓRes Y.smallEtaleTopology A (op (Scheme.Etale.mk (𝟙 Y)))
  let τ' := Sheaf.natTransΓRes Y'.smallEtaleTopology A (op (Scheme.Etale.mk (𝟙 Y')))
  have hc := congr_app (Functor.rightDerivedFunctorNatTrans_comp_rightDerivedPullback (π)^*[A]
    τ τ' (ΓPullback A π) (sectionsPullback A π (V := Scheme.Etale.mk (𝟙 Y))
      (W := Scheme.Etale.mk (𝟙 Y')) π rfl) (by
        refine NatTrans.ext (funext fun F ↦ ?_)
        exact (ΓPullback_app_comp_ΓRes A π (V := Scheme.Etale.mk (𝟙 Y))
          (W := Scheme.Etale.mk (𝟙 Y')) π rfl F).symm)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hc
  refine ⟨inv ((Functor.rightDerivedFunctorNatTrans τ').app ((π)^*[A].mapDerivedCategory.obj M)) ≫
    t ≫ (Functor.rightDerivedFunctorNatTrans τ).app M, ?_⟩
  change (sectionsRestriction A π (V := Scheme.Etale.mk (𝟙 Y)) (W := Scheme.Etale.mk (𝟙 Y'))
    π rfl).app M ≫ _ = _
  rw [← cancel_epi ((Functor.rightDerivedFunctorNatTrans τ).app M)]
  simp only [sectionsRestriction] at hc ⊢
  rw [reassoc_of% hc, IsIso.hom_inv_id_assoc, reassoc_of% ht, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Etale
