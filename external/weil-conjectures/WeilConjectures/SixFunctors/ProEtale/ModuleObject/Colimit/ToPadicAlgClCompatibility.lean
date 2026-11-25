/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

/-!

# The extension of scalars `E ⟶ ℚ̄_ℓ` and the operations `f^*`, `g_*`, `j_!`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, and `k` a field of characteristic
`p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`
for the extension of scalars `ℚ̄_ℓ,X ⊗ᴸ_{E_X} -` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleToPadicAlgCl`, the functor
`ProEtale.constructibleToPadicAlgCl` typed on the categories `Dᵇc(X)⟦Λ⟧`). This file gives the
coefficient comparisons of blueprint `proposition-six-operations-change-coefficients` for `E ⟶ ℚ̄_ℓ`
that do not involve `f^!`:

* **(Pull)** on bounded constructible complexes:
  `Lf^*_E ⋙ T_X ≅ T_Y ⋙ Lf^*_{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleUpperStarToPadicAlgClIso`), the restriction of
  `ProEtale.CondensedRing.derivedPullIso`.
* **(Push)** for a proper `g`: the comparison `Rg_*^E ⋙ T_Y ⟶ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClHom`), the restriction of
  `ProEtale.CondensedRing.derivedPushHom`, is an isomorphism at bounded below complexes
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClIso`).
* **(Shriek)** for an open immersion `j`: `j_!^E ⋙ T_X ≅ T_U ⋙ j_!^{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso`), and the
  exchange `j^*_E ⋙ T_U ⟶ T_X ⋙ j^*_{ℚ̄_ℓ}`, an isomorphism
  (`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionUpperStarToPadicAlgCl`).

The exchange for `f^!` is in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility`. This file
does not import the exceptional inverse image, so that the existence of `Rg^!` over `ℚ̄_ℓ`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarTwoColimit`) can use it.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism `G ⋙ L₂ ≅ L₁ ⋙ H` along adjunctions
`L₁ ⊣ R₁` and `L₂ ⊣ R₂` with fully faithful left adjoints is an isomorphism, provided the right
adjoints commute with `G` and `H` up to some natural isomorphism `e : H ⋙ R₂ ≅ R₁ ⋙ G`. Indeed,
at `d`, the mate is the unit of `L₂ ⊣ R₂`, then `R₂` of the isomorphism, then `R₂ H` of the
counit `ε_d` of `L₁ ⊣ R₁`; and `R₂ H ε_d ≅ G R₁ ε_d` (by `e`) is an isomorphism, `R₁ ε_d` being
the inverse of a unit. -/
theorem isIso_mateEquiv_of_isIso_unit [IsIso adj₁.unit] [IsIso adj₂.unit]
    (α : TwoSquare G L₁ L₂ H) [IsIso α] (e : H ⋙ R₂ ≅ R₁ ⋙ G) :
    IsIso (mateEquiv adj₁ adj₂ α) := by
  have (d : B) : IsIso ((mateEquiv adj₁ adj₂ α).app d) := by
    have : IsIso (R₁.map (adj₁.counit.app d)) := by
      have : IsIso (adj₁.unit.app (R₁.obj d) ≫ R₁.map (adj₁.counit.app d)) := by
        rw [adj₁.right_triangle_components]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left (adj₁.unit.app (R₁.obj d)) _
    have : IsIso ((H ⋙ R₂).map (adj₁.counit.app d)) :=
      (NatIso.isIso_map_iff e _).mpr (inferInstanceAs (IsIso (G.map (R₁.map _))))
    have : IsIso (R₂.map (H.map (adj₁.counit.app d))) := this
    simp only [mateEquiv_apply, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, rightUnitor_inv_app, leftUnitor_hom_app,
      Functor.comp_map]
    dsimp only [Functor.comp_obj]
    simp only [Category.id_comp]
    have : IsIso (α.app (R₁.obj d)) := inferInstance
    have : IsIso (𝟙 (R₂.obj (H.obj d))) := inferInstance
    exact IsIso.comp_isIso
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section ToPadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The extension of scalars `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` on bounded constructible complexes:
the functor `ProEtale.constructibleToPadicAlgCl`, typed on the categories `Dᵇc(X)⟦Λ⟧` of the six
operations rather than on `ProEtale.PadicSubfieldConstructible` and
`ProEtale.PadicAlgClConstructible`. The two category structures agree only after unfolding their
instances, so the coefficient comparisons below are stated with this functor. -/
noncomputable def boundedConstructibleToPadicAlgCl :
    Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  constructibleToPadicAlgCl X ℓ E

lemma boundedConstructibleToPadicAlgCl_eq :
    boundedConstructibleToPadicAlgCl X ℓ E = constructibleToPadicAlgCl X ℓ E :=
  rfl

/-- The extension of scalars `T_X` on bounded constructible complexes is compatible with the
inclusions. -/
noncomputable def boundedConstructibleToPadicAlgClCompatibility :
    boundedConstructibleToPadicAlgCl X ℓ E ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived extension of scalars is a left adjoint, hence preserves zero morphisms. -/
instance : (derivedExtendScalarsToPadicAlgCl X ℓ E).PreservesZeroMorphisms :=
  have := (Mod.derivedExtendMapDerivedCategoryAdjunction
    (padicSubfieldRingObjToPadicAlgCl X ℓ E)).isLeftAdjoint
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- The extension of scalars `T_X` preserves zero morphisms, as the derived extension of scalars
does. -/
instance : (boundedConstructibleToPadicAlgCl X ℓ E).PreservesZeroMorphisms where
  map_zero A B := (boundedConstructible _).ι.map_injective (by
    have h := (boundedConstructibleToPadicAlgClCompatibility X ℓ E).hom.naturality (0 : A ⟶ B)
    simp only [Functor.comp_map, Functor.map_zero, Limits.comp_zero] at h
    rw [(boundedConstructible _).ι.map_zero]
    exact (cancel_mono _).1 (h.trans (Limits.zero_comp).symm))

end ToPadicAlgCl

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

omit [Fact (ringChar k).Prime] in
/-- A scheme of finite type over a field is a noetherian topological space. -/
lemma noetherianSpace_left_of_over (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : TopologicalSpace.NoetherianSpace X.left := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  infer_instance

/-! ### (Pull) -/

section UpperStar

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- **(Pull)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ`:
`Lf^*_E ⋙ T_X ≅ T_Y ⋙ Lf^*_{ℚ̄_ℓ}`, the restriction of `ProEtale.CondensedRing.derivedPullIso`
along the fully faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarToPadicAlgClIso :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f ⋙
        boundedConstructibleToPadicAlgCl X.left ℓ E ≅
      boundedConstructibleToPadicAlgCl Y.left ℓ E ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleToPadicAlgClCompatibility X.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ ℓ f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleToPadicAlgClCompatibility Y.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility _ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

end UpperStar

/-! ### (Push) for a proper morphism -/

/-- **(Push)** for the inclusion `E ⟶ ℚ̄_ℓ` is an isomorphism at bounded constructible complexes,
for a quasi-compact quasi-separated `g`: these are bounded below
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`). -/
instance isIso_whiskerLeft_ι_derivedPushHom_padicSubfieldRingObjToPadicAlgCl {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g] :
    IsIso (Functor.whiskerLeft
      (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z)).ι
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g)) := by
  have (K : Dᵇc(Z)⟦Profinite.continuousMapRingObj E⟧) : IsIso ((Functor.whiskerLeft
      (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z)).ι
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g)).app K) :=
    have := K.property.1.1.choose_spec
    isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E g K.obj
      K.property.1.1.choose
  exact NatIso.isIso_of_isIso_app _

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- **(Push)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ` and a proper
morphism `g`: the comparison `Rg_*^E ⋙ T_Y ⟶ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`, the restriction of
`ProEtale.CondensedRing.derivedPushHom` along the inclusions of the bounded constructible
complexes. -/
noncomputable def boundedConstructibleLowerStarToPadicAlgClHom :
    ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g ⋙
        boundedConstructibleToPadicAlgCl Y.left ℓ E ⟶
      boundedConstructibleToPadicAlgCl Z.left ℓ E ⋙
        boundedConstructibleLowerStar ℓ g :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimage
    ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (boundedConstructibleToPadicAlgClCompatibility Y.left ℓ E).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility ℓ E g).hom _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _
        (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g.left) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (boundedConstructibleToPadicAlgClCompatibility Z.left ℓ E).inv _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ g).inv ≫
      (Functor.associator _ _ _).inv)

/-- **(Push) is an isomorphism** for `E ⟶ ℚ̄_ℓ` on bounded constructible complexes: these are
bounded below, where `derivedPushHom` is invertible
(`ProEtale.CondensedRing.isIso_whiskerLeft_ι_derivedPushHom_padicSubfieldRingObjToPadicAlgCl`). -/
instance isIso_boundedConstructibleLowerStarToPadicAlgClHom :
    IsIso (boundedConstructibleLowerStarToPadicAlgClHom ℓ E g) :=
  (((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleToPadicAlgClCompatibility Y.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility ℓ E g) _ ≪≫
      Functor.associator _ _ _ ≪≫
      asIso (Functor.whiskerLeft _
        (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g.left)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleToPadicAlgClCompatibility Z.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ g).symm ≪≫
      (Functor.associator _ _ _).symm)).isIso_hom

/-- **(Push)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ` and a proper
morphism `g`: `Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`, the comparison
`boundedConstructibleLowerStarToPadicAlgClHom`, which is an isomorphism. -/
noncomputable def boundedConstructibleLowerStarToPadicAlgClIso :
    ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g ⋙
        boundedConstructibleToPadicAlgCl Y.left ℓ E ≅
      boundedConstructibleToPadicAlgCl Z.left ℓ E ⋙
        boundedConstructibleLowerStar ℓ g :=
  asIso (boundedConstructibleLowerStarToPadicAlgClHom ℓ E g)

end LowerStar

/-! ### (Shriek) for an open immersion -/

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- **(Shriek)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ` and an open
immersion `j`: `j_!^E ⋙ T_X ≅ T_U ⋙ j_!^{ℚ̄_ℓ}`, the restriction of
`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ j ⋙
        boundedConstructibleToPadicAlgCl X.left ℓ E ≅
      boundedConstructibleToPadicAlgCl U.left ℓ E ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleToPadicAlgClCompatibility X.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedOpenImmersionShriekIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) j.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleToPadicAlgClCompatibility U.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The exchange `j^*_E ⋙ T_U ⟶ T_X ⋙ j^*_{ℚ̄_ℓ}` for an open immersion `j`: the mate of the
inverse of (Shriek) under the adjunctions `j_! ⊣ j^*`. -/
noncomputable def boundedConstructibleOpenImmersionUpperStarToPadicAlgCl :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ j ⋙
        boundedConstructibleToPadicAlgCl U.left ℓ E ⟶
      boundedConstructibleToPadicAlgCl X.left ℓ E ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  mateEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E j).inv

/-- The exchange for an open immersion `j` is an isomorphism: `j_!` is fully faithful on both
sides, and `j^*` commutes with the extension of scalars by (Pull)
(`boundedConstructibleUpperStarToPadicAlgClIso`). -/
instance isIso_boundedConstructibleOpenImmersionUpperStarToPadicAlgCl :
    IsIso (boundedConstructibleOpenImmersionUpperStarToPadicAlgCl ℓ E j) :=
  isIso_mateEquiv_of_isIso_unit _ _ _ (boundedConstructibleUpperStarToPadicAlgClIso ℓ E j).symm

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing
