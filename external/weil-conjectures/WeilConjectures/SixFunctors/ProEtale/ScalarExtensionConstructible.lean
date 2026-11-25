/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ExtendScalars
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-!
# Extension of scalars of flat constructible étale sheaves

For a ring morphism `φ : R →+* S`, extension of scalars `S ⊗_R -` of étale sheaves of modules
(`AlgebraicGeometry.ProEtale.etaleSheafExtendScalars`) commutes with stalks, with pullbacks and
with constant sheaves, as the corresponding statements for the right adjoints are clear. Hence it
sends flat sheaves to flat sheaves, checked on stalks, and it sends finite
locally constant, resp. constructible, sheaves to finite locally constant, resp. constructible,
sheaves, with the same trivialising cover, resp. stratification.

## Main results

- `AlgebraicGeometry.ProEtale.flat_etaleSheafExtendScalars_obj`: extension of scalars preserves
  flat étale sheaves.
- `AlgebraicGeometry.ProEtale.isConstructibleSheaf_etaleSheafExtendScalars_obj`: extension of
  scalars preserves constructible étale sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)

section

variable (X : Scheme.{u})

/-- Restriction of scalars of étale sheaves is additive. -/
instance additive_sheafComposeRestrictScalars_smallEtaleTopology :
    (sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ)).Additive where
  map_add {F G a b} := by
    ext U x
    rfl

/-- Extension of scalars of étale sheaves is additive, being a left adjoint. -/
instance additive_etaleSheafExtendScalars : (etaleSheafExtendScalars φ X).Additive :=
  (etaleSheafExtendScalarsAdjunction φ X).left_adjoint_additive

/-- The stalks of `S ⊗_R F` are the extensions of scalars of the stalks of `F`: sheafification
does not change stalks, and taking stalks commutes with the left adjoint `S ⊗_R -`. -/
noncomputable def etaleSheafExtendScalarsCompSheafFiberIso
    (P : X.smallEtaleTopology.Point.{u + 1}) :
    etaleSheafExtendScalars φ X ⋙ P.sheafFiber ≅
      P.sheafFiber ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ :=
  -- Mathlib's instance is stated for `extendScalars.{u₁, u₂, max u₂ w}`, and unifying
  -- `u + 1 =?= max (u + 1) ?w` gets stuck
  haveI := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  Functor.isoWhiskerLeft (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))
    (P.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (P.presheafFiberCompIso (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))

/-- Extension of scalars of étale sheaves sends constant sheaves to constant sheaves: both
functors are left adjoint to taking global sections viewed as an `R`-module. -/
noncomputable def constantSheafCompEtaleSheafExtendScalarsIso :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙ etaleSheafExtendScalars φ X ≅
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ ⋙
        constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S) :=
  ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R) terminalIsTerminal).comp
    (etaleSheafExtendScalarsAdjunction φ X)).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).comp
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} S)
        terminalIsTerminal)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

end

variable {X Y : Scheme.{u}}

/-- Extension of scalars of étale sheaves commutes with pullback, `g^*(S ⊗_R F) ≅ S ⊗_R g^* F`:
both functors are left adjoint to `G ↦ g_* G` viewed as a sheaf of `R`-modules. -/
noncomputable def etaleSheafExtendScalarsCompUpperStarIso (g : Y ⟶ X) :
    etaleSheafExtendScalars φ X ⋙ Etale.upperStar (ModuleCat.{u + 1} S) g ≅
      Etale.upperStar (ModuleCat.{u + 1} R) g ⋙ etaleSheafExtendScalars φ Y :=
  ((etaleSheafExtendScalarsAdjunction φ X).comp
      (Etale.upperStarLowerStarAdjunction _ g)).leftAdjointUniq
    (((Etale.upperStarLowerStarAdjunction _ g).comp
      (etaleSheafExtendScalarsAdjunction φ Y)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

variable {φ} in
/-- Extension of scalars of étale sheaves preserves flatness: the stalks of `S ⊗_R F` are the
extensions of scalars `S ⊗_R F_s` of the stalks of `F`. -/
theorem flat_etaleSheafExtendScalars_obj {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (hF : ObjectProperty.flat F) : ObjectProperty.flat ((etaleSheafExtendScalars φ X).obj F) := by
  rw [Etale.flat_iff_forall_flat_sheafFiber_obj] at hF ⊢
  intro Ω _ _ s
  have := (ModuleCat.flat_iff_flat _).1 (hF s)
  have := ModuleCat.flat_extendScalars_obj φ ((pointSmallEtale s).ulift.{u + 1}.sheafFiber.obj F)
  exact ObjectProperty.prop_of_iso _
    ((etaleSheafExtendScalarsCompSheafFiberIso φ X _).app F).symm
    ((ModuleCat.flat_iff_flat _).2 this)

/-- Extension of scalars of étale sheaves preserves finite sheaves: the stalks of `S ⊗_R F` are
the extensions of scalars `S ⊗_R F_s` of the stalks of `F`. -/
theorem isFiniteSheaf_etaleSheafExtendScalars_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [hF : IsFiniteSheaf F] :
    IsFiniteSheaf ((etaleSheafExtendScalars φ X).obj F) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let Φ := (pointSmallEtale s).ulift.{u + 1}
    have h := hF.isFinitelyGenerated_sheafFiber Ω s
    rw [← ConcreteCategory.isFinitelyGenerated_iff_of_iso
      (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} _).app F),
      ModuleCat.isFinitelyGenerated_iff] at h
    have := ModuleCat.finite_extendScalars_obj' φ (Φ.sheafFiber.obj F)
    exact ((ModuleCat.isFinitelyGenerated_iff _).2 this).of_iso
      (((etaleSheafExtendScalarsCompSheafFiberIso φ X Φ).app F).symm ≪≫
        ((pointSmallEtale s).uliftSheafFiberIso.{u + 1} _).app _)

/-- Extension of scalars of étale sheaves preserves locally constant sheaves, trivialised by the
same cover: it commutes with pullbacks and sends constant sheaves to constant sheaves. -/
instance isLocallyConstantSheaf_etaleSheafExtendScalars_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [h : IsLocallyConstantSheaf F] :
    IsLocallyConstantSheaf ((etaleSheafExtendScalars φ X).obj F) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := h.nonempty_locallyConstantDatum
  refine ⟨⟨⟨𝒰, fun i ↦ ?_⟩⟩⟩
  have := h𝒰 i
  rw [isConstant_over_iff_upperStar] at this ⊢
  obtain ⟨M, ⟨e⟩⟩ := this.1
  exact Sheaf.isConstant_of_iso _ ((etaleSheafExtendScalarsCompUpperStarIso φ _).app F ≪≫
    (etaleSheafExtendScalars φ _).mapIso e.symm ≪≫
    (constantSheafCompEtaleSheafExtendScalarsIso φ _).app M)

/-- Extension of scalars of étale sheaves preserves finite locally constant sheaves. -/
instance isFiniteLocallyConstantSheaf_etaleSheafExtendScalars_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheaf ((etaleSheafExtendScalars φ X).obj F) where
  toIsFiniteSheaf := isFiniteSheaf_etaleSheafExtendScalars_obj φ F

/-- Extension of scalars of étale sheaves preserves constructible sheaves, with the same
stratification: it commutes with the pullbacks to the strata. -/
instance isConstructibleSheaf_etaleSheafExtendScalars_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [h : IsConstructibleSheaf F] :
    IsConstructibleSheaf ((etaleSheafExtendScalars φ X).obj F) := by
  obtain ⟨T, hT⟩ := h.exists_stratification
  refine ⟨T, fun i ↦ ?_⟩
  have := hT i
  exact IsFiniteLocallyConstantSheaf.of_iso (F := (etaleSheafExtendScalars φ _).obj
      ((Etale.upperStar _ (T.immersion i)).obj F))
    ((etaleSheafExtendScalarsCompUpperStarIso φ (T.immersion i)).app F).symm

end AlgebraicGeometry.ProEtale
