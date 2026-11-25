/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeConjugate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Checking that a morphism out of an extension of scalars is invertible on a pro-étale cover

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, `S` a scheme, `K` a module object
over `Λ_S`, `L` one over `Λ'_S` and `φ : K ⟶ Res L` a `Λ_S`-linear map, with adjoint
`φ♯ : Λ'_S ⊗_{Λ_S} K ⟶ L`. Then:

* the pullbacks of module objects along the members of a pro-étale cover are jointly
  conservative (`ProEtale.CondensedRing.isIso_of_isIso_upperStar_map_of_cover`);
* the pullback of `φ♯` along `f` is, through the (Pull) isomorphism
  `f^* (Λ'_S ⊗ K) ≅ Λ'_Y ⊗ f^* K`, the adjoint of `f^* φ` followed by `f^* Res L ≅ Res f^* L`
  (`ProEtale.CondensedRing.pullIso_hom_app_comp_upperStar_map_homEquiv_symm`);
* hence `φ♯` is invertible as soon as all these adjoints are, for a pro-étale cover
  (`ProEtale.CondensedRing.isIso_homEquiv_symm_of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Conservative

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Pullbacks of module objects along a pro-étale cover are jointly conservative.** -/
theorem isIso_of_isIso_upperStar_map_of_cover {S : Scheme.{u}}
    {N N' : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)} (g : N ⟶ N')
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (h : ∀ i, IsIso ((𝒰.f i)^*⟦Λ⟧.map g)) : IsIso g := by
  have hw (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  have : IsIso g.hom := by
    refine ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1} g.hom 𝒰.f 𝒰.mem₀
      fun i ↦ ?_
    have h₁ : IsIso ((Mod.forget _).map ((𝒰.f i)^*⟦Λ⟧.map g)) := inferInstance
    have h₂ := (NatIso.isIso_map_iff (upperStarForgetIso Λ (𝒰.f i)) g).2 h₁
    exact (NatIso.isIso_map_iff
      (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) inferInstance) g.hom).1 h₂
  have : IsIso ((Mod.forget _).map g) := this
  exact isIso_of_reflects_iso g (Mod.forget _)

end Conservative

section Adjoint

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The pullback of the adjoint `Λ'_S ⊗ K ⟶ L` of `φ : K ⟶ Res L` is, through (Pull), the adjoint
of `f^* φ` followed by `f^* Res L ≅ Res f^* L`. -/
lemma pullIso_hom_app_comp_upperStar_map_homEquiv_symm {X S : Scheme.{u}} (f : X ⟶ S)
    {K : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)}
    (φ : K ⟶ (Mod.comap (coefficientMap a S)).obj L) :
    (pullIso a f).hom.app K ≫ (f)^*⟦Λ'⟧.map
        (((Mod.extendRestrictAdjunction (coefficientMap a S)).homEquiv _ _).symm φ) =
      ((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv _ _).symm
        ((f)^*⟦Λ⟧.map φ ≫ (comapUpperStarIso a f).inv.app L) := by
  set adj₁ := Mod.extendRestrictAdjunction (coefficientMap a X)
  set adj₂ := Mod.extendRestrictAdjunction (coefficientMap a S)
  set adjR := upperStarLowerStarAdjunction Λ f
  set adjS := upperStarLowerStarAdjunction Λ' f
  set β := (adj₁.homEquiv _ _).symm ((f)^*⟦Λ⟧.map φ ≫ (comapUpperStarIso a f).inv.app L)
  have H : adj₂.homEquiv _ _ (adjS.homEquiv _ _ ((pullIso a f).inv.app K ≫ β)) =
      adjR.homEquiv _ _ (adj₁.homEquiv _ _ β) ≫ (comapLowerStarIso a f).inv.app _ :=
    Adjunction.homEquiv_homEquiv_pullIsoOfComapIso_inv adj₁ adj₂ adjR adjS _ K β
  have hc := squareCompatible_upperStarLowerStarAdjunction_unit a f L
  simp only [Functor.idSquareIso_hom_app, Functor.pasteSquareIso_hom_app, Category.id_comp,
    Functor.comp_obj, Functor.id_obj] at hc
  have H' : adj₂.homEquiv _ _ (adjS.homEquiv _ _ ((f)^*⟦Λ'⟧.map (((adj₂.homEquiv _ _).symm φ)))) =
      adj₂.homEquiv _ _ (adjS.homEquiv _ _ ((pullIso a f).inv.app K ≫ β)) := by
    rw [H, Equiv.apply_symm_apply, adjR.homEquiv_naturality_left, adjR.homEquiv_unit,
      adjS.homEquiv_unit, adjS.unit_naturality, adj₂.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Category.assoc, Category.assoc]
    congr 1
    rw [← hc]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.id_comp, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [(adjS.homEquiv _ _).injective ((adj₂.homEquiv _ _).injective H'), Iso.hom_inv_id_app_assoc]

/-- A morphism `Λ'_S ⊗_{Λ_S} K ⟶ L` adjoint to `φ : K ⟶ Res L` is an isomorphism as soon as, for
a pro-étale cover `{f_i}`, all the adjoints of the `f_i^* φ` are. -/
theorem isIso_homEquiv_symm_of_cover {S : Scheme.{u}}
    {K : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)}
    (φ : K ⟶ (Mod.comap (coefficientMap a S)).obj L)
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (h : ∀ i, IsIso (((Mod.extendRestrictAdjunction (coefficientMap a (𝒰.X i))).homEquiv _ _).symm
      ((𝒰.f i)^*⟦Λ⟧.map φ ≫ (comapUpperStarIso a (𝒰.f i)).inv.app L))) :
    IsIso (((Mod.extendRestrictAdjunction (coefficientMap a S)).homEquiv _ _).symm φ) := by
  refine isIso_of_isIso_upperStar_map_of_cover Λ' _ 𝒰 fun i ↦ ?_
  have := h i
  rw [← pullIso_hom_app_comp_upperStar_map_homEquiv_symm] at this
  exact IsIso.of_isIso_comp_left ((pullIso a (𝒰.f i)).hom.app K) _

end Adjoint

end AlgebraicGeometry.ProEtale.CondensedRing
