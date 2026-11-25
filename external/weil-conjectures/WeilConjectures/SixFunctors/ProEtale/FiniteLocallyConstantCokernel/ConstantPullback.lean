/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf

/-!
# Pullbacks of constant pro-étale sheaves

For a morphism of schemes `g : Z ⟶ Y`, the pro-étale pullback `g^*` sends the constant sheaf
`M_Y` to the constant sheaf `M_Z` (`AlgebraicGeometry.ProEtale.constantSheafCompUpperStarMkIdIso`):
both `constantSheaf ⋙ g^*` and `constantSheaf` are left adjoint to the sections over the
terminal object, since base change sends the terminal object `Y` of `Y_proét` to `Y ×_Y Z ≅ Z`.

Through this identification, a morphism `φ : M_Y ⟶ N_Y` pulls back to the constant morphism
`ψ_Z` of a morphism `ψ : M ⟶ N` as soon as the global section map `M ⟶ Γ(Y, N_Y)` of `φ` agrees
with `ψ` followed by `N ⟶ Γ(Y, N_Y)` after restriction to an object `V ⟶ Y` of `Y_proét` admitting
a section `Z ⟶ V ×_Y Z` (`constantSheafCompUpperStarMkIdIso_inv_app_comp_map_comp_hom_app`). For
sheaves of modules, `g^*` then sends the cokernel of `φ` to the constant sheaf of `N ⧸ ψ(M)`
(`AlgebraicGeometry.ProEtale.upperStarCokernelIsoOfEq`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

/-- If `F` and `F'` are both left adjoint to `G`, then transporting a morphism `F.obj x ⟶ y`
along the comparison `F' ≅ F` does not change its adjunct. -/
lemma CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_inv_app_comp {C D : Type*}
    [Category* C] [Category* D] {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    {x : C} {y : D} (f : F.obj x ⟶ y) :
    adj2.homEquiv _ _ ((adj1.leftAdjointUniq adj2).inv.app x ≫ f) = adj1.homEquiv _ _ f := by
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    G.map_comp, ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]

/-- The unit `N ⟶ Γ(T, N_C)` of the constant sheaf adjunction, restricted to an object `V`, is
the sheafification map of the constant presheaf at `V`. -/
lemma CategoryTheory.constantSheafAdj_unit_app_comp_map {C : Type*} [Category* C]
    (J : GrothendieckTopology C) (D : Type*) [Category* D] [HasWeakSheafify J D] {T : C}
    (hT : IsTerminal T) (N : D) {V : C} (f : V ⟶ T) :
    (constantSheafAdj J D hT).unit.app N ≫ ((constantSheaf J D).obj N).obj.map f.op =
      (toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op V) := by
  have h := (toSheafify J ((Functor.const Cᵒᵖ).obj N)).naturality f.op
  simp only [constantSheafAdj, constantPresheafAdj, Adjunction.comp_unit_app,
    Functor.constCompEvaluationObj_hom_app, sheafificationAdjunction_unit_app, evaluation_obj_map,
    Category.id_comp]
  exact h.symm.trans (Category.id_comp _)

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The sections over the terminal object of a pushforward: `(g_* G)(Y) = G(Y ×_Y Z) ≅ G(Z)`. -/
noncomputable def lowerStarCompSectionsMkIdIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (g)_*[A] ⋙ (sheafSections (ProEt.topology Y) A).obj (op (ProEt.mk (𝟙 Y))) ≅
      (sheafSections (ProEt.topology Z) A).obj (op (ProEt.mk (𝟙 Z))) :=
  NatIso.ofComponents (fun F ↦ F.obj.mapIso (overPullbackObjMkIdIso g).op.symm)
    (fun α ↦ (α.hom.naturality _).symm)

/-- The pro-étale pullback of a constant sheaf is constant: `g^* (M_Y) ≅ M_Z`. Both sides are
left adjoint to the sections over the terminal object `Z` of `Z_proét`. -/
noncomputable def constantSheafCompUpperStarMkIdIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    constantSheaf (ProEt.topology Y) A ⋙ (g)^*[A] ≅ constantSheaf (ProEt.topology Z) A :=
  (((constantSheafAdj (ProEt.topology Y) A (ProEt.isTerminalMkId Y)).comp
      (upperStarLowerStarAdjunction A g)).ofNatIsoRight
    (lowerStarCompSectionsMkIdIso A g)).leftAdjointUniq
    (constantSheafAdj (ProEt.topology Z) A (ProEt.isTerminalMkId Z))

/-- The global section map `M ⟶ Γ(Z, N_Z)` of the pullback `g^* φ` of a morphism
`φ : M_Y ⟶ N_Y` of constant sheaves is the global section map of `φ` followed by the map
`Γ(Y, N_Y) ⟶ Γ(Z, g^* N_Y) ≅ Γ(Z, N_Z)` induced by the unit of `g^* ⊣ g_*`. -/
lemma homEquiv_constantSheafCompUpperStarMkIdIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) {M N : A}
    (φ : (constantSheaf (ProEt.topology Y) A).obj M ⟶ (constantSheaf (ProEt.topology Y) A).obj N) :
    (constantSheafAdj (ProEt.topology Z) A (ProEt.isTerminalMkId Z)).homEquiv _ _
      ((constantSheafCompUpperStarMkIdIso A g).inv.app M ≫ (g)^*[A].map φ ≫
        (constantSheafCompUpperStarMkIdIso A g).hom.app N) =
    (constantSheafAdj (ProEt.topology Y) A (ProEt.isTerminalMkId Y)).homEquiv _ _ φ ≫
      ((upperStarLowerStarAdjunction A g).unit.app ((constantSheaf _ A).obj N)).hom.app
        (op (ProEt.mk (𝟙 Y))) ≫
      ((g)^*[A].obj ((constantSheaf _ A).obj N)).obj.map (overPullbackObjMkIdIso g).inv.op ≫
      ((constantSheafCompUpperStarMkIdIso A g).hom.app N).hom.app (op (ProEt.mk (𝟙 Z))) := by
  rw [constantSheafCompUpperStarMkIdIso, Adjunction.homEquiv_leftAdjointUniq_inv_app_comp,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  dsimp only
  erw [Equiv.trans_apply, Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit (upperStarLowerStarAdjunction A g)]
  simp [lowerStarCompSectionsMkIdIso, lowerStar_map_hom_app]

/-- The section over the terminal object `Z` of `g^* P` induced by a global section of `P` only
depends on the restriction of the section to any `V ⟶ Y` admitting a lift
`t : Z ⟶ V ×_Y Z`. -/
@[reassoc]
lemma unit_app_hom_app_mkId_comp_map {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (P : Sheaf (ProEt.topology Y) A) {V : Y.ProEt} (f : V ⟶ ProEt.mk (𝟙 Y))
    (t : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    ((upperStarLowerStarAdjunction A g).unit.app P).hom.app (op (ProEt.mk (𝟙 Y))) ≫
        ((g)^*[A].obj P).obj.map (overPullbackObjMkIdIso g).inv.op =
      P.obj.map f.op ≫ ((upperStarLowerStarAdjunction A g).unit.app P).hom.app (op V) ≫
        ((g)^*[A].obj P).obj.map t.op := by
  have h₁ := ((upperStarLowerStarAdjunction A g).unit.app P).hom.naturality f.op
  have h₂ : t ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f =
      (overPullbackObjMkIdIso g).inv :=
    ((ProEt.isTerminalMkId Z).ofIso (overPullbackObjMkIdIso g).symm).hom_ext _ _
  rw [reassoc_of% h₁, ← h₂, op_comp, Functor.map_comp]
  rfl

/-- **Local criterion for the pullback of a morphism of constant sheaves to be constant.** Let
`φ : M_Y ⟶ N_Y` and `ψ : M ⟶ N`. If, after restriction to some `V ⟶ Y` admitting a lift
`Z ⟶ V ×_Y Z`, the global section map of `φ` agrees with `ψ` followed by `N ⟶ Γ(Y, N_Y)`, then
`g^* φ` is identified with the constant morphism `ψ_Z`. -/
lemma constantSheafCompUpperStarMkIdIso_inv_app_comp_map_comp_hom_app {Z X : Scheme.{u}}
    (g : Z ⟶ X) {V : X.ProEt} (f : V ⟶ ProEt.mk (𝟙 X))
    (t : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) {M N : A}
    (φ : (constantSheaf (ProEt.topology X) A).obj M ⟶ (constantSheaf (ProEt.topology X) A).obj N)
    (ψ : M ⟶ N)
    (h : (constantSheafAdj (ProEt.topology X) A (ProEt.isTerminalMkId X)).homEquiv _ _ φ ≫
        ((constantSheaf _ A).obj N).obj.map f.op =
      ψ ≫ (constantSheafAdj (ProEt.topology X) A (ProEt.isTerminalMkId X)).unit.app N ≫
        ((constantSheaf _ A).obj N).obj.map f.op) :
    (constantSheafCompUpperStarMkIdIso A g).inv.app M ≫ (g)^*[A].map φ ≫
        (constantSheafCompUpperStarMkIdIso A g).hom.app N =
      (constantSheaf (ProEt.topology Z) A).map ψ := by
  apply ((constantSheafAdj (ProEt.topology Z) A (ProEt.isTerminalMkId Z)).homEquiv _ _).injective
  have hψ : (constantSheaf (ProEt.topology Z) A).map ψ =
      (constantSheafCompUpperStarMkIdIso A g).inv.app M ≫
        (g)^*[A].map ((constantSheaf _ A).map ψ) ≫
          (constantSheafCompUpperStarMkIdIso A g).hom.app N := by
    rw [← Functor.comp_map, (constantSheafCompUpperStarMkIdIso A g).hom.naturality,
      Iso.inv_hom_id_app_assoc]
  rw [hψ, homEquiv_constantSheafCompUpperStarMkIdIso, homEquiv_constantSheafCompUpperStarMkIdIso,
    unit_app_hom_app_mkId_comp_map_assoc _ _ _ f t,
    Adjunction.homEquiv_unit _ _ _ ((constantSheaf (ProEt.topology X) A).map ψ),
    Adjunction.unit_naturality]
  simp only [Category.assoc]
  rw [reassoc_of% h]

/-- Solving the identification `g^* φ ≅ ψ_Z` for `g^* φ`. -/
lemma upperStar_map_eq_of_constantSheafCompUpperStarMkIdIso {Z X : Scheme.{u}} (g : Z ⟶ X)
    {M N : A}
    (φ : (constantSheaf (ProEt.topology X) A).obj M ⟶ (constantSheaf (ProEt.topology X) A).obj N)
    (ψ : M ⟶ N)
    (h : (constantSheafCompUpperStarMkIdIso A g).inv.app M ≫ (g)^*[A].map φ ≫
        (constantSheafCompUpperStarMkIdIso A g).hom.app N =
      (constantSheaf (ProEt.topology Z) A).map ψ) :
    (g)^*[A].map φ = (constantSheafCompUpperStarMkIdIso A g).hom.app M ≫
      (constantSheaf (ProEt.topology Z) A).map ψ ≫
        (constantSheafCompUpperStarMkIdIso A g).inv.app N := by
  rw [← h]
  simp

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- If the pullback `g^* φ` of a morphism `φ : M_X ⟶ N_X` of constant sheaves of modules is
identified with the constant morphism `ψ_Z`, then `g^*` sends the cokernel of `φ` to the constant
sheaf of `N ⧸ ψ(M)`: `g^*` and the constant sheaf functor preserve cokernels, being left
adjoints. -/
noncomputable def upperStarCokernelIsoOfEq {Z X : Scheme.{u}} (g : Z ⟶ X)
    {M N : ModuleCat.{u + 1} Λ}
    (φ : (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj M ⟶
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj N) (ψ : M ⟶ N)
    (h : (constantSheafCompUpperStarMkIdIso _ g).inv.app M ≫ (g)^*[ModuleCat.{u + 1} Λ].map φ ≫
        (constantSheafCompUpperStarMkIdIso _ g).hom.app N =
      (constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)).map ψ) :
    (g)^*[ModuleCat.{u + 1} Λ].obj (cokernel φ) ≅
      (constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (N ⧸ LinearMap.range ψ.hom)) :=
  PreservesCokernel.iso _ φ ≪≫
    cokernelIsoOfEq (upperStar_map_eq_of_constantSheafCompUpperStarMkIdIso _ g φ ψ h) ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ (PreservesCokernel.iso _ ψ).symm ≪≫
    (constantSheaf _ _).mapIso (ModuleCat.cokernelIsoRangeQuotient ψ)

end AlgebraicGeometry.ProEtale
