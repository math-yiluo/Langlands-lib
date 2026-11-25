/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection

/-!
# Germs of sections of pro-étale sheaves

Let `g : Z ⟶ Y` be a morphism of schemes and `P` a pro-étale sheaf on `Y`. A section `σ` of `P`
over an object `V` of the small pro-étale site of `Y`, together with a lift
`t : Z ⟶ V ×_Y Z` of `Z` through the base change of `V` (a morphism from the terminal object of
`Z_proét`), has a *germ* `germ g P t σ ∈ Γ(Z, g^* P)`: the image of `σ` under the unit
`P ⟶ g_* g^* P`, restricted along `t` (`AlgebraicGeometry.ProEtale.germ`).

If `Z = Spec K` for an algebraically closed field `K`, so that `Γ(Z, g^* P)` is the stalk of `P`
at the geometric point `g`, the stalk is the filtered colimit of the sections over the
pro-étale neighbourhoods `(V, t)`:

- every element of the stalk is a germ (`AlgebraicGeometry.ProEtale.exists_germ_eq`);
- a section with vanishing germ vanishes on a smaller neighbourhood
  (`AlgebraicGeometry.ProEtale.exists_map_eq_zero_of_germ_eq_zero`).

Both follow from the description of `g^* P` as the sheafification of a left Kan extension, a
filtered colimit, and from the fact that every covering sieve of the terminal object of
`(Spec K)_proét` is the maximal sieve
(`AlgebraicGeometry.Scheme.ProEt.id_mem_of_mem_topology_of_iso`),
so that sheafification does not change the sections over `Spec K`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

section Germ

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The germ `Γ(Z, g^* P)` of a section of `P` over `V`, along a lift `t : Z ⟶ V ×_Y Z`: the
image under the unit `P ⟶ g_* g^* P`, restricted along `t`. -/
noncomputable def germ (P : Sheaf (ProEt.topology Y) A) {V : Y.ProEt}
    (t : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    P.obj.obj (op V) ⟶ (Sheaf.Γ _ A).obj ((g)^*[A].obj P) :=
  ((upperStarLowerStarAdjunction A g).unit.app P).hom.app (op V) ≫
    ((g)^*[A].obj P).obj.map t.op ≫
    (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Z)).inv.app _

variable {A g}

/-- Germs are natural in the sheaf. -/
@[reassoc]
lemma germ_naturality {P Q : Sheaf (ProEt.topology Y) A} (φ : P ⟶ Q) {V : Y.ProEt}
    (t : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    φ.hom.app (op V) ≫ germ A g Q t = germ A g P t ≫ (Sheaf.Γ _ A).map ((g)^*[A].map φ) := by
  have h₁ := congrArg (fun f ↦ f.hom.app (op V))
    ((upperStarLowerStarAdjunction A g).unit.naturality φ)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h₁
  have h₂ := ((g)^*[A].map φ).hom.naturality t.op
  have h₃ := (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Z)).inv.naturality
    ((g)^*[A].map φ)
  rw [germ, germ, reassoc_of% h₁, lowerStar_map_hom_app]
  simp only [Category.assoc]
  rw [← reassoc_of% h₂]
  congr 2

/-- The germ of the restriction of a section to a smaller neighbourhood is the germ of the
section. -/
@[reassoc]
lemma map_germ {P : Sheaf (ProEt.topology Y) A} {V V' : Y.ProEt} (f : V' ⟶ V)
    (t : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)
    (t' : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V')
    (h : t' ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f = t) :
    P.obj.map f.op ≫ germ A g P t' = germ A g P t := by
  have h₁ := ((upperStarLowerStarAdjunction A g).unit.app P).hom.naturality f.op
  rw [germ, germ, reassoc_of% h₁]
  congr 1
  rw [← h, op_comp, Functor.map_comp_assoc]
  rfl

end Germ

section Stalk

variable {R : Type (u + 1)} [Ring R] {K : Type u} [Field K] {Y : Scheme.{u}}
  (g : Spec (.of K) ⟶ Y) (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))

/-- The unit `P ⟶ g_* g^* P` is the unit of the left Kan extension followed by
sheafification. -/
lemma upperStarLowerStarAdjunction_unit_app_hom_app (V : Y.ProEt) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).unit.app P).hom.app (op V) =
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtensionUnit P.obj).app
          (op V) ≫
        (toSheafify _ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtension
          P.obj)).app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)) :=
  rfl

/-- The germ along `t` is the image under the unit of the left Kan extension along the opposite
of base change, restricted along `t` and followed by sheafification. -/
lemma germ_eq {V : Y.ProEt}
    (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    germ _ g P t =
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtensionUnit P.obj).app
          (op V) ≫
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtension P.obj).map t.op ≫
        (toSheafify _ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtension
          P.obj)).app (op (ProEt.mk (𝟙 _))) ≫
        (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId _)).inv.app
          ((g)^*[ModuleCat.{u + 1} R].obj P) := by
  have n := (toSheafify (ProEt.topology _)
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtension P.obj)).naturality t.op
  rw [germ, upperStarLowerStarAdjunction_unit_app_hom_app, Category.assoc]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact n.symm

variable [IsAlgClosed K]

/-- **Germs vanish locally.** If the germ of a section `σ` of `P` over `V` at a geometric point
`g : Spec K ⟶ Y` vanishes, then `σ` vanishes on a smaller pro-étale neighbourhood `V' ⟶ V`
of `g`. -/
lemma exists_map_eq_zero_of_germ_eq_zero {V : Y.ProEt}
    (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)
    (σ : ToType (P.obj.obj (op V))) (hσ : germ _ g P t σ = 0) :
    ∃ (V' : Y.ProEt) (f : V' ⟶ V)
      (t' : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V'),
      t' ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f = t ∧
        P.obj.map f.op σ = 0 := by
  have h₀ : (toSheafify (ProEt.topology _)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtension P.obj)).app
      (op (ProEt.mk (𝟙 _)))
        (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtension P.obj).map t.op
        (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtensionUnit P.obj).app
          (op V) σ)) = 0 := by
    rw [germ_eq] at hσ
    simp only [ConcreteCategory.comp_apply] at hσ
    have e := congrArg ((Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId _)).hom.app
      ((g)^*[ModuleCat.{u + 1} R].obj P)) hσ
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app, map_zero] at e
    exact e
  have hS := Presheaf.equalizerSieve_mem (ProEt.topology _)
    (toSheafify (ProEt.topology _)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtension P.obj))
    (X := op (ProEt.mk (𝟙 _))) _ 0 (h₀.trans (map_zero _).symm)
  have hid := ProEt.id_mem_of_mem_topology_of_iso (Iso.refl _) hS
  obtain ⟨V', f, t', ht', h⟩ := Functor.exists_map_eq_of_leftKanExtensionUnit_eq
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) P.obj t σ 0 (by simpa using hid)
  exact ⟨V', f, t', ht', by simpa using h⟩

/-- **Every element of a stalk is a germ.** Every element of `Γ(Spec K, g^* P)` is the germ of a
section of `P` over some pro-étale neighbourhood of the geometric point `g`. -/
lemma exists_germ_eq (a : ToType ((Sheaf.Γ _ _).obj ((g)^*[ModuleCat.{u + 1} R].obj P))) :
    ∃ (V : Y.ProEt)
      (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)
      (σ : ToType (P.obj.obj (op V))), germ _ g P t σ = a := by
  -- the section `b` over `Spec K` of the sheafification of the left Kan extension
  obtain ⟨c, hc⟩ := ProEt.id_mem_of_mem_topology_of_iso (Iso.refl _)
    (Presheaf.imageSieve_mem (ProEt.topology _) (toSheafify (ProEt.topology _)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtension P.obj))
      (U := op (ProEt.mk (𝟙 _))) ((Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId _)).hom.app
        ((g)^*[ModuleCat.{u + 1} R].obj P) a))
  -- `c` is a section of the left Kan extension, a filtered colimit
  have : IsFiltered (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op
      (op (ProEt.mk (𝟙 (Spec (.of K)))))) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _)
  obtain ⟨j, σ, hσ⟩ := Concrete.isColimit_exists_rep _
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op P.obj (op (ProEt.mk (𝟙 _)))) c
  refine ⟨j.left.unop, j.hom.unop, σ, ?_⟩
  rw [Functor.LeftExtension.coconeAt_ι_app, ConcreteCategory.comp_apply] at hσ
  rw [germ_eq]
  simp only [ConcreteCategory.comp_apply]
  erw [hσ]
  have hc' : (toSheafify (ProEt.topology _)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.leftKanExtension P.obj)).app
      (op (ProEt.mk (𝟙 _))) c = (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId _)).hom.app
        ((g)^*[ModuleCat.{u + 1} R].obj P) a := by
    rw [hc, op_id]
    erw [CategoryTheory.Functor.map_id]
    rfl
  erw [hc']
  exact ConcreteCategory.congr_hom ((Sheaf.ΓNatIsoSheafSections _ _
    (ProEt.isTerminalMkId _)).hom_inv_id_app ((g)^*[ModuleCat.{u + 1} R].obj P)) a

end Stalk

end AlgebraicGeometry.ProEtale
