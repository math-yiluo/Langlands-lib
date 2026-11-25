/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.Sites.UnitHomEval
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison

/-!

# Scalars in the comparison of the two models of finite coefficients

Let `T` be a finite discrete commutative ring and `X` a scheme. The equivalence
`ProEtale.finiteCoefficientModEquivalence` identifies module objects `M` over `Λ_X = p_X^* T̲`
with sheaves of `T`-modules on `X_proét`, keeping the underlying abelian sheaf. This file
identifies the action of `t ∈ T` on the sections of the sheaf of `T`-modules: it is the action
on `M` of the constant global section `t` of `Λ_X`, the image under `p_X^*` of the constant
global section of `T̲ = C(-, T)`
(`ProEtale.finiteCoefficientModEquivalence_smul`).

## Main definitions and results

* `Mod.regularHomAddEquiv`: morphisms of module objects out of `A` are the global sections of
  the target.
* `Sheaf.unitHomEvalAddEquiv`: morphisms `𝟙 ⟶ F` of abelian sheaves are the sections of `F`
  over a terminal object.
* `Sheaf.constRingSheafSection`: the constant global section `t` of the constant ring sheaf `T`;
  on sections of a module object over it, its action is the action of `t`
  (`Sheaf.modSmul_modToPresheafMod`).
* `ProEtale.constRingSheafSection_comp_constRingSheafToCondensedRingObj`: the comparison
  `T_X ⟶ Λ_X` sends the constant section `t` to the image under `p_X^*` of the constant section
  of `T̲`.

-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

/-! ### Morphisms out of the regular module object -/

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] {A : C} [MonObj A]

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

/-- Morphisms of `A`-modules out of `A` are the global sections of the target: `x ↦ 1 ≫ x`, with
inverse `regularLift`. -/
def regularHomAddEquiv (M : Mod C A) : (regular A ⟶ M) ≃+ (𝟙_ C ⟶ M.X) where
  toFun x := η[A] ≫ x.hom
  invFun m := regularLift M m
  left_inv x := regular_hom_ext (one_comp_regularLift M _)
  right_inv m := one_comp_regularLift M m
  map_add' x y := by
    rw [add_hom, Preadditive.comp_add]

lemma regularHomAddEquiv_apply (M : Mod C A) (x : regular A ⟶ M) :
    regularHomAddEquiv M x = η[A] ≫ x.hom :=
  rfl

end Preadditive

end CategoryTheory.Mod

/-! ### Monoidal natural transformations and global sections -/

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (α : F ⟶ G) [α.IsMonoidal]

/-- A monoidal natural transformation `α : F ⟶ G` sends the image `ε ≫ F s` of a global section
`s : 𝟙 ⟶ Y` to its image `ε ≫ G s`. -/
@[reassoc]
lemma IsMonoidal.ε_comp_map_comp_app {Y : C} (s : 𝟙_ C ⟶ Y) :
    ε F ≫ F.map s ≫ α.app Y = ε G ≫ G.map s := by
  rw [α.naturality, IsMonoidal.unit_assoc]

end CategoryTheory.NatTrans

/-! ### Morphisms out of the unit of abelian sheaves -/

namespace CategoryTheory.Sheaf

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J Ab.{w}]
  [(J.W (A := Ab.{w})).IsMonoidal] {T : C}

/-- The morphism of abelian presheaves `ℤ ⟶ P` out of the monoidal unit (the constant presheaf
`ℤ`) sending `1` to the restrictions of a section `y` over a terminal object. -/
noncomputable def unitPresheafHomOfSection (hT : IsTerminal T) {P : Cᵒᵖ ⥤ Ab.{w}}
    (y : P.obj (op T)) : 𝟙_ (Cᵒᵖ ⥤ Ab.{w}) ⟶ P where
  app X := AddCommGrpCat.ofHom
    { toFun n := (n : ULift.{w} ℤ).down • P.map (hT.from X.unop).op y
      map_zero' := zero_smul ℤ _
      map_add' a b := add_smul a.down b.down _ }
  naturality X Y f := by
    have h : (hT.from X.unop).op ≫ f = (hT.from Y.unop).op :=
      Quiver.Hom.unop_inj (hT.hom_ext _ _)
    ext n
    change (n : ULift.{w} ℤ).down • P.map (hT.from Y.unop).op y =
      P.map f ((n : ULift.{w} ℤ).down • P.map (hT.from X.unop).op y)
    rw [map_zsmul, ← ConcreteCategory.comp_apply, ← P.map_comp, h]

lemma unitPresheafHomOfSection_app_one (hT : IsTerminal T) {P : Cᵒᵖ ⥤ Ab.{w}}
    (y : P.obj (op T)) : (unitPresheafHomOfSection hT y).app (op T) (ULift.up 1) = y := by
  simp [unitPresheafHomOfSection]

/-- Every section over a terminal object is the value at the unit section of a morphism out of
the unit. -/
lemma unitHomEval_surjective (hT : IsTerminal T) (F : Sheaf J Ab.{w}) :
    Function.Surjective (unitHomEval (J := J) T (F := F)) := by
  intro y
  let adj := sheafificationAdjunction J Ab.{w}
  refine ⟨ε (presheafToSheaf J Ab.{w}) ≫ (adj.homEquiv _ _).symm
    (unitPresheafHomOfSection hT y), ?_⟩
  have e : ε (sheafToPresheaf J Ab.{w}) ≫ (sheafToPresheaf J Ab.{w}).map
      (ε (presheafToSheaf J Ab.{w}) ≫ (adj.homEquiv _ _).symm (unitPresheafHomOfSection hT y)) =
      unitPresheafHomOfSection hT y := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_right_symm]
    have e' : (adj.homEquiv _ _).symm (ε (sheafToPresheaf J Ab.{w})) =
        Functor.OplaxMonoidal.η (presheafToSheaf J Ab.{w}) := by
      apply (adj.homEquiv _ _).injective
      rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, adj.unit_app_unit_comp_map_η]
    rw [e', Functor.Monoidal.η_ε_assoc]
  exact (congrArg (fun f : 𝟙_ (Cᵒᵖ ⥤ Ab.{w}) ⟶ F.obj ↦ f.app (op T) (ULift.up 1)) e).trans
    (unitPresheafHomOfSection_app_one hT y)

/-- **Morphisms out of the unit of abelian sheaves are the sections over a terminal object**:
`s ↦ s(1)`. -/
noncomputable def unitHomEvalAddEquiv (hT : IsTerminal T) (F : Sheaf J Ab.{w}) :
    (𝟙_ (Sheaf J Ab.{w}) ⟶ F) ≃+ F.obj.obj (op T) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (unitHomEval T) fun s t ↦ by simp [unitHomEval])
    ⟨unitHomEval_injective hT F, unitHomEval_surjective hT F⟩

lemma unitHomEvalAddEquiv_apply (hT : IsTerminal T) {F : Sheaf J Ab.{w}}
    (s : 𝟙_ (Sheaf J Ab.{w}) ⟶ F) : unitHomEvalAddEquiv hT F s = unitHomEval T s :=
  rfl

end CategoryTheory.Sheaf

/-! ### The constant global sections of a constant ring sheaf -/

namespace AddCommGrpCat

/-- The morphism `ℤ ⟶ M`, `n ↦ n • m`, out of the monoidal unit of abelian groups. -/
def unitHom {M : Ab.{w}} (m : M) : 𝟙_ Ab.{w} ⟶ M :=
  ofHom
    { toFun n := (n : ULift.{w} ℤ).down • m
      map_zero' := zero_smul ℤ _
      map_add' a b := add_smul a.down b.down _ }

lemma unitHom_apply {M : Ab.{w}} (m : M) (n : ULift.{w} ℤ) : (unitHom m).hom n = n.down • m :=
  rfl

end AddCommGrpCat

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {T : Type (u + 1)} [Ring T]

/-- The constant global section `t` of the constant ring sheaf `T`: the image of
`ℤ ⟶ T, 1 ↦ t` under the monoidal constant sheaf functor. -/
noncomputable def constRingSheafSection (t : T) : 𝟙_ (Sheaf J Ab.{u + 1}) ⟶ constRingSheaf J T :=
  ε (constantSheaf J Ab.{u + 1}) ≫
    (constantSheaf J Ab.{u + 1}).map (AddCommGrpCat.unitHom (M := AddCommGrpCat.of T) t)

/-- The unit of the monoidal constant sheaf functor is the unit of sheafification. -/
lemma ε_constantSheaf :
    ε (constantSheaf J Ab.{u + 1}) = ε (presheafToSheaf J Ab.{u + 1}) := by
  have h : ε (Functor.const Cᵒᵖ : Ab.{u + 1} ⥤ Cᵒᵖ ⥤ Ab.{u + 1}) = 𝟙 _ := by
    ext
    rfl
  change ε (presheafToSheaf J Ab.{u + 1}) ≫
    (presheafToSheaf J Ab.{u + 1}).map (ε (Functor.const Cᵒᵖ)) = _
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The constant global section `t`, read on underlying presheaves after the unit of
`sheafToPresheaf`, is the constant section `t` followed by the unit of sheafification. -/
lemma ε_comp_constRingSheafSection (t : T) :
    ε (sheafToPresheaf J Ab.{u + 1}) ≫
        (sheafToPresheaf J Ab.{u + 1}).map (constRingSheafSection J t) =
      (Functor.const Cᵒᵖ).map (AddCommGrpCat.unitHom (M := AddCommGrpCat.of T) t) ≫
        (sheafificationAdjunction J Ab.{u + 1}).unit.app _ := by
  have e : ε (sheafToPresheaf J Ab.{u + 1}) ≫
      (sheafToPresheaf J Ab.{u + 1}).map (ε (presheafToSheaf J Ab.{u + 1})) =
      (sheafificationAdjunction J Ab.{u + 1}).unit.app _ := by
    rw [← (sheafificationAdjunction J Ab.{u + 1}).unit_app_unit_comp_map_η, Category.assoc,
      Functor.Monoidal.η_ε_map]
    exact Category.comp_id _
  rw [constRingSheafSection, ε_constantSheaf, Functor.map_comp, ← Category.assoc, e]
  exact ((sheafificationAdjunction J Ab.{u + 1}).unit.naturality _).symm

variable {J} in
/-- **The action of `t ∈ T` on the sections of a module object over the constant ring sheaf
`T`** is the action of the constant global section `t`. -/
lemma modSmul_modToPresheafMod (N : Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T)) (U : Cᵒᵖ)
    (t : T) (y : N.X.obj.obj U) :
    Presheaf.modSmul ((modToPresheafMod J T).obj N) U t y =
      (Mod.globalSmul (constRingSheafSection J t) N).hom.app U y := by
  have key : (sheafToPresheaf J Ab.{u + 1}).map (Mod.globalSmul (constRingSheafSection J t) N) =
      (λ_ _).inv ≫ (Functor.const Cᵒᵖ).map (AddCommGrpCat.unitHom (M := AddCommGrpCat.of T) t) ▷
        _ ≫ Mod.act ((modToPresheafMod J T).obj N).X := by
    rw [Mod.globalSmul, Functor.map_comp, Functor.map_comp, ← left_unitality_inv,
      Category.assoc, Category.assoc, ← μ_natural_left_assoc, ← comp_whiskerRight_assoc,
      ε_comp_constRingSheafSection, comp_whiskerRight_assoc]
    rfl
  refine Eq.trans ?_ (congrArg (fun f ↦ (f.app U).hom y) key).symm
  refine Eq.trans (congrArg (fun z : T ↦ Presheaf.modSmul ((modToPresheafMod J T).obj N) U z y)
    (one_smul ℤ t).symm) ?_
  rfl

end CategoryTheory.Sheaf

/-! ### The comparison `T_X ≅ Λ_X` on constant global sections -/

namespace Profinite

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

omit [DiscreteTopology T] [Finite T] in
/-- The comparison `T ⟶ T̲` from the constant ring sheaf to the condensed ring `C(-, T)` sends
the constant global section `t` to the constant global section `t`. -/
lemma constRingSheafSection_comp_constRingSheafToContinuousMapRingObj (t : T) :
    Sheaf.constRingSheafSection (coherentTopology Profinite.{u}) (ULift.up t : ULift.{u + 1} T) ≫
        constRingSheafToContinuousMapRingObj T =
      (continuousMapConstRingHom.{u} T t).hom := by
  let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
  refine Sheaf.hom_ext_of_ε_comp ?_
  refine Eq.trans ?_ (Sheaf.ε_comp_ringHomΓSheafCompose_hom _ (continuousMapRingSheaf.{u} T)
    (continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) t).symm
  rw [Functor.map_comp, ← Category.assoc, Sheaf.ε_comp_constRingSheafSection,
    constRingSheafToContinuousMapRingObj, Functor.map_comp, Category.assoc]
  erw [← reassoc_of% (adj.unit.naturality (constToContinuousMap T)), adj.right_triangle_components,
    Category.comp_id]
  ext S n
  refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
  change (n.down • (ULift.up t : ULift.{u + 1} T)).down =
    (((n.down : ℤ) : ULift.{u + 1} C(S.unop, T)) * ULift.up (ContinuousMap.const _ t)).down s
  simp

end Profinite

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

omit [DiscreteTopology T] [Finite T] in
/-- **The comparison `T_X ⟶ Λ_X` on constant global sections**: it sends the constant global
section `t` of the constant ring sheaf `T_X` to the image under `p_X^*` of the constant global
section `t` of the condensed ring `T̲ = C(-, T)`. -/
lemma constRingSheafSection_comp_constRingSheafToCondensedRingObj (t : T) :
    Sheaf.constRingSheafSection (Scheme.ProEt.topology X) (ULift.up t : ULift.{u + 1} T) ≫
        constRingSheafToCondensedRingObj X T =
      ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom.{u} T t).hom := by
  let tab := AddCommGrpCat.unitHom (M := AddCommGrpCat.of (ULift.{u + 1} T)) (ULift.up t)
  let π := (toSpecZ X)^*[Ab.{u + 1}]
  let cS := constantSheaf (Scheme.ProEt.topology specZ.{u}) Ab.{u + 1}
  let cP := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  have h₁ := NatTrans.IsMonoidal.ε_comp_map_comp_app (constantSheafToUpperStarToSpecZ X) tab
  have h₂ := NatTrans.IsMonoidal.ε_comp_map_comp_app constantSheafToPointUpperStar.{u} tab
  have h₃ := Profinite.constRingSheafSection_comp_constRingSheafToContinuousMapRingObj.{u} T t
  have e₁ : ε (cS ⋙ π) = ε π ≫ π.map (ε cS) := rfl
  have e₂ : ε (cP ⋙ pointUpperStar.{u}) = ε pointUpperStar.{u} ≫ pointUpperStar.map (ε cP) := rfl
  have e₃ : ε (upperStarFromPoint X) = ε π ≫ π.map (ε pointUpperStar.{u}) := rfl
  rw [Sheaf.constRingSheafSection, constRingSheafToCondensedRingObj, Category.assoc,
    reassoc_of% h₁, e₁, e₃]
  simp only [Category.assoc]
  refine congrArg (fun g ↦ ε π ≫ g) ?_
  change π.map (ε cS) ≫ π.map (cS.map tab) ≫ π.map (constantSheafToPointUpperStar.app _) ≫
      π.map (pointUpperStar.map (Profinite.constRingSheafToContinuousMapRingObj T)) =
    π.map (ε pointUpperStar.{u}) ≫
      π.map (pointUpperStar.map (Profinite.continuousMapConstRingHom.{u} T t).hom)
  rw [← π.map_comp, ← π.map_comp, ← π.map_comp, ← π.map_comp, reassoc_of% h₂, e₂, Category.assoc,
    ← pointUpperStar.map_comp, ← pointUpperStar.map_comp, ← Category.assoc (ε cP), ← h₃]
  rfl

/-- **The scalars of `finiteCoefficientModEquivalence`**: for a module object `M` over
`Λ_X = p_X^* T̲`, the action of `t ∈ T` on the sections of the sheaf of `T`-modules
corresponding to `M` is the action on `M` of the constant global section `t` of `Λ_X`. -/
lemma finiteCoefficientModEquivalence_smul
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))
    (U : X.ProEtᵒᵖ) (t : T) (y : ((finiteCoefficientModEquivalence X T).functor.obj M).obj.obj U) :
    (ULift.up t : ULift.{u + 1} T) • y =
      (Mod.globalSmul (ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom.{u} T t).hom) M).hom.app
          U y := by
  refine (Sheaf.modSmul_modToPresheafMod
    ((Mod.comap (constRingSheafToCondensedRingObj X T)).obj M) U _ y).trans ?_
  rw [Mod.globalSmul_comap, constRingSheafSection_comp_constRingSheafToCondensedRingObj]
  rfl

end AlgebraicGeometry.ProEtale
