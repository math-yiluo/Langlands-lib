/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.InjectiveRestrictionSurjective
import WeilConjectures.CategoryTheory.Abelian.RightDerived.InjExactSquareBoundaryExact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.InjExactSquareBoundaryNaturality
import Mathlib.Topology.Sheaves.MayerVietoris

/-! # Mayer--Vietoris for modules on a ringed space

Source: Stacks Project, Cohomology, Lemma 20.8.2, Tag 01EB
(blueprint: lem-sc-mayer-vietoris-ringed-space).
-/

@[expose] public section

universe v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

private noncomputable def sectionRestriction (X : RingedSpace.{v})
    {U V : Opens X} (i : V ⟶ U) : openModuleSections X U ⟶ openModuleSections X V :=
  Functor.whiskerLeft (SheafOfModules.forget (moduleRings X) ⋙
    PresheafOfModules.toPresheaf (moduleRings X).obj)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{v}).map i.op)

private theorem sectionRestriction_comp (X : RingedSpace.{v})
    {U V W : Opens X} (i : V ⟶ U) (j : W ⟶ V) :
    sectionRestriction X i ≫ sectionRestriction X j = sectionRestriction X (j ≫ i) := by
  apply NatTrans.ext
  funext F
  exact (F.val.presheaf.map_comp i.op j.op).symm

private theorem sectionRestriction_square (X : RingedSpace.{v})
    {A B C D : Opens X} (ab : B ⟶ A) (bd : D ⟶ B) (ac : C ⟶ A) (cd : D ⟶ C) :
    sectionRestriction X ab ≫ sectionRestriction X bd =
      sectionRestriction X ac ≫ sectionRestriction X cd := by
  rw [sectionRestriction_comp, sectionRestriction_comp]
  congr 1

private theorem section_pair_injective_exact (X : RingedSpace.{v}) (U V : Opens X)
    (F : SheafOfModules.{v} (moduleRings X)) :
    Function.Injective (fun x : (openModuleSections X (U ⊔ V)).obj F ↦
      ((sectionRestriction X (homOfLE le_sup_left)).app F x,
        (sectionRestriction X (homOfLE le_sup_right)).app F x)) ∧
    Function.Exact
      (fun x : (openModuleSections X (U ⊔ V)).obj F ↦
        ((sectionRestriction X (homOfLE le_sup_left)).app F x,
          (sectionRestriction X (homOfLE le_sup_right)).app F x))
      (fun x : (openModuleSections X U).obj F × (openModuleSections X V).obj F ↦
        (sectionRestriction X (homOfLE inf_le_left)).app F x.1 -
          (sectionRestriction X (homOfLE inf_le_right)).app F x.2) := by
  let G := (sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj
    ((SheafOfModules.toSheaf (moduleRings X)).obj F)
  have h := (Opens.mayerVietorisSquare U V).sheafCondition_of_sheaf G
  constructor
  · intro x y hxy
    exact h.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  · intro x
    constructor
    · intro hx
      have hx' : (sectionRestriction X
          (homOfLE (inf_le_left : U ⊓ V ≤ U))).app F x.1 =
        (sectionRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V))).app F x.2 :=
          sub_eq_zero.mp hx
      refine ⟨h.glue x.1 x.2 hx', ?_⟩
      apply Prod.ext
      · exact h.map_f₂₄_op_glue x.1 x.2 hx'
      · exact h.map_f₃₄_op_glue x.1 x.2 hx'
    · rintro ⟨y, rfl⟩
      change (F.val.presheaf.map (homOfLE inf_le_left).op)
          (F.val.presheaf.map (homOfLE le_sup_left).op y) -
        (F.val.presheaf.map (homOfLE inf_le_right).op)
          (F.val.presheaf.map (homOfLE le_sup_right).op y) = 0
      rw [← AddCommGrpCat.comp_apply, ← F.val.presheaf.map_comp,
        ← AddCommGrpCat.comp_apply, ← F.val.presheaf.map_comp]
      have he : (homOfLE (le_sup_left : U ≤ U ⊔ V)).op ≫
          (homOfLE (inf_le_left : U ⊓ V ≤ U)).op =
        (homOfLE (le_sup_right : V ≤ U ⊔ V)).op ≫
          (homOfLE (inf_le_right : U ⊓ V ≤ V)).op := Subsingleton.elim _ _
      rw [he, sub_self]

private noncomputable def sectionSquare (X : RingedSpace.{v}) (U V : Opens X) :
    InjectivelyExactSquare (SheafOfModules.{v} (moduleRings X)) where
  X₁ := openModuleSections X (U ⊔ V)
  X₂ := openModuleSections X U
  X₃ := openModuleSections X V
  X₄ := openModuleSections X (U ⊓ V)
  f₁₂ := sectionRestriction X (homOfLE le_sup_left)
  f₁₃ := sectionRestriction X (homOfLE le_sup_right)
  f₂₄ := sectionRestriction X (homOfLE inf_le_left)
  f₃₄ := sectionRestriction X (homOfLE inf_le_right)
  fac := sectionRestriction_square X _ _ _ _
  injective := fun I _ ↦ (section_pair_injective_exact X U V I).1
  exact := fun I _ ↦ (section_pair_injective_exact X U V I).2
  surjective := by
    intro I hI
    have := hI
    exact (AlgebraicGeometry.injective_restriction_surjective X (le_refl U) I).2 U V

/-- The Mayer--Vietoris long exact sequence for `O_X`-modules. We state it for every
pair of opens simultaneously, on their union; taking `U ⊔ V = ⊤` gives the sequence
on `X`. The connecting maps are natural transformations, hence natural in the module.
The last equality is compatibility with restriction to any open `W`. The remaining
squares commute by functoriality of cohomology restriction.

Source: Stacks Project, Cohomology, Lemma 20.8.2, Tag 01EB
(blueprint: lem-sc-mayer-vietoris-ringed-space).

Proof: Choose an injective resolution of the module
(`def-sc-ringed-space-module-cohomology`). Its restriction to every open remains an
injective resolution (`lem-sc-ringed-space-restrict-injective-resolution`). The sheaf
condition gives left exactness of sections on the two-open cover, and injectivity
makes the difference of restrictions surjective
(`lem-sc-ringed-space-injective-restriction-surjective`). This is a short exact
sequence of section complexes. Its long exact cohomology sequence
(`lem-weil-pbc-complex-ses-homology-long-exact`) has the indicated restriction maps.
For a module morphism, lift to injective resolutions
(`lem-weil-pbc-derived-functor-map-via-lift`) and restrict these lifts to the opens.
Naturality of the complex long exact sequence
(`lem-weil-pbc-complex-ses-long-exact-naturality`) gives natural connecting maps,
independent of the lift. Finally restrict the chosen resolution to `W`; it remains
injective, and restriction of sections is a morphism of the two short exact sequences
of complexes. The same long exact sequence naturality gives the last equality. -/
theorem module_mayerVietoris (X : RingedSpace.{v}) :
    let H := openModuleCohomology X
    let r : ∀ (p : ℕ) {U V : Opens X}, (V ⟶ U) → (H p U ⟶ H p V) :=
      fun p {_ _} i => openModuleCohomologyRestriction X p i
    ∃ δ : ∀ (U V : Opens X) (p : ℕ), H p (U ⊓ V) ⟶ H (p + 1) (U ⊔ V),
      (∀ (U V : Opens X) (F : SheafOfModules.{v} (moduleRings X)),
        Function.Injective (fun x : (H 0 (U ⊔ V)).obj F =>
          ((r 0 (homOfLE (show U ≤ U ⊔ V from le_sup_left))).app F x,
            (r 0 (homOfLE (show V ≤ U ⊔ V from le_sup_right))).app F x))) ∧
      (∀ (U V : Opens X) (F : SheafOfModules.{v} (moduleRings X)) (p : ℕ),
        Function.Exact
          (fun x : (H p (U ⊔ V)).obj F =>
            ((r p (homOfLE (show U ≤ U ⊔ V from le_sup_left))).app F x,
              (r p (homOfLE (show V ≤ U ⊔ V from le_sup_right))).app F x))
          (fun x : (H p U).obj F × (H p V).obj F =>
            (r p (homOfLE (show U ⊓ V ≤ U from inf_le_left))).app F x.1 -
              (r p (homOfLE (show U ⊓ V ≤ V from inf_le_right))).app F x.2) ∧
        Function.Exact
          (fun x : (H p U).obj F × (H p V).obj F =>
            (r p (homOfLE (show U ⊓ V ≤ U from inf_le_left))).app F x.1 -
              (r p (homOfLE (show U ⊓ V ≤ V from inf_le_right))).app F x.2)
          ((δ U V p).app F) ∧
        Function.Exact ((δ U V p).app F)
          (fun x : (H (p + 1) (U ⊔ V)).obj F =>
            ((r (p + 1) (homOfLE (show U ≤ U ⊔ V from le_sup_left))).app F x,
              (r (p + 1) (homOfLE (show V ≤ U ⊔ V from le_sup_right))).app F x))) ∧
      (∀ (U V W : Opens X) (p : ℕ),
        δ U V p ≫ r (p + 1) (homOfLE (sup_le_sup inf_le_left inf_le_left)) =
          r p (homOfLE (inf_le_inf inf_le_left inf_le_left)) ≫
            δ (U ⊓ W) (V ⊓ W) p) := by
  let : EnoughInjectives (SheafOfModules.{v} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  let d : ∀ (S : InjectivelyExactSquare (SheafOfModules.{v} (moduleRings X))) (p : ℕ),
      S.X₄.rightDerived p ⟶ S.X₁.rightDerived (p + 1) :=
    fun S p ↦
      { app := fun F ↦ S.boundary F p
        naturality := by
          intro F G f
          exact S.boundary_naturality p f }
  refine ⟨fun U V p ↦ d (sectionSquare X U V) p, ?_, ?_, ?_⟩
  · intro U V F
    exact (sectionSquare X U V).boundary_exact.1 F
  · intro U V F p
    exact (sectionSquare X U V).boundary_exact.2 F p
  · intro U V W p
    let φ : (sectionSquare X U V).toSquare ⟶
        (sectionSquare X (U ⊓ W) (V ⊓ W)).toSquare :=
      { τ₁ := sectionRestriction X (homOfLE (sup_le_sup inf_le_left inf_le_left))
        τ₂ := sectionRestriction X (homOfLE inf_le_left)
        τ₃ := sectionRestriction X (homOfLE inf_le_left)
        τ₄ := sectionRestriction X (homOfLE (inf_le_inf inf_le_left inf_le_left))
        comm₁₂ := sectionRestriction_square X _ _ _ _
        comm₁₃ := sectionRestriction_square X _ _ _ _
        comm₂₄ := sectionRestriction_square X _ _ _ _
        comm₃₄ := sectionRestriction_square X _ _ _ _ }
    apply NatTrans.ext
    funext F
    exact (sectionSquare X U V).boundary_square_naturality p
      (sectionSquare X (U ⊓ W) (V ⊓ W)) φ F

end AlgebraicGeometry.RingedSpace
