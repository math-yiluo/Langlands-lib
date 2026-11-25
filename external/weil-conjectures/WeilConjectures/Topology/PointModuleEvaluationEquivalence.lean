/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Modules on a one-point ringed space

Source: Stacks Project, Sheaves, Tags 009A (4) and 006U; the one-point
identification used by Cohomology, Section 20.44, Tag 0B6A.
(blueprint: lem-pc-point-module-evaluation-equivalence)

Evaluation on the whole space identifies module sheaves on a singleton ringed
space with modules over its global ring. The proof constructs a module sheaf
from an ordinary module using functions on proofs that an open contains the point.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
noncomputable section
namespace AlgebraicGeometry.RingedSpace

variable (Y : RingedSpace.{u}) [Unique Y]

private theorem topLE (U : Opens Y) (h : (default : Y) ∈ U) : ⊤ ≤ U := by
  intro x _
  simpa only [Subsingleton.elim x default] using h

private abbrev PointSections (M : ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤)))
    (U : Opens Y) := PLift ((default : Y) ∈ U) → M

private noncomputable instance pointSectionsModule
    (M : ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) (U : Opens Y) :
    Module ((moduleRings Y).obj.obj (op U)) (PointSections Y M U) :=
  letI (h : PLift ((default : Y) ∈ U)) : Module ((moduleRings Y).obj.obj (op U)) M :=
    Module.compHom M ((moduleRings Y).obj.map (homOfLE (topLE Y U h.down)).op).hom
  inferInstanceAs (Module ((moduleRings Y).obj.obj (op U))
    (∀ _ : PLift ((default : Y) ∈ U), M))

private abbrev pointPresheaf (M : ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) :
    (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (PointSections Y M U.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := fun s h ↦ s ⟨f.unop.le h.down⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable instance pointPresheafModule
    (M : ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) (U : (Opens Y)ᵒᵖ) :
    Module ((moduleRings Y).obj.obj U) ((pointPresheaf Y M).obj U) :=
  pointSectionsModule Y M U.unop

private theorem pointPresheaf_smul
    (M : ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤)))
    {U V : (Opens Y)ᵒᵖ} (f : U ⟶ V) (r : (moduleRings Y).obj.obj U)
    (s : (pointPresheaf Y M).obj U) :
    (pointPresheaf Y M).map f (r • s) =
      (moduleRings Y).obj.map f r • (pointPresheaf Y M).map f s := by
  funext h
  change ((moduleRings Y).obj.map
      (homOfLE (topLE Y U.unop (f.unop.le h.down))).op r) • s _ =
    ((moduleRings Y).obj.map (homOfLE (topLE Y V.unop h.down)).op
      ((moduleRings Y).obj.map f r)) • s _
  rw [← RingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem pointPresheaf_isSheaf
    (M : ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y) (pointPresheaf Y M) := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hsf
  choose index index_spec using fun h : PLift ((default : Y) ∈ iSup U) ↦
    Opens.mem_iSup.mp h.down
  let s : PointSections Y M (iSup U) := fun h ↦ sf (index h) ⟨index_spec h⟩
  refine ⟨s, ?_, ?_⟩
  · intro i
    funext h
    exact congrFun (hsf (index ⟨(Opens.leSupr U i).le h.down⟩) i)
      ⟨⟨index_spec ⟨(Opens.leSupr U i).le h.down⟩, h.down⟩⟩
  · intro t ht
    funext h
    exact congrFun (ht (index h)) ⟨index_spec h⟩

private noncomputable def pointModule
    (M : ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) :
    SheafOfModules.{u} (moduleRings Y) where
  val := PresheafOfModules.ofPresheaf (pointPresheaf Y M)
    (fun {_ _} f r s ↦ pointPresheaf_smul Y M f r s)
  isSheaf := pointPresheaf_isSheaf Y M

private noncomputable def pointModuleGlobalIso
    (M : ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) :
    (globalSectionsFunctor Y).obj (pointModule Y M) ≅ M := by
  apply LinearEquiv.toModuleIso
  refine { toFun := fun s ↦ s ⟨by trivial⟩
           invFun := fun m _ ↦ m
           left_inv := fun _ ↦ rfl
           right_inv := fun _ ↦ rfl
           map_add' := fun _ _ ↦ rfl
           map_smul' := ?_ }
  intro r s
  change (moduleRings Y).obj.map (𝟙 (op ⊤)) r • s _ = r • s _
  simp

private theorem opens_cases (U : Opens Y) : U = ⊤ ∨ U = ⊥ := by
  classical
  by_cases h : (default : Y) ∈ U
  · exact Or.inl (le_antisymm le_top (topLE Y U h))
  · right
    apply le_antisymm _ bot_le
    intro x hx
    exact (h (by simpa only [Subsingleton.elim x default] using hx)).elim

omit [Unique Y] in
private theorem empty_subsingleton (M : SheafOfModules.{u} (moduleRings Y)) :
    Subsingleton (M.val.obj (op ⊥)) := by
  let F : Y.carrier.Sheaf AddCommGrpCat := ⟨M.val.presheaf, M.isSheaf⟩
  exact AddCommGrpCat.subsingleton_of_isZero F.isTerminalOfEmpty.isZero

private noncomputable def pointHom
    {M N : SheafOfModules.{u} (moduleRings Y)}
    (f : (globalSectionsFunctor Y).obj M ⟶ (globalSectionsFunctor Y).obj N) : M ⟶ N := by
  classical
  refine ⟨{ app := fun U ↦ ?_, naturality := ?_ }⟩
  · exact if h : U = op ⊤ then by subst U; exact f else 0
  · intro U V g
    rcases opens_cases Y U.unop with hU | hU <;>
      rcases opens_cases Y V.unop with hV | hV
    · have hu : U = op ⊤ := congrArg op hU
      have hv : V = op ⊤ := congrArg op hV
      subst U; subst V
      have hg : g = 𝟙 (op ⊤) := Subsingleton.elim _ _
      subst g
      simp only [PresheafOfModules.map_id]
      ext s
      rfl
    · have hv : V = op ⊥ := congrArg op hV
      subst V
      have := empty_subsingleton Y N
      ext
      apply Subsingleton.elim (α := N.val.obj (op ⊥))
    · have hbad : (default : Y) ∈ (⊥ : Opens Y) := by
        rw [← hU]
        exact g.unop.le (by rw [hV]; trivial)
      exact hbad.elim
    · have hv : V = op ⊥ := congrArg op hV
      subst V
      have := empty_subsingleton Y N
      ext
      apply Subsingleton.elim (α := N.val.obj (op ⊥))

private theorem pointEvaluation_full : (globalSectionsFunctor Y).Full := by
  classical
  constructor
  intro M N f
  refine ⟨pointHom Y f, ?_⟩
  change (if _ : op ⊤ = op ⊤ then _ else _) = f
  simp

private theorem pointEvaluation_faithful : (globalSectionsFunctor Y).Faithful := by
  constructor
  intro M N f g h
  ext U s
  rcases opens_cases Y U.unop with hU | hU
  · have hu : U = op ⊤ := congrArg op hU
    subst U
    exact congrArg (fun k ↦ k s) h
  · have hu : U = op ⊥ := congrArg op hU
    subst U
    have := empty_subsingleton Y N
    exact Subsingleton.elim _ _

/-- Evaluation at the whole space is an equivalence for a one-point ringed space.
Source: Stacks Project, Sheaves, Tags 009A (4) and 006U; the identification of
one-point module sheaves used in Cohomology, Section 20.44, Tag 0B6A.
(blueprint: lem-pc-point-module-evaluation-equivalence)

Proof: every open is either the whole point or empty. A module M over the global
ring gives the sheaf with sections `PLift (default ∈ U) → M`; if the point lies in U,
the inclusion of the whole space into U transports the scalar action, and otherwise
this section module is zero. Restrictions precompose membership proofs. On a cover,
compatibility identifies the values on members containing the point, giving a unique
gluing; on an open missing the point there is exactly one section. Evaluation of
this sheaf is linearly isomorphic to M by evaluation at the unique membership proof,
so evaluation is essentially surjective. A linear map on global sections extends
by that map on the whole space and by zero on the empty open. Naturality is immediate
when both opens are the whole space; otherwise the target is empty and its module
is zero by the sheaf condition for the empty covering. This proves fullness.
Two sheaf morphisms agreeing globally agree on the whole space and, by the same
zero-module observation, on the empty open, proving faithfulness. -/
theorem globalSectionsFunctor_isEquivalence_of_unique :
    (globalSectionsFunctor Y).IsEquivalence := by
  have := pointEvaluation_full Y
  have := pointEvaluation_faithful Y
  have : (globalSectionsFunctor Y).EssSurj :=
    ⟨fun M ↦ ⟨pointModule Y M, ⟨pointModuleGlobalIso Y M⟩⟩⟩
  exact {}

end AlgebraicGeometry.RingedSpace
