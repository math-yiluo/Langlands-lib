/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.Topology.ModuleObjectOpenDescent

/-!
# Glueing morphisms and sheaves of modules along an open covering

Source: Stacks Project, Sheaves, Section 00AK, Lemmas 04TN, 00AL and 00AM
(blueprint: lem-weil-pbc-glue-sheaves-of-modules).
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

private theorem module_hom_eq_of_over_eq
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤)
    (F G : SheafOfModules.{max u v} (moduleRings X)) (α β : F ⟶ G)
    (h : ∀ i : I, α.over (U i) = β.over (U i)) : α = β := by
  let S : TopCat.Sheaf (Type (max u v)) X.toPresheafedSpace.carrier :=
    (sheafCompose _ (forget AddCommGrpCat.{max u v})).obj
      ((SheafOfModules.toSheaf (moduleRings X)).obj G)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply S.eq_of_locally_eq' (fun i ↦ W.unop ⊓ U i) W.unop
    (fun i ↦ homOfLE inf_le_left)
  · simp only [← inf_iSup_eq, hcover, inf_top_eq, le_refl]
  · intro i
    change G.val.map (homOfLE inf_le_left).op (α.val.app W x) =
      G.val.map (homOfLE inf_le_left).op (β.val.app W x)
    rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
    have hi := congrArg (fun f ↦ f.val.app
      (op (Over.mk (homOfLE (inf_le_right : W.unop ⊓ U i ≤ U i))))) (h i)
    exact congrArg (fun f ↦ f (F.val.map (homOfLE inf_le_left).op x)) hi

set_option backward.isDefEq.respectTransparency false in
private theorem module_hom_gluing_exists
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤)
    (F G : SheafOfModules.{max u v} (moduleRings X))
    (φ : ∀ i : I, F.over (U i) ⟶ G.over (U i))
    (hφ : ∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      (φ i).val.app (op (Over.mk (homOfLE hi))) =
        (φ j).val.app (op (Over.mk (homOfLE hj)))) :
    ∃ ψ : F ⟶ G, ∀ i : I, ψ.over (U i) = φ i := by
  classical
  let S : TopCat.Sheaf (Type (max u v)) X.toPresheafedSpace.carrier :=
    (sheafCompose _ (forget AddCommGrpCat.{max u v})).obj
      ((SheafOfModules.toSheaf (moduleRings X)).obj G)
  let a (i : I) (W : Opens X) (hi : W ≤ U i) :
      F.val.obj (op W) ⟶ G.val.obj (op W) :=
    (φ i).val.app (op (Over.mk (homOfLE hi)))
  have nat (i : I) (A B : Opens X) (ha : A ≤ U i) (hb : B ≤ U i)
      (hab : B ≤ A) (x : F.val.obj (op A)) :
      a i B hb (F.val.map (homOfLE hab).op x) =
        G.val.map (homOfLE hab).op (a i A ha x) := by
    exact PresheafOfModules.naturality_apply (φ i).val
      (Over.homMk (U := Over.mk (homOfLE hb))
        (V := Over.mk (homOfLE ha)) (homOfLE hab)).op x
  have ex (W : Opens X) (x : F.val.obj (op W)) :
      ∃! y : G.val.obj (op W), ∀ i : I,
        G.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op y =
          a i (W ⊓ U i) inf_le_right
            (F.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op x) := by
    apply S.existsUnique_gluing' (fun i ↦ W ⊓ U i) W
      (fun i ↦ homOfLE inf_le_left)
    · simp only [← inf_iSup_eq, hcover, inf_top_eq, le_refl]
    · intro i j
      change G.val.map (homOfLE inf_le_left).op
          (a i (W ⊓ U i) inf_le_right (F.val.map (homOfLE inf_le_left).op x)) =
        G.val.map (homOfLE inf_le_right).op
          (a j (W ⊓ U j) inf_le_right (F.val.map (homOfLE inf_le_left).op x))
      rw [← nat i _ _ inf_le_right (inf_le_left.trans inf_le_right) inf_le_left,
        ← nat j _ _ inf_le_right (inf_le_right.trans inf_le_right) inf_le_right]
      simp only [← PresheafOfModules.map_comp_apply]
      rw [show a i ((W ⊓ U i) ⊓ (W ⊓ U j)) (inf_le_left.trans inf_le_right) =
        a j ((W ⊓ U i) ⊓ (W ⊓ U j)) (inf_le_right.trans inf_le_right) from
        hφ i j _ _ _]
      rfl
  let t (W : Opens X) (x : F.val.obj (op W)) : G.val.obj (op W) := (ex W x).choose
  have ht (W : Opens X) (x : F.val.obj (op W)) (i : I) :
      G.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op (t W x) =
        a i (W ⊓ U i) inf_le_right
          (F.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op x) :=
    (ex W x).choose_spec.1 i
  have sep (W : Opens X) (y z : G.val.obj (op W))
      (h : ∀ i : I, G.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op y =
        G.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op z) : y = z := by
    exact S.eq_of_locally_eq' (fun i ↦ W ⊓ U i) W
      (fun i ↦ homOfLE inf_le_left)
      (by simp only [← inf_iSup_eq, hcover, inf_top_eq, le_refl]) y z h
  have tadd (W : Opens X) (x y : F.val.obj (op W)) :
      t W (x + y) = t W x + t W y := by
    apply sep
    intro i
    rw [ht]
    simp only [map_add, ht]
  have tsmul (W : Opens X) (r : (moduleRings X).obj.obj (op W))
      (x : F.val.obj (op W)) : t W (r • x) = r • t W x := by
    apply sep
    intro i
    rw [ht, F.val.map_smul, G.val.map_smul, ht]
    exact (a i (W ⊓ U i) inf_le_right).hom.map_smul _ _
  have tnat (A B : Opens X) (hab : B ≤ A) (x : F.val.obj (op A)) :
      t B (F.val.map (homOfLE hab).op x) =
        G.val.map (homOfLE hab).op (t A x) := by
    apply sep
    intro i
    rw [ht]
    have e : (homOfLE hab).op ≫ (homOfLE (inf_le_left : B ⊓ U i ≤ B)).op =
        (homOfLE (inf_le_left : A ⊓ U i ≤ A)).op ≫
          (homOfLE (inf_le_inf hab (le_refl (U i)))).op := Subsingleton.elim _ _
    rw [← G.val.map_comp_apply, e, G.val.map_comp_apply, ht]
    rw [← nat i _ _ inf_le_right inf_le_right (inf_le_inf hab (le_refl (U i)))]
    simp only [← PresheafOfModules.map_comp_apply]
    rfl
  let ψ : F ⟶ G :=
    { val :=
        { app := fun W ↦ ModuleCat.ofHom
            { toFun := t W.unop
              map_add' := tadd W.unop
              map_smul' := tsmul W.unop }
          naturality := by
            intro A B f
            ext x
            exact tnat A.unop B.unop f.unop.le x } }
  refine ⟨ψ, ?_⟩
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  change t W.unop.left x = a i W.unop.left W.unop.hom.le x
  apply sep
  intro j
  rw [ht, ← nat i _ _ W.unop.hom.le (inf_le_left.trans W.unop.hom.le) inf_le_left]
  rw [show a j (W.unop.left ⊓ U j) inf_le_right =
      a i (W.unop.left ⊓ U j) (inf_le_left.trans W.unop.hom.le) from hφ j i _ _ _]

/-- Glueing morphisms and sheaves of modules on an open cover.
Restrictions to `U` use the localized site `Over U`: its objects are precisely the
opens `W ≤ U`. Restrictions of local modules use `SheafOfModules.overMap`.
Equality of maps on overlaps is expressed at every such open `W`, so no choices
of comparison isomorphisms for iterated restriction enter the statement.

Source: Stacks Project, Sheaves, Section 00AK, Lemmas 04TN, 00AL and 00AM
(blueprint: lem-weil-pbc-glue-sheaves-of-modules).
Proof (using situation-conventions throughout):
1. For `s ∈ F(W)`, glue the sections `φᵢ(s|W ∩ Uᵢ)` in `G` using overlap agreement.
2. Check naturality, additivity and O-linearity after restriction to `W ∩ Uᵢ`;
   separation of `G` makes these local identities global.
3. At `W ≤ Uᵢ` this construction equals `φᵢ`; uniqueness of glued sections proves
   uniqueness of the morphism and the stated equality criterion for two morphisms.
4. The cocycle gives `φᵢᵢ = id`. Define `H(W)` as compatible families in the product
   of `Fᵢ(W ∩ Uᵢ)`. Linearity makes this an O(W)-submodule; restriction is componentwise.
5. Glue families componentwise using each `Fᵢ`'s sheaf axiom; separation checks overlap
   compatibility and uniqueness, giving the sheaf axiom for `H`.
6. On `W ≤ Uᵢ`, projection to component `i` is a linear isomorphism: all other
   components are recovered by `φᵢⱼ` from that component, and the cocycle ensures
   these recovered components agree. These maps and inverses commute with restriction.
7. The defining equations of compatible families give `φᵢ ≫ φᵢⱼ = φⱼ` on overlaps. -/
theorem glue_sheaves_of_modules
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤) :
    (∀ (F G : SheafOfModules.{max u v} (moduleRings X))
      (φ : ∀ i : I, F.over (U i) ⟶ G.over (U i)),
      (∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
        (φ i).val.app (op (Over.mk (homOfLE hi))) =
          (φ j).val.app (op (Over.mk (homOfLE hj)))) →
      ∃! ψ : F ⟶ G, ∀ i : I, ψ.over (U i) = φ i) ∧
    (∀ (F G : SheafOfModules.{max u v} (moduleRings X)) (α β : F ⟶ G),
      (∀ i : I, α.over (U i) = β.over (U i)) → α = β) ∧
    (∀ (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
      (φij : ∀ i j : I,
        (SheafOfModules.overMap (moduleRings X) (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj
            (Fi i) ≅
          (SheafOfModules.overMap (moduleRings X)
            (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j)),
      (∀ (i j k : I) (W : Opens X)
        (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
        (φij i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
          (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
            (φij j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) →
      ∃ (H : SheafOfModules.{max u v} (moduleRings X))
        (φi : ∀ i : I, H.over (U i) ≅ Fi i),
        ∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
          (φi i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
            (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) =
              (φi j).hom.val.app (op (Over.mk (homOfLE hj)))) := by
  refine ⟨?_, ?_, module_object_open_descent X I U hcover⟩
  · intro F G φ hφ
    obtain ⟨ψ, hψ⟩ := module_hom_gluing_exists X I U hcover F G φ hφ
    refine ⟨ψ, hψ, ?_⟩
    intro χ hχ
    exact module_hom_eq_of_over_eq X I U hcover F G χ ψ
      (fun i ↦ (hχ i).trans (hψ i).symm)
  · exact module_hom_eq_of_over_eq X I U hcover

end AlgebraicGeometry
