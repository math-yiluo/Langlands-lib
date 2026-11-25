/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
import all WeilConjectures.Topology.ConstantSheafLocallyConstantComparison

/-!
# The unit-compatible locally constant description of the constant abelian sheaf

Source: literature/stacks-project/sheaves.tex, Definition 006W and Example 0081.
(blueprint: lem-sc-constant-sheaf-locally-constant-unit-comparison)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace TopCat

/-- The constant abelian sheaf is naturally the group of locally constant maps on opens.

Source: literature/stacks-project/sheaves.tex, Definition 006W and Example 0081.
(blueprint: lem-sc-constant-sheaf-locally-constant-unit-comparison)
Proof: first extract elementwise gluing and separation from the abelian sheaf condition
using the corepresentability of the forgetful functor by the lifted integers. The
subgroups of sections locally in the image of the constant-presheaf unit form a sheaf:
local representatives are stable under restriction, addition on common intersections,
and negation; gluing preserves the local representative property. The unit factors
through this subsheaf. Its sheafification lift followed by the inclusion is the identity,
by uniqueness of sheafification, so every section is locally represented by a constant.
For a point x, the presheaf with value A on opens containing x and the trivial group
elsewhere is a sheaf, directly by gluing. Factoring the constant presheaf map to this
skyscraper sheaf through sheafification proves the unit injective on every open containing
x. This proof does not require the space and coefficient universes to coincide.
Assign to a section at x the value of any local constant representative. On intersections
the injectivity just proved makes this value independent of the representative. The
resulting function is locally constant. Restriction and addition follow by comparing
representatives on a common neighbourhood. Equality of these functions implies local,
hence global, equality of sections. Conversely, the constant sections on the open fibres
of a locally constant function agree on overlaps and glue to a section with that function.
The resulting bijective additive maps are the required additive equivalences; restriction
compatibility was proved pointwise. The local representative of a unit section is its
prescribed value, giving the additional compatibility with the sheafification unit.
The proof reuses the comparison construction of group P3, retaining its hconst equation.
Empty opens are included: separation is vacuous and
the gluing argument works with all fibres empty. -/
theorem constantSheaf_locallyConstant_unit_comparison
    (X : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : Type v) [AddCommGroup A] :
    ∃ e : ∀ U : Opens X,
      AddEquiv (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of A)).1.obj (op U)) (LocallyConstant U A),
      (∀ (U V : Opens X) (hVU : V ≤ U) (s :
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of A)).1.obj (op U)) (x : V),
        e V (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of A)).1.map (homOfLE hVU).op s) x =
            e U s ⟨x.1, hVU x.2⟩) ∧
      (∀ (U : Opens X) (a : A) (x : U),
        e U ((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A))).app (op U) a) x = a) := by
  classical
  let F := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
    (AddCommGrpCat.of A)
  let η := toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A))
  have hloc := constantSheaf_unit_localSurj X A
  have hinj := unit_inj X A
  change (∀ (U : Opens X) (s : F.obj.obj (op U)) (x : U),
    ∃ (V : Opens X) (hVU : V ≤ U), x.1 ∈ V ∧
      ∃ a : A, η.app (op V) a = F.obj.map (homOfLE hVU).op s) at hloc
  change (∀ (U : Opens X) (_x : U), Function.Injective (η.app (op U))) at hinj
  have hη (U V : Opens X) (hVU : V ≤ U) (a : A) :
      F.obj.map (homOfLE hVU).op (η.app (op U) a) = η.app (op V) a := by
    exact (ConcreteCategory.congr_hom (η.naturality (homOfLE hVU).op) a).symm
  have hcomp (U V W : Opens X) (hVU : V ≤ U) (hWV : W ≤ V)
      (s : F.obj.obj (op U)) :
      F.obj.map (homOfLE hWV).op (F.obj.map (homOfLE hVU).op s) =
        F.obj.map (homOfLE (hWV.trans hVU)).op s := by
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    rfl
  have hex (U : Opens X) (s : F.obj.obj (op U)) (x : U) :
      ∃ a : A, ∃ (V : Opens X) (hVU : V ≤ U), x.1 ∈ V ∧
        η.app (op V) a = F.obj.map (homOfLE hVU).op s := by
    obtain ⟨V, hVU, hxV, a, ha⟩ := hloc U s x
    exact ⟨a, V, hVU, hxV, ha⟩
  let val (U : Opens X) (s : F.obj.obj (op U)) (x : U) := (hex U s x).choose
  have hval (U : Opens X) (s : F.obj.obj (op U)) (x : U) := (hex U s x).choose_spec
  have hvalue (U V : Opens X) (hVU : V ≤ U) (s : F.obj.obj (op U))
      (x : V) (a : A) (ha : η.app (op V) a = F.obj.map (homOfLE hVU).op s) :
      val U s ⟨x.1, hVU x.2⟩ = a := by
    obtain ⟨W, hWU, hxW, hw⟩ := hval U s ⟨x.1, hVU x.2⟩
    apply hinj (W ⊓ V) ⟨x.1, hxW, x.2⟩
    calc
      η.app (op (W ⊓ V)) (val U s ⟨x.1, hVU x.2⟩) =
          F.obj.map (homOfLE inf_le_left).op (η.app (op W) _) :=
        (hη W (W ⊓ V) inf_le_left _).symm
      _ = F.obj.map (homOfLE ((inf_le_left : W ⊓ V ≤ W).trans hWU)).op s := by
        rw [hw, hcomp]
      _ = F.obj.map (homOfLE ((inf_le_right : W ⊓ V ≤ V).trans hVU)).op s := rfl
      _ = F.obj.map (homOfLE inf_le_right).op (η.app (op V) a) := by
        rw [ha, hcomp]
      _ = η.app (op (W ⊓ V)) a := hη V (W ⊓ V) inf_le_right a
  have hconst (U : Opens X) (a : A) (x : U) : val U (η.app (op U) a) x = a := by
    exact hvalue U U le_rfl _ x a (by simp)
  have hlocal (U : Opens X) (s : F.obj.obj (op U)) : IsLocallyConstant (val U s) := by
    apply (IsLocallyConstant.iff_exists_open _).2
    intro x
    obtain ⟨V, hVU, hxV, ha⟩ := hval U s x
    refine ⟨{y : U | y.1 ∈ V}, V.isOpen.preimage continuous_subtype_val, hxV, ?_⟩
    intro y hy
    exact hvalue U V hVU s ⟨y.1, hy⟩ (val U s x) ha
  let ev (U : Opens X) (s : F.obj.obj (op U)) : LocallyConstant U A :=
    ⟨val U s, hlocal U s⟩
  have hev_res (U V : Opens X) (hVU : V ≤ U) (s : F.obj.obj (op U)) (x : V) :
      ev V (F.obj.map (homOfLE hVU).op s) x = ev U s ⟨x.1, hVU x.2⟩ := by
    obtain ⟨W, hWV, hxW, a, ha⟩ := hloc V (F.obj.map (homOfLE hVU).op s) x
    have ha' : η.app (op W) a = F.obj.map (homOfLE (hWV.trans hVU)).op s := by
      rw [ha, hcomp]
    exact (hvalue V W hWV _ ⟨x.1, hxW⟩ a ha).trans
      (hvalue U W (hWV.trans hVU) s ⟨x.1, hxW⟩ a ha').symm
  have hev_add (U : Opens X) (s t : F.obj.obj (op U)) :
      ev U (s + t) = ev U s + ev U t := by
    ext x
    obtain ⟨V, hVU, hxV, a, ha⟩ := hloc U s x
    obtain ⟨W, hWU, hxW, b, hb⟩ := hloc U t x
    have hab : η.app (op (V ⊓ W)) (a + b) =
        F.obj.map (homOfLE ((inf_le_left : V ⊓ W ≤ V).trans hVU)).op (s + t) := by
      rw [map_add, map_add]
      congr 1
      · rw [← hη V (V ⊓ W) inf_le_left a, ha, hcomp]
      · rw [← hη W (V ⊓ W) inf_le_right b, hb, hcomp]
    exact (hvalue U (V ⊓ W) ((inf_le_left : V ⊓ W ≤ V).trans hVU) (s + t)
      ⟨x.1, hxV, hxW⟩ (a + b) hab).trans
        (congrArg₂ (· + ·) (hvalue U V hVU s ⟨x.1, hxV⟩ a ha)
          (hvalue U W hWU t ⟨x.1, hxW⟩ b hb)).symm
  have hev_zero (U : Opens X) : ev U 0 = 0 := by
    ext x
    change val U 0 x = 0
    have hc := hconst U 0 x
    simpa using hc
  let e (U : Opens X) : F.obj.obj (op U) →+ LocallyConstant U A :=
    { toFun := ev U
      map_zero' := hev_zero U
      map_add' := hev_add U }
  have hev_inj (U : Opens X) : Function.Injective (e U) := by
    intro s t hst
    apply abelian_section_ext X F U s t
    intro x
    obtain ⟨V, hVU, hxV, a, ha⟩ := hloc U s x
    obtain ⟨W, hWU, hxW, b, hb⟩ := hloc U t x
    have hab : a = b := by
      have hh := congrArg (fun f : LocallyConstant U A ↦ f x) hst
      change val U s x = val U t x at hh
      rw [hvalue U V hVU s ⟨x.1, hxV⟩ a ha,
        hvalue U W hWU t ⟨x.1, hxW⟩ b hb] at hh
      exact hh
    refine ⟨V ⊓ W, (inf_le_left : V ⊓ W ≤ V).trans hVU, ⟨hxV, hxW⟩, ?_⟩
    calc
      F.obj.map (homOfLE ((inf_le_left : V ⊓ W ≤ V).trans hVU)).op s =
          η.app (op (V ⊓ W)) a := by
        rw [← hcomp U V (V ⊓ W) hVU inf_le_left s, ← ha, hη]
      _ = η.app (op (V ⊓ W)) b := congrArg _ hab
      _ = F.obj.map (homOfLE ((inf_le_left : V ⊓ W ≤ V).trans hVU)).op t := by
        rw [← hη W (V ⊓ W) inf_le_right b, hb, hcomp]
  have hev_surj (U : Opens X) : Function.Surjective (e U) := by
    intro f
    let V (a : A) : Opens X :=
      ⟨Subtype.val '' {x : U | f x = a},
        U.isOpen.isOpenMap_subtype_val _ (f.isLocallyConstant.isOpen_fiber a)⟩
    have hVU (a : A) : V a ≤ U := by
      rintro x ⟨y, _, rfl⟩
      exact y.2
    have hVa (a : A) (x : V a) : f ⟨x.1, hVU a x.2⟩ = a := by
      obtain ⟨y, hy, hxy⟩ := x.2
      have heq : (⟨x.1, hVU a x.2⟩ : U) = y := Subtype.ext hxy.symm
      rw [heq]
      exact hy
    have hcover : U ≤ iSup V := by
      intro x hx
      exact Opens.mem_iSup.mpr ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl, rfl⟩⟩
    have hc : Presheaf.IsCompatible F.obj V (fun a ↦ η.app (op (V a)) a) := by
      intro a b
      apply abelian_section_ext X F (V a ⊓ V b)
      intro x
      have hab : a = b :=
        (hVa a ⟨x.1, x.2.1⟩).symm.trans (hVa b ⟨x.1, x.2.2⟩)
      refine ⟨V a ⊓ V b, le_rfl, x.2, ?_⟩
      change F.obj.map (𝟙 (op (V a ⊓ V b))) _ =
        F.obj.map (𝟙 (op (V a ⊓ V b))) _
      rw [F.obj.map_id]
      change F.obj.map (homOfLE inf_le_left).op (η.app (op (V a)) a) =
        F.obj.map (homOfLE inf_le_right).op (η.app (op (V b)) b)
      rw [hη, hη, hab]
    obtain ⟨s, hs⟩ := abelian_gluing X F V U hVU hcover
      (fun a ↦ η.app (op (V a)) a) hc
    refine ⟨s, ?_⟩
    apply LocallyConstant.ext
    intro x
    let y : V (f x) := ⟨x.1, ⟨x, rfl, rfl⟩⟩
    exact hvalue U (V (f x)) (hVU (f x)) s y (f x) (hs (f x)).symm
  refine ⟨fun U ↦ AddEquiv.ofBijective (e U) ⟨hev_inj U, hev_surj U⟩, ?_⟩
  constructor
  · intro U V hVU s x
    exact hev_res U V hVU s x
  · intro U a x
    exact hconst U a x

end TopCat
