/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Finite pushforward and extension by zero

Consider a cartesian square of schemes

```
U --jX--> X
|         |
v         v̄
↓         ↓
V --jY--> Y
```

with `jX`, `jY` open immersions and `v̄` finite. This file constructs the comparison map
`β : (jY)_! v_* G ⟶ v̄_* (jX)_! G` of étale sheaves and proves that it is an isomorphism.

The map `β` is the transpose under `(jY)_! ⊣ jY^*` of the isomorphism
`v_* G ≅ v_* jX^* (jX)_! G ≅ jY^* v̄_* (jX)_! G`, made of the unit of `(jX)_! ⊣ jX^*` and the
inverse of the finite base change isomorphism `jY^* v̄_* ≅ v_* jX^*`
(`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`).

That `β` is an isomorphism is checked on geometric points `s` of `Y`. If `s` lies in `V`,
the stalk of `β` at `s` is a stalk of `jY^* β`, which is invertible since it is
`jY^* (jY)_!` of the isomorphism above followed by `jY^*` of the counit of
`(jY)_! ⊣ jY^*`. If `s` does not lie in `V`, both `s^* (jY)_! v_* G` and
`s^* v̄_* (jX)_! G ≅ v̄'_* s'^* (jX)_! G` vanish (finite base change along `s`), since the
ranges of `s` and `jY`, resp. of `s'` and `jX`, are disjoint.

The extension by zero itself is `AlgebraicGeometry.Etale.openImmersionLowerShriek`,
`(j)_!open[A]`, of `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, left
adjoint to `j^*` (`AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction`);
we add its description on geometric stalks.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekCompUliftSheafFiberIso`: the stalk of
  `j_! F` at a geometric point `t ≫ j` of `X` lying in `U` is the stalk of `F` at `t`.
- `AlgebraicGeometry.Etale.finiteOpenComparison`: the comparison map
  `β : (jY)_! v_* ⟶ v̄_* (jX)_!` (blueprint: `lemma-normalization-constant-sheaf--1`).

## Main statements

- `AlgebraicGeometry.Etale.isZero_uliftSheafFiber_openImmersionLowerShriek_obj`: the stalk
  of `j_! F` at a geometric point outside `U` vanishes
  (blueprint: `proposition-extension-zero-restriction-closed-subscheme--7`).
- `AlgebraicGeometry.Etale.isIso_finiteOpenComparison_app`: `β` is an isomorphism at every
  sheaf `G` (blueprint: `lemma-normalization-constant-sheaf--1`).
- `AlgebraicGeometry.Etale.isIso_finiteOpenComparison`: `β` is a natural isomorphism
  (blueprint: `lemma-normalization-constant-sheaf--1`).
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

noncomputable section

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-! ### Auxiliary lemmas -/

/-- If the closed point of `Spec K` is not mapped into the range of `j`, then the ranges of
`j` and of `s : Spec K ⟶ X` are disjoint. -/
lemma disjoint_range_of_closedPoint_not_mem {U X : Scheme.{u}} (j : U ⟶ X) {K : Type u}
    [Field K] (s : Spec (.of K) ⟶ X)
    (hs : s.base (IsLocalRing.closedPoint K) ∉ Set.range j.base) :
    Disjoint (Set.range j.base) (Set.range s.base) := by
  rw [Set.disjoint_right]
  rintro _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]

/-! ### Stalks of the extension by zero -/

section Stalk

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

omit [HasSmallSiteSheafify A] in
/-- **The stalk of the extension by zero inside `U`.** For a geometric point `t` of `U`, the
stalk of `j_! F` at `t ≫ j` is the stalk of `F` at `t`, naturally in `F`: it is the stalk at
`t` of `j^* j_! F ≅ F`.
(blueprint: `proposition-extension-zero-restriction-closed-subscheme--7`,
`lem-weil-pbc-extension-by-zero-stalks`) -/
def Etale.openImmersionLowerShriekCompUliftSheafFiberIso {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ U) :
    (j)_!open[A] ⋙ ((pointSmallEtale (t ≫ j)).ulift.{u + 1}).sheafFiber ≅
      ((pointSmallEtale t).ulift.{u + 1}).sheafFiber :=
  Functor.isoWhiskerLeft (j)_!open[A] (Etale.upperStarCompUliftSheafFiberIso A j t).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit).symm _ ≪≫
    Functor.leftUnitor _

omit [HasSmallSiteSheafify A] in
/-- **The stalk of the extension by zero outside `U` vanishes**: for a geometric point `s`
of `X` not lying in `U`, the stalk of `j_! F` at `s` is zero. It is the stalk of
`s^* j_! F`, which vanishes since the ranges of `s` and `j` are disjoint.
(blueprint: `proposition-extension-zero-restriction-closed-subscheme--7`,
`lem-weil-pbc-extension-by-zero-stalks`) -/
lemma Etale.isZero_uliftSheafFiber_openImmersionLowerShriek_obj {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s.base (IsLocalRing.closedPoint Ω) ∉ Set.range j.base)
    (F : Sheaf U.smallEtaleTopology A) :
    IsZero (((pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj ((j)_!open[A].obj F)) := by
  have hz := Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A j s
    (disjoint_range_of_closedPoint_not_mem j s hs) F
  have := ((Etale.upperStarCompUliftSheafFiberIso A s (𝟙 _)).app ((j)_!open[A].obj F))
  rw [id_comp] at this
  exact (Functor.map_isZero ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber
    hz).of_iso this.symm

end Stalk

/-! ### The comparison map -/

section Comparison

variable {U X V Y : Scheme.{u}} {jX : U ⟶ X} {v : U ⟶ V} {vbar : X ⟶ Y} {jY : V ⟶ Y}
  [IsOpenImmersion jX] [IsOpenImmersion jY] [IsFinite vbar]

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The isomorphism `v_* ⟶ jY^* v̄_* (jX)_!` underlying the finite-open comparison map: the
unit of `(jX)_! ⊣ jX^*` followed by the inverse of the finite base change isomorphism
`jY^* v̄_* ≅ v_* jX^*` (`Etale.isIso_baseChangeMap_of_isFinite`). -/
def Etale.finiteOpenComparisonAux (sq : IsPullback jX v vbar jY) :
    (v)_*[A] ⟶ (jX)_!open[A] ⋙ (vbar)_*[A] ⋙ (jY)^*[A] :=
  have := Etale.isIso_baseChangeMap_of_isFinite A sq
  Functor.whiskerRight (Etale.openImmersionLowerShriekUpperStarAdjunction A jX).unit (v)_*[A] ≫
    Functor.whiskerLeft (jX)_!open[A] (inv (Etale.baseChangeMap A sq.toCommSq))

instance Etale.isIso_finiteOpenComparisonAux (sq : IsPullback jX v vbar jY) :
    IsIso (Etale.finiteOpenComparisonAux A sq) := by
  have := Etale.isIso_baseChangeMap_of_isFinite A sq
  dsimp [Etale.finiteOpenComparisonAux]
  infer_instance

/-- **The finite-open comparison map.** For a cartesian square
```
U --jX--> X
|         |
v         v̄
↓         ↓
V --jY--> Y
```
with `jX`, `jY` open immersions and `v̄` finite, the natural transformation
`β : (jY)_! v_* ⟶ v̄_* (jX)_!`, the transpose under `(jY)_! ⊣ jY^*` of the isomorphism
`v_* G ≅ jY^* v̄_* (jX)_! G` given by `jX^* (jX)_! G ≅ G` and finite base change.
(blueprint: `lemma-normalization-constant-sheaf--1`) -/
def Etale.finiteOpenComparison (sq : IsPullback jX v vbar jY) :
    (v)_*[A] ⋙ (jY)_!open[A] ⟶ (jX)_!open[A] ⋙ (vbar)_*[A] :=
  Functor.whiskerRight (Etale.finiteOpenComparisonAux A sq) (jY)_!open[A] ≫
    Functor.whiskerLeft ((jX)_!open[A] ⋙ (vbar)_*[A])
      (Etale.openImmersionLowerShriekUpperStarAdjunction A jY).counit

/-- The restriction `jY^* β` of the finite-open comparison map to `V` is an isomorphism. -/
lemma Etale.isIso_upperStar_map_finiteOpenComparison_app (sq : IsPullback jX v vbar jY)
    (G : Sheaf U.smallEtaleTopology A) :
    IsIso ((jY)^*[A].map ((Etale.finiteOpenComparison A sq).app G)) := by
  dsimp [Etale.finiteOpenComparison]
  rw [Functor.map_comp]
  infer_instance

/-- The pullback `s^* β` of the finite-open comparison map to a geometric point `s` of `Y`
outside `V` is an isomorphism, both sides being zero. -/
lemma Etale.isIso_upperStar_point_map_finiteOpenComparison_app
    (sq : IsPullback jX v vbar jY) (G : Sheaf U.smallEtaleTopology A) {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ Y) (hs : s.base (IsLocalRing.closedPoint Ω) ∉ Set.range jY.base) :
    IsIso ((s)^*[A].map ((Etale.finiteOpenComparison A sq).app G)) := by
  have hdisj := disjoint_range_of_closedPoint_not_mem jY s hs
  have h₁ : IsZero ((s)^*[A].obj ((jY)_!open[A].obj ((v)_*[A].obj G))) :=
    Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A jY s hdisj _
  have hsq := IsPullback.of_hasPullback vbar s
  have := Etale.isIso_baseChangeMap_of_isFinite A hsq
  have hdisj' : Disjoint (Set.range jX.base) (Set.range (pullback.fst vbar s).base) := by
    rw [Set.disjoint_iff]
    rintro _ ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    refine hdisj.ne_of_mem ⟨v.base a, rfl⟩ ⟨(pullback.snd vbar s).base b, rfl⟩ ?_
    rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply, ← hb,
      ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have h₂ : IsZero ((s)^*[A].obj ((vbar)_*[A].obj ((jX)_!open[A].obj G))) :=
    (Functor.map_isZero (pullback.snd vbar s)_*[A]
      (Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A
        jX (pullback.fst vbar s) hdisj' G)).of_iso
      (asIso ((Etale.baseChangeMap A hsq.toCommSq).app ((jX)_!open[A].obj G)))
  exact ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

/-- **The finite-open comparison map is an isomorphism** at every sheaf `G` on `U`. It is
checked on geometric stalks: at a point of `V` the stalk is a stalk of the isomorphism
`jY^* β` (`Etale.isIso_upperStar_map_finiteOpenComparison_app`), and at a point `s` outside
`V` it is a stalk of `s^* β`, a morphism between zero objects
(`Etale.isIso_upperStar_point_map_finiteOpenComparison_app`).

The blueprint also describes the inverse explicitly on sections and on geometric stalks;
here only the existence of the inverse is recorded.
(blueprint: `lemma-normalization-constant-sheaf--1`) -/
lemma Etale.isIso_finiteOpenComparison_app (sq : IsPullback jX v vbar jY)
    (G : Sheaf U.smallEtaleTopology A) :
    IsIso ((Etale.finiteOpenComparison A sq).app G) := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
  let s := Y.algClosurePoint x
  by_cases hs : s.base (IsLocalRing.closedPoint _) ∈ Set.range jY.base
  · have h := Etale.isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map A jY _
      (Etale.isIso_upperStar_map_finiteOpenComparison_app A sq G)
      (IsOpenImmersion.lift jY s (Scheme.range_base_subset_of_closedPoint_mem s hs))
    rw [IsOpenImmersion.lift_fac] at h
    exact h
  · have h := Etale.isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map A s _
      (Etale.isIso_upperStar_point_map_finiteOpenComparison_app A sq G s hs) (𝟙 _)
    rw [id_comp] at h
    exact h

/-- **Finite pushforward commutes with extension by zero**: for a cartesian square with
`jX`, `jY` open immersions and `v̄` finite, the comparison map
`β : (jY)_! v_* ⟶ v̄_* (jX)_!` of `Etale.finiteOpenComparison` is a natural isomorphism;
naturality in `G` is built into the construction of `β` as a natural transformation.

The compatibilities of `β` with identity and composite finite maps and with base change,
also part of the blueprint statement, are not formalised here.
(blueprint: `lemma-normalization-constant-sheaf--1`) -/
lemma Etale.isIso_finiteOpenComparison (sq : IsPullback jX v vbar jY) :
    IsIso (Etale.finiteOpenComparison A sq) :=
  have := Etale.isIso_finiteOpenComparison_app A sq
  NatIso.isIso_of_isIso_app _

end Comparison

end AlgebraicGeometry

end
