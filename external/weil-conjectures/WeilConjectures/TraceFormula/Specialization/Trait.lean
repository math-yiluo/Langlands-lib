/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!

# The trait `Spec k'⟦t⟧`

For a field `k'`, the power series ring `k'⟦t⟧` is a complete discrete valuation ring, so
`S = Spec k'⟦t⟧` (`AlgebraicGeometry.trait`) is a trait: its closed point is `Spec k'`
(`AlgebraicGeometry.traitClosedPoint`, `t ↦ 0`) and its generic point is the spectrum of the
field of Laurent series `Frac k'⟦t⟧`. When `k'` is separably closed, `k'⟦t⟧` is henselian (it is
complete) with separably closed residue field, so `S` is a *strictly henselian* trait, the base of
the nearby cycles functors of SGA 7 XIII. A geometric generic point of `S` is
`Spec Ω → S` with `Ω = (Frac k'⟦t⟧)^alg` (`AlgebraicGeometry.traitGenericPoint`).

In Varshavsky's specialization to the normal cone (*Lefschetz–Verdier trace formula and a
generalization of a theorem of Fujiwara*, §1.4–§2) the trait maps to the affine line over the base
field `k` by the coordinate `t` (`AlgebraicGeometry.traitToAffineLine`), sending the closed
point to the origin (`AlgebraicGeometry.traitClosedPoint_traitToAffineLine`); the deformation to
the normal cone is then base changed along this map.

None of the henselian properties are formalised here; only the schemes and morphisms are.

## Main definitions

- `AlgebraicGeometry.trait`: the trait `S = Spec k'⟦t⟧`.
- `AlgebraicGeometry.traitClosedPoint`: the closed point `Spec k' ⟶ S`.
- `AlgebraicGeometry.traitGenericField`, `AlgebraicGeometry.traitGenericPoint`: the geometric
  generic point `Spec Ω ⟶ S`.
- `AlgebraicGeometry.traitToAffineLine`: the coordinate `t : S ⟶ 𝔸¹_k`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

section Trait

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The trait `S = Spec k'⟦t⟧`. If `k'` is separably closed, it is a strictly henselian trait. -/
noncomputable abbrev trait : Scheme.{u} :=
  Spec (.of (PowerSeries k'))

/-- The closed point `Spec k' ⟶ Spec k'⟦t⟧`, given by the constant coefficient `t ↦ 0`. -/
noncomputable def traitClosedPoint : Spec (.of k') ⟶ trait k' :=
  Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k')))

/-- The field `Ω = (Frac k'⟦t⟧)^alg` of the geometric generic point of the trait `Spec k'⟦t⟧`. -/
abbrev traitGenericField : Type u :=
  AlgebraicClosure (FractionRing (PowerSeries k'))

/-- The geometric generic point `Spec Ω ⟶ Spec k'⟦t⟧`, `Ω = (Frac k'⟦t⟧)^alg`. -/
noncomputable def traitGenericPoint : Spec (.of (traitGenericField k')) ⟶ trait k' :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k') (traitGenericField k')))

/-- The structure morphism `Spec k'⟦t⟧ ⟶ Spec k`. -/
noncomputable def traitToBase : trait k' ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k')))

/-- The coordinate `t : Spec k'⟦t⟧ ⟶ 𝔸¹_k`, over the structure morphism
`Spec k'⟦t⟧ ⟶ Spec k`. -/
noncomputable def traitToAffineLine : trait k' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
  AffineSpace.homOfVector (traitToBase k k')
    fun _ ↦ (Scheme.ΓSpecIso (.of (PowerSeries k'))).inv PowerSeries.X

@[reassoc (attr := simp)]
lemma traitToAffineLine_over :
    traitToAffineLine k k' ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) =
      traitToBase k k' :=
  AffineSpace.homOfVector_over _ _

/-- The closed point of the trait lies over `Spec k' ⟶ Spec k`. -/
@[reassoc]
lemma traitClosedPoint_traitToBase :
    traitClosedPoint k' ≫ traitToBase k k' =
      Spec.map (CommRingCat.ofHom (algebraMap k k')) := by
  rw [traitClosedPoint, traitToBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- The coordinate `t` maps the closed point of the trait to the origin of `𝔸¹_k`. -/
@[reassoc]
lemma traitClosedPoint_traitToAffineLine :
    traitClosedPoint k' ≫ traitToAffineLine k k' =
      Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫
        AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)) := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, Category.assoc, traitToAffineLine_over, AffineSpace.zeroSection_over,
      Category.comp_id, traitClosedPoint_traitToBase]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.zeroSection_appTop_coord, map_zero, traitToAffineLine,
      AffineSpace.homOfVector_appTop_coord, traitClosedPoint, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    change (Scheme.ΓSpecIso (.of k')).inv (PowerSeries.constantCoeff PowerSeries.X) = 0
    rw [PowerSeries.constantCoeff_X, map_zero]

end Trait

end AlgebraicGeometry
