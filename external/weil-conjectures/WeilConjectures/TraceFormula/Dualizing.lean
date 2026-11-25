/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SmoothPurity.TateTwistBoundedConstructible
public import WeilConjectures.TraceFormula.Basic

/-!

# Dualizing complexes, Borel–Moore sections and integration

Let `ℓ` be a prime, `k` a field of characteristic `p ≠ ℓ` and `X` a separated `k`-scheme of
finite type with structure morphism `a_X : X ⟶ s = Spec k`. The *dualizing complex* of `X` is
```
ω_X = Ra_X^! ℚ̄_ℓ ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧
```
(`ProEtale.CondensedRing.dualizingComplex'`), for the exceptional inverse image
`boundedConstructibleUpperShriek` of the chosen compactification. It is transported along
morphisms by the composition isomorphism `Rf^! ω_Y ≅ ω_X`
(`ProEtale.CondensedRing.dualizingComplexComp`, blueprint
`proposition-composition-open-restriction-compactifications-f--1`), the conjugate of the composition
isomorphism of the lower shriek.

## Smooth purity

The dualizing complexes of smooth schemes are computed by smooth purity
(`ProEtale.CondensedRing.smoothPurityIso`, `WeilConjectures.SmoothPurity.Defs`): for `X` smooth
of pure dimension `d` over `s`,
```
ω_X = Ra_X^! ℚ̄_ℓ ≅ ℚ̄_ℓ,X(d)[2d]
```
(`ProEtale.CondensedRing.dualizingComplexSmoothIso`); in particular `ω_C ≅ ℚ̄_ℓ,C(1)[2]` for a
smooth curve `C`, which is what makes the local terms of the Frobenius correspondence on a curve
computable (`WeilConjectures.TraceFormula.Correspondence`). For an open immersion `j : U ⟶ X`, such
as the inclusion of an open and closed subscheme, no chosen purity isomorphism is used: the
identification `Rj^! ℚ̄_ℓ,X ≅ j^* ℚ̄_ℓ,X ≅ ℚ̄_ℓ,U` is canonical
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl`), from
`Rj_! ≅ j_!` and the adjunction `j_! ⊣ j^*`.

For the base point no purity is needed: `a_s` is the identity of `s`, and
`ω_s = R(𝟙 s)^! ℚ̄_ℓ,s ≅ ℚ̄_ℓ,s` is the identity isomorphism of the exceptional inverse image
(`ProEtale.CondensedRing.dualizingComplexPointIso`).

## Borel–Moore sections and integration

A *Borel–Moore section* of `X` is a morphism `α : ℚ̄_ℓ,X ⟶ ω_X`
(`ProEtale.CondensedRing.BorelMooreSection`, blueprint `definition-trace-class-local-terms--2`).
Along an open immersion `j : U ⟶ X` it restricts to
```
j^* α : ℚ̄_ℓ,U ≅ Rj^! ℚ̄_ℓ,X --Rj^! α--> Rj^! ω_X ≅ ω_U
```
by the canonical purity for open immersions
(`ProEtale.CondensedRing.BorelMooreSection.restrict`). For `X` proper over `s`
its *integral* is
```
∫_X α : ℚ̄_ℓ,s ⟶ Ra_{X*} La_X^* ℚ̄_ℓ,s ≅ Ra_{X*} ℚ̄_ℓ,X ≅ Ra_{X!} ℚ̄_ℓ,X --α^♭--> ℚ̄_ℓ,s,
```
an element of `End (ℚ̄_ℓ,s)`, where `α^♭` is the adjoint of `α` for `Ra_{X!} ⊣ Ra_X^!`
(`ProEtale.CondensedRing.BorelMooreSection.integral`, blueprint
`definition-trace-class-local-terms--2`). The
*local term* of `α` along an open and closed subscheme `j : B ⟶ X` proper over `s` is the
integral of its restriction, `LT_B(α) = ∫_B j^* α`
(`ProEtale.CondensedRing.BorelMooreSection.localTerm`, blueprint
`definition-trace-class-local-terms--3`), and the integral over a finite disjoint union of open and
closed pieces is the sum of the local terms
(`ProEtale.CondensedRing.BorelMooreSection.integral_eq_sum_localTerm`, blueprint
`theorem-proper-pushforward-lefschetz-verdier--3`). Over the base point the integral of `α` is `α`
itself, read through `ω_s ≅ ℚ̄_ℓ,s` (`ProEtale.CondensedRing.BorelMooreSection.integral_point`): the
identity isomorphisms of the six functors for `𝟙 s` are compatible with the unit comparison of the
monoidal pullback `L(𝟙 s)^*`
(`ProEtale.CondensedRing.boundedConstructibleLowerStarId_inv_app_unit`).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleUpperShriekId`: the identity isomorphism of the
  exceptional inverse image; its composition isomorphism is
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl`.
- `ProEtale.CondensedRing.dualizingComplex'`, `ProEtale.CondensedRing.dualizingComplexComp`.
- `ProEtale.CondensedRing.dualizingComplexSmoothIso`: smooth purity for the dualizing complexes.
- `ProEtale.CondensedRing.dualizingComplexPointIso`: `ω_s ≅ ℚ̄_ℓ,s`.
- `ProEtale.CondensedRing.BorelMooreSection`, `BorelMooreSection.restrict`,
  `BorelMooreSection.integral`, `BorelMooreSection.localTerm`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The identity and composition isomorphisms of the exceptional functors -/

section Comparison

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The identity isomorphism `R(𝟙 X)_! ≅ 𝟭` of the derived lower shriek on bounded constructible
`ℚ̄_ℓ`-sheaves: the identification `R(𝟙 X)_! ≅ R(𝟙 X)_*` of the lower shriek of a proper morphism
with its pushforward, followed by `R(𝟙 X)_* ≅ 𝟭`. -/
noncomputable def boundedConstructibleLowerShriekId (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    boundedConstructibleLowerShriek ℓ (𝟙 X) ≅
      𝟭 (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X) ≪≫
    boundedConstructibleLowerStarId ℓ X

/-- The identity isomorphism `R(𝟙 X)^! ≅ 𝟭` of the exceptional inverse image: the conjugate of
`boundedConstructibleLowerShriekId` for the adjunctions `R(𝟙 X)_! ⊣ R(𝟙 X)^!` and `𝟭 ⊣ 𝟭`. -/
noncomputable def boundedConstructibleUpperShriekId (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    boundedConstructibleUpperShriek ℓ (𝟙 X) ≅
      𝟭 (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  conjugateIsoEquiv
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X))
    Adjunction.id (boundedConstructibleLowerShriekId ℓ X).symm

end Comparison

/-! ### Dualizing complexes -/

section Dualizing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The *dualizing complex* `ω_X = Ra_X^! ℚ̄_ℓ` of a separated `k`-scheme of finite type
(blueprint `definition-verdier-dual-evaluation`). -/
noncomputable abbrev dualizingComplex' (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleUpperShriek ℓ (toPoint X)).obj (𝟙_ _)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The composition isomorphism `Rf^! ω_Y ≅ ω_X` of the dualizing complexes (blueprint
`proposition-composition-open-restriction-compactifications-f--1`). -/
noncomputable def dualizingComplexComp (f : X ⟶ Y) :
    (boundedConstructibleUpperShriek ℓ f).obj
        (dualizingComplex' ℓ Y) ≅ dualizingComplex' ℓ X :=
  ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f (toPoint Y)).app (𝟙_ _)).symm ≪≫
    eqToIso (by rw [comp_toPoint])

/-- The identity isomorphism `Ra^! ℚ̄_ℓ,s ≅ ℚ̄_ℓ,s` for an endomorphism `a = 𝟙` of `s`. -/
noncomputable def upperShriekUnitIsoOfEqId (a : point k ⟶ point k) (ha : a = 𝟙 (point k)) :
    (boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _) ≅
      𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  eqToIso (by rw [ha]) ≪≫ (boundedConstructibleUpperShriekId ℓ (point k)).app (𝟙_ _)

variable (k) in
/-- The dualizing complex of the base point is the unit, `ω_s ≅ ℚ̄_ℓ,s`: the structure morphism
`a_s = toPoint s` is the identity of `s`, and this is the identity isomorphism
`R(𝟙 s)^! ≅ 𝟭` of the exceptional inverse image (`boundedConstructibleUpperShriekId`) at the
unit. -/
noncomputable def dualizingComplexPointIso :
    dualizingComplex' ℓ (point k) ≅ 𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  upperShriekUnitIsoOfEqId ℓ (toPoint (point k)) (toPoint_ext _ _)

end Dualizing

private lemma integral_conjugate_id {C : Type*} [Category C] {L R : C ⥤ C}
    (adj : L ⊣ R) (e : L ≅ 𝟭 C) {M N : C} (α : M ⟶ R.obj N) :
    e.inv.app M ≫ (adj.homEquiv M N).symm α =
      α ≫ (conjugateIsoEquiv adj Adjunction.id e.symm).hom.app N := by
  have h := homEquiv_comp_conjugateEquiv_app adj Adjunction.id e.inv
    ((adj.homEquiv M N).symm α)
  simpa only [Equiv.apply_symm_apply, Adjunction.id_homEquiv_apply,
    conjugateIsoEquiv_apply_hom, Iso.symm_hom] using h.symm

/-! ### Borel–Moore sections -/

section BorelMoore

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The *Borel–Moore sections* of `X`: the morphisms `ℚ̄_ℓ,X ⟶ ω_X` (blueprint
`definition-trace-class-local-terms--2`). -/
abbrev BorelMooreSection (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] : Type _ :=
  𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶ dualizingComplex' ℓ X

variable {ℓ} {X U : Over (Spec (.of k))} [QuasiCompact X.hom] [QuasiCompact U.hom]

namespace BorelMooreSection

variable [LocallyOfFiniteType X.hom] [IsSeparated X.hom] [LocallyOfFiniteType U.hom]
  [IsSeparated U.hom] in
/-- The *restriction* of a Borel–Moore section along an open immersion `j : U ⟶ X`, for
instance the inclusion of an open and closed subscheme:
```
j^* α : ℚ̄_ℓ,U ≅ Rj^! ℚ̄_ℓ,X --Rj^! α--> Rj^! ω_X ≅ ω_U,
```
through the canonical identification `Rj^! ℚ̄_ℓ,X ≅ j^* ℚ̄_ℓ,X ≅ ℚ̄_ℓ,U`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`) and `dualizingComplexComp` (blueprint
`definition-trace-class-local-terms--3`, restricted sections). -/
noncomputable def restrict (j : U ⟶ X) [IsOpenImmersion j.left]
    (α : BorelMooreSection ℓ X) : BorelMooreSection ℓ U :=
  (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
    (boundedConstructibleUpperShriek ℓ j).map α ≫
    (dualizingComplexComp ℓ j).hom

/-- The *integral* `∫_X α ∈ End ℚ̄_ℓ,s` of a Borel–Moore section of a scheme proper over `s`:
```
ℚ̄_ℓ,s ⟶ Ra_{X*} La_X^* ℚ̄_ℓ,s ≅ Ra_{X*} ℚ̄_ℓ,X ≅ Ra_{X!} ℚ̄_ℓ,X --α^♭--> ℚ̄_ℓ,s,
```
the unit of `La_X^* ⊣ Ra_{X*}`, the unit isomorphism of the monoidal functor `La_X^*`, the
identification `Ra_{X!} ≅ Ra_{X*}` for the proper `a_X`, and the adjoint `α^♭` of `α` for
`Ra_{X!} ⊣ Ra_X^!` (blueprint `definition-trace-class-local-terms--2`). -/
noncomputable def integral [IsProper X.hom] (α : BorelMooreSection ℓ X) :
    End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  haveI : IsProper (toPoint X).left := by
    rw [toPoint_left]
    infer_instance
  .of ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (toPoint X)).unit.app (𝟙_ _) ≫
    (boundedConstructibleLowerStar ℓ (toPoint X)).map
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).inv ≫
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
      (toPoint X)).inv.app (𝟙_ _) ≫
    ((boundedConstructibleUpperShriekAdjunction ℓ
      (toPoint X)).homEquiv _ _).symm α)

/-- The integral is additive (blueprint `theorem-proper-pushforward-lefschetz-verdier--3`). -/
lemma integral_add [IsProper X.hom] (α β : BorelMooreSection ℓ X) :
    (α + β).integral = α.integral + β.integral :=
  by
  apply End.ext
  simp only [End.add_asHom, integral, Adjunction.homEquiv_counit, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

variable [LocallyOfFiniteType X.hom] [IsSeparated X.hom] in
/-- The *local term* `LT_B(α) = ∫_B j^* α` of a Borel–Moore section along an open and closed
subscheme `j : B ⟶ X` proper over `s` (blueprint `definition-trace-class-local-terms--3`). -/
noncomputable def localTerm (j : U ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    [IsProper U.hom] (α : BorelMooreSection ℓ X) :
    End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (α.restrict j).integral

instance : IsProper (point k).hom :=
  inferInstanceAs (IsProper (𝟙 (Spec (.of k))))

/-- The integral over the base point, for an endomorphism `a = 𝟙` of the base point in place of
its structure morphism. -/
private lemma integral_point_aux (a : point k ⟶ point k) (ha : a = 𝟙 (point k))
    [IsProper a.left]
    (α : 𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      (boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ a).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ a).map
          (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)).inv ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).inv.app (𝟙_ _) ≫
        ((boundedConstructibleUpperShriekAdjunction ℓ a).homEquiv _ _).symm α =
      α ≫ (upperShriekUnitIsoOfEqId ℓ a ha).hom := by
  subst ha
  simp only [upperShriekUnitIsoOfEqId, eqToIso_refl, Iso.refl_trans, Iso.app_hom]
  refine Eq.trans ?_ (integral_conjugate_id
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 (point k)))
    (boundedConstructibleLowerShriekId ℓ (point k)) α)
  change _ = ((boundedConstructibleLowerStarId ℓ (point k)).inv.app (𝟙_ _) ≫
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 (point k))).inv.app (𝟙_ _)) ≫ _
  rw [boundedConstructibleLowerStarId_inv_app_unit]
  simp only [Category.assoc]

/-- **Point normalization of the integral**: over the base point, where `ω_s ≅ ℚ̄_ℓ,s`
(`dualizingComplexPointIso`), the integral of a Borel–Moore section is the section itself. -/
theorem integral_point (α : BorelMooreSection ℓ (point k)) :
    α.integral = .of (α ≫ (dualizingComplexPointIso ℓ k).hom) :=
  haveI : IsProper (toPoint (point k)).left := by
    rw [toPoint_left]
    infer_instance
  End.ext (integral_point_aux (toPoint (point k)) (toPoint_ext _ _) α)

end BorelMooreSection

end BorelMoore

end AlgebraicGeometry.ProEtale.CondensedRing
