/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Reduction
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk

/-!

# The projective line, and the reduction of proper base change to it

The proof of the proper base change theorem has two halves. The geometric half is the single
computation that the projection `ℙ¹_S ⟶ S` (`AlgebraicGeometry.ProjectiveLine`) satisfies
the base change property `AlgebraicGeometry.Etale.HasTorsionBaseChange` for every base
scheme `S`; it rests on the cohomology of curves over a separably closed field. The formal
half deduces the general theorem from that one case, using Chow's lemma to dominate an
arbitrary proper morphism by a projective one.

The two halves are combined here into
`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isProper`, from which
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` is derived.

## The proof of the projective-line case

The proof first treats a single torsion sheaf `F` on `ℙ¹_S`: the degreewise exchange maps
`g⁻¹ Rᵠp_* F ⟶ Rᵠp'_* g'⁻¹ F` are isomorphisms
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_projectiveLine` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`). There
the exchange morphism is checked at every geometric point, since geometric stalks are
conservative; by
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`, the
stalk is the pullback map `Hᵠ(ℙ¹_{κ(s̄)}, F) ⟶ Hᵠ(ℙ¹_{κ(t̄)}, F)` between two separably closed
fields. That map is bijective by the invariance of the cohomology of a curve under extension
of separably closed base fields. The strictly henselian route of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian`
(Mayer–Vietoris on the two standard charts, finite étale lifting) is not used by the Lean
proof; it is the intended proof of the `sorry`ed stalk statement, through the comparison of
`ℙ¹` over a strictly henselian ring with its closed fibre.

Complexes are then reached by truncation dévissage
(`AlgebraicGeometry.Etale.isIso_baseChange_app_projectiveLine`): both sides of the derived
exchange morphism do not lower the cohomological degree, so `Hᵐ` of both sides only depends
on `τ_{≤ m} K`, a bounded complex which is built from its shifted cohomology sheaves by
truncation triangles.

## The reduction

The formal half, `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper`,
is proved in `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Reduction`.

## Main statements

- `AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveLine`: the projective line over
  any base satisfies the base change property.
- `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isProper`: every proper morphism
  satisfies the base change property.

## References

- Stacks Project, Lemma 59.91.10, the reduction to the projective line,
  <https://stacks.math.columbia.edu/tag/0A4F>
- Stacks Project, Theorem 59.91.11, whose proof is the projective-line computation,
  <https://stacks.math.columbia.edu/tag/095T>
- [SGA 4, Exp. XII, Théorème 5.1]

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The derived exchange morphism of the projective line is an isomorphism at a torsion sheaf
placed in degree `0`: in nonnegative degrees, its cohomology sheaves are the degreewise exchange
maps `g⁻¹ Rᵠp_* F ⟶ Rᵠp'_* g'⁻¹ F`, which are isomorphisms by
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_projectiveLine`, and in negative degrees
both sides vanish. This is step (iii) of the proof of
`proposition-proper-base-change-projective-line`. -/
lemma Etale.isIso_baseChange_app_singleFunctor_obj_projectiveLine {S T X' : Scheme.{u}}
    {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  refine (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).2 fun q ↦ ?_
  rcases le_or_gt 0 q with hq | hq
  · lift q to ℕ using hq
    exact Etale.isIso_baseChangeHomologyMap_projectiveLine Λ sq F q
  · rw [Etale.isIso_baseChangeHomologyMap_iff]
    exact ⟨0, (Etale.isZero_homologyFunctor_baseChangeSource_obj Λ g _ _ 0 q hq).eq_of_src _ _,
      (Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ g' f' _ 0 q hq).eq_of_src _ _⟩

/-- The derived exchange morphism of the projective line is an isomorphism at every bounded
below complex `K` with torsion cohomology sheaves. This is the truncation dévissage of step (iv)
of the proof of `proposition-proper-base-change-projective-line`: both `g⁻¹ ∘ Rp_*` and
`Rp'_* ∘ g'⁻¹` do not lower the cohomological degree, so `Hᵐ` of both sides at `K` only depends on
`τ_{≤ m} K`, which is reached from its shifted cohomology sheaves by the truncation triangles and
the five lemma (`DerivedCategory.Plus.isIso_app_of_forall_homology`); for the cohomology sheaves,
which are torsion, this is
`AlgebraicGeometry.Etale.isIso_baseChange_app_singleFunctor_obj_projectiveLine`. -/
lemma Etale.isIso_baseChange_app_projectiveLine {S T X' : Scheme.{u}}
    {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    (K : DerivedCategory.Plus (Sheaf (ProjectiveLine S).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.moduleTorsionHomology Λ (ProjectiveLine S) K) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  let P : ObjectProperty (Sheaf (ProjectiveLine S).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) := fun F ↦ IsTorsionModuleSheaf F
  have : P.IsClosedUnderIsomorphisms := ⟨fun φ (_ : IsTorsionModuleSheaf _) ↦ .of_epi φ.hom⟩
  exact DerivedCategory.Plus.isIso_app_of_forall_homology _ P
    (fun F (_ : IsTorsionModuleSheaf F) ↦
      Etale.isIso_baseChange_app_singleFunctor_obj_projectiveLine Λ sq F)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeSource_obj Λ g _ K n q hq)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ g' f' K n q hq) K hK

/-- **The projective line satisfies base change**: for every scheme `S`, the projection
`ℙ¹_S ⟶ S` satisfies `AlgebraicGeometry.Etale.HasTorsionBaseChange`, that is, for every
cartesian square

```
ℙ¹_T --g'--> ℙ¹_S
  |            |
  p'           p
  v            v
  T ---g-----> S
```

the derived base change map is an isomorphism on every bounded below complex with torsion
cohomology. This is the geometric half of the proof of proper base change; see the module
docstring, and Stacks Project, Tag 095T, whose proof it is.
(blueprint: `proposition-proper-base-change-projective-line`) -/
theorem Etale.hasTorsionBaseChange_projectiveLine (S : Scheme.{u}) :
    Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S) := fun _ _ _ _ _ sq K hK ↦ by
  have := Etale.isIso_baseChange_app_projectiveLine Λ sq K hK
  rwa [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this

/-- **Proper morphisms satisfy base change**: the two halves of the proof combined. -/
theorem Etale.hasTorsionBaseChange_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper Λ
    (Etale.hasTorsionBaseChange_projectiveLine Λ) f

/-- **Injective acyclicity gives bounded-below base change, arbitrary coefficients.** Let `Λ` be
a commutative ring and `f : X ⟶ Y` proper. Assume injective acyclicity `IA(f)` over `Λ`: for every
cartesian square over `f` and every torsion injective sheaf `I` of `Λ`-modules on `X_ét`,
`Rᵠf'_*(g'^* I) = 0` for `q > 0`. Then `f` has the base change property: the derived base change
map is an isomorphism on every `K ∈ D⁺(X_ét, Λ)` with torsion cohomology sheaves.

For a coefficient ring which is torsion as an additive group this is the direct argument
`AlgebraicGeometry.Etale.HasInjectiveAcyclicity.hasTorsionBaseChange`: resolve `K` by injectives,
which are torsion and hence `f'_*`-acyclic after base change. Over an arbitrary `Λ` a torsion sheaf
need not embed into a torsion injective sheaf, so that argument does not apply. The conclusion is
instead the proper base change theorem
`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isProper`, which needs no acyclicity hypothesis.
(blueprint: `theorem-pbc-injective-acyclicity`) -/
@[stacks 0A4B]
theorem Etale.HasInjectiveAcyclicity.hasTorsionBaseChange_of_isProper {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (_hf : Etale.HasInjectiveAcyclicity Λ f) :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_isProper Λ f

end AlgebraicGeometry
