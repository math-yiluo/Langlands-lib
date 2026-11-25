/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.FieldExtension
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian
import WeilConjectures.RingTheory.ProEtale.WeakDimension

/-!
# The exchange morphism of the projective line at a geometric point

Let `p : ℙ¹_S ⟶ S` be the projective line and

```
X' --g'--> ℙ¹_S
|            |
f'           p
v            v
T ----g----> S
```

a cartesian square. At a geometric point `t̄` of `T` with image `s̄` in `S`, the stalk of the
degree-`q` exchange morphism `g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` is the pullback map
`Hᵠ(ℙ¹_{κ(s̄)}, F|) ⟶ Hᵠ(ℙ¹_{κ(t̄)}, F|)` between the cohomologies of the projective lines over
the residue fields of the strict henselisations at `s̄` and `t̄`
(`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`).
These residue fields are the separable closures of `κ(s)` and `κ(t)`, so the pullback map is
an isomorphism by the invariance of the cohomology of a proper curve under extension of
separably closed fields (`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed`).

Hence the exchange morphism is an isomorphism at every geometric point, and so an
isomorphism; applied to an injective torsion sheaf `I`, whose higher direct images along `p`
vanish, this is the injective acyclicity of `p`
(`AlgebraicGeometry.Etale.hasInjectiveAcyclicity_projectiveLine`).

## Main statements

- `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`:
  the stalk of the exchange morphism of `ℙ¹` at a geometric point is the pullback map between
  the cohomologies of two projective lines over separably closed fields.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_projectiveLine`: the degree-`q`
  exchange morphism of `ℙ¹` is an isomorphism on torsion sheaves.
- `AlgebraicGeometry.Etale.hasInjectiveAcyclicity_projectiveLine`: the projection
  `ℙ¹_S ⟶ S` has injective acyclicity.

## References

- Stacks Project, proof of Theorem 59.91.11, <https://stacks.math.columbia.edu/tag/095T>
-/

@[expose] public section

universe u

open CategoryTheory Limits

section Auxiliary

/-! ### Auxiliary lemmas -/

namespace AlgebraicGeometry

open Scheme Etale

/-- The geometric point `Spec κ(x)‾ ⟶ X` given by the algebraic closure of the residue field
is `Spec` of the inclusion `κ(x) ⟶ κ(x)‾` followed by the canonical map. -/
lemma Scheme.algClosurePoint_eq (X : Scheme.{u}) (x : X) :
    X.algClosurePoint x =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) _)) ≫
        X.fromSpecResidueField x :=
  rfl

end AlgebraicGeometry

end Auxiliary

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The exchange morphism of `ℙ¹` on a geometric stalk.** Let

```
X' --g'--> ℙ¹_S
|            |
f'           p
v            v
T ----g----> S
```

be cartesian, let `F` be a torsion sheaf of `Λ`-modules on `ℙ¹_S` and `q ≥ 0`. Let
`τ : Spec k' ⟶ T` and `σ : Spec k ⟶ S` be geometric points whose fields are algebraic over
the residue fields of their images — so that `k` and `k'` are the residue fields of the strict
henselisations of `S` at `σ` and of `T` at `τ` — and let `ι : Spec k' ⟶ Spec k` be compatible
with `g`. Then the stalk at `τ` of the degree-`q` exchange morphism
`g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` (`AlgebraicGeometry.Etale.baseChangeHomologyMap`) is, up to
isomorphisms of its source and target, the pullback map
`Hᵠ(ℙ¹_k, F|) ⟶ Hᵠ(ℙ¹_{k'}, F|)` along `ℙ¹_{k'} ⟶ ℙ¹_k`.

The source and target stalks are the cohomologies of `ℙ¹` over the strict henselisations of
`S` and `T` (the strict henselisation stalk formula), which restrict isomorphically to the
closed fibres (the strictly henselian comparison for `ℙ¹`); expanding the unit, base change
and counit composite defining the exchange morphism identifies the induced map with the
field-extension pullback.

**Form of the statement.** The statement asserts the existence of additive
isomorphisms of the two stalks with closed-fibre cohomology that make the
exchange square commute.
(blueprint: proposition-proper-base-change-projective-line--1)
-/
theorem Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k))
    (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (φ : S.residueField s ⟶ .of k),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (φ : T.residueField t ⟶ .of k'),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ T.fromSpecResidueField t = τ)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    ∃ (e₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ ι)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ ι)
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q (e₁ x) := by
  exact Etale.geometricStalk_projectiveLine_of_strictLocal Λ
    (fun A B _ _ _ _ _ _ φ _ F _ q =>
      Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal Λ φ F q)
    sq σ τ ι hι hσ hτ F q

/-- **The exchange morphism of `ℙ¹` is an isomorphism on torsion sheaves.** For every
cartesian square

```
X' --g'--> ℙ¹_S
|            |
f'           p
v            v
T ----g----> S
```

every torsion sheaf `F` of `Λ`-modules on `ℙ¹_S` and every `q ≥ 0`, the degree-`q` exchange
morphism `g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` is an isomorphism. By conservativity of the geometric
stalks it suffices to check this at the geometric points `Spec κ(t)‾ ⟶ T`; there the stalk is
the pullback map between the cohomologies of the projective lines over two separably closed
fields (`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`),
which is bijective because `ℙ¹` is a proper curve
(`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed`). -/
theorem Etale.isIso_baseChangeHomologyMap_projectiveLine
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun t ↦ ?_
  rw [uliftPointSmallEtale, NatIso.isIso_map_iff ((pointSmallEtale _).uliftSheafFiberIso _)]
  let κs := S.residueField (g.base t)
  let κt := T.residueField t
  let : Algebra κs (AlgebraicClosure κt) :=
    ((algebraMap κt (AlgebraicClosure κt)).comp (g.residueFieldMap t).hom).toAlgebra
  let ψ : AlgebraicClosure κs →ₐ[κs] AlgebraicClosure κt := IsAlgClosed.lift
  let ι : Spec (.of (AlgebraicClosure κt)) ⟶ Spec (.of (AlgebraicClosure κs)) :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hι : ι ≫ S.algClosurePoint (g.base t) = T.algClosurePoint t ≫ g := by
    rw [Scheme.algClosurePoint_eq, Scheme.algClosurePoint_eq, Category.assoc,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 2
    ext x
    exact ψ.commutes x
  obtain ⟨e₁, e₂, h⟩ := Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine
    Λ sq (S.algClosurePoint (g.base t)) (T.algClosurePoint t) ι hι
    ⟨g.base t, CommRingCat.ofHom (algebraMap κs (AlgebraicClosure κs)),
      Algebra.IsIntegral.isIntegral (R := κs), rfl⟩
    ⟨t, CommRingCat.ofHom (algebraMap κt (AlgebraicClosure κt)),
      Algebra.IsIntegral.isIntegral (R := κt), rfl⟩ F q
  have hb := IsCurve.bijective_cohomologyMap_of_isSepClosed Λ _
    (ProjectiveSpace.isPullback_map _ ι)
    ((ProjectiveSpace.map _ (S.algClosurePoint (g.base t)))^*[ModuleCat.{u + 1} Λ].obj F) q
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have hfun : ⇑(((pointSmallEtale (T.algClosurePoint t)).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
      (Etale.baseChangeHomologyMap Λ sq q F)).hom = e₂.symm ∘ _ ∘ e₁ :=
    funext fun x ↦ (e₂.symm_apply_apply _).symm.trans (congrArg e₂.symm (h x))
  exact hfun ▸ e₂.symm.bijective.comp (hb.comp e₁.bijective)

/-- **Injective acyclicity of the projective line**: for every scheme `S`, the projection
`ℙ¹_S ⟶ S` satisfies `AlgebraicGeometry.Etale.HasInjectiveAcyclicity`. For an injective
torsion sheaf `I` the higher direct images `Rᵠp_* I` vanish, and after any base change the
exchange morphism `g⁻¹ Rᵠp_* I ⟶ Rᵠf'_* g'⁻¹ I` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_projectiveLine`), so the target
vanishes too.
(blueprint: `proposition-proper-base-change-projective-line`) -/
theorem Etale.hasInjectiveAcyclicity_projectiveLine (S : Scheme.{u}) :
    Etale.HasInjectiveAcyclicity Λ (ProjectiveLine S ↘ S) := by
  intro T X' g f' g' sq I hI _ q hq
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
  have := hI
  have := Etale.isIso_baseChangeHomologyMap_projectiveLine Λ sq I n
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ n).mapIso
    (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
      ((((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app I))).symm
  refine IsZero.of_iso ?_ (asIso (Etale.baseChangeHomologyMap Λ sq n I)).symm
  refine IsZero.of_iso ?_
    ((((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso n).app _).symm
  exact ((g)^*[ModuleCat.{u + 1} Λ]).map_isZero
    (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor _ I (q := n) (by lia))

end AlgebraicGeometry
