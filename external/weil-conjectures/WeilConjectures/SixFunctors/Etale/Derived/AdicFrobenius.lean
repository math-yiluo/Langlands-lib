/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange

/-!
# Compatible systems of Frobenius coefficient morphisms and their realizations

Let `g` be an automorphism of a scheme `X` lying over an automorphism `h` of the base
`s = Spec k` (`g ≫ a_X = a_X ≫ h` cartesian); in the `ℓ`-adic formalism `X = X₀ ×_{k₀} k` and
`g = g_γ` is the geometric Frobenius. A *Weil datum* on `K` is a morphism `φ : Lg^* K ⟶ K`; it
has a *global Frobenius operator* `F_c(φ) = RΓ_c(X, φ) ∘ g_c^*` on compact cohomology
(`AlgebraicGeometry.Etale.globalOperator`) and, at a point `x̄` fixed by `(g, h)`, a *local
Frobenius operator* `F_x̄(φ) = φ_x̄ ∘ τ_x̄` on the geometric stalk
(`AlgebraicGeometry.Etale.localOperator`), blueprint `definition-frobenius-operator--1`.

A *compatible system of Frobenius coefficient morphisms* on a normalized adic system `L_•`
(`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem`) is a family `ψ_n : Lg^* L_n ⟶ L_n` reducing
to each other along the transitions of `L_•`; a compatible tower of Weil pairs is the case where
every `ψ_n` is invertible (`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.IsWeil`). For such a
system and every `m ≥ 1`, the global operators `F_c(ψ_n^{[m]})` and the local operators
`F_x̄(ψ_n^{[m]})` at points fixed by `(g^m, h^m)` form compatible families of endomorphisms of the
normalized towers of perfect complexes `RΓ_c(X, L_n)` and `(L_n)_x̄`; hence they lift to the
realizations over `R`, the realization isomorphisms are equivariant for the lifts, and the traces
of the lifts are the limits of the levelwise traces.

## Main definitions

- `AlgebraicGeometry.Etale.globalOperator`, `AlgebraicGeometry.Etale.localOperator`: the
  Frobenius operators of a Weil datum.
- `AlgebraicGeometry.Etale.endIterate`, `AlgebraicGeometry.Etale.iterateWeilDatum`: the iterates
  `g^m` and `φ^{[m]} : L(g^m)^* K ⟶ K`.
- `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem`: a compatible system of Frobenius
  coefficient morphisms, with its iterates
  `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.iterate`.

## Main results

- `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.isCompatible_globalOperatorFamily`,
  `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.isCompatible_localOperatorFamily`:
  the global and local Frobenius operators form compatible families on the towers.
- `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_isLift_globalOperatorFamily`,
  `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_trace_eq_globalOperatorFamily` and
  their local versions: the operators lift to the realizations, equivariantly for the
  realization isomorphisms, and the traces of the lifts are the limits of the levelwise traces.

## Implementation notes

The blueprint writes Frobenius coefficient morphisms `ψ : LΦ^* K ⟶ K` with respect to the
`q`-power scheme Frobenius `Φ`, and their global operators as the action of the graph
correspondence of `(𝟙, Φ^m)`. By blueprint `lemma-scheme-frobenius-geometric-frobenius--3` (general
clause), that action is `RΓ_c(X, v) ∘ g_{γ,c}^{m,*}` for the morphism `v = ψ_m ∘ (κ^{(m)})⁻¹`
attached to the geometric Frobenius `g_γ` through the comparison `κ^{(m)} : LΦ^{m*} ≅ Lg_γ^{m*}` of
`lemma-scheme-frobenius-geometric-frobenius--1`. Here the data are taken directly relative to
`g = g_γ` (as for the strict Weil complexes `AlgebraicGeometry.Etale.WeilComplex` of
`definition-weil-structure`), and the operators are defined by that formula, with the
compact-support base change `g_c^*` of `AlgebraicGeometry.Etale.compactPullback`.

The compatibility of the operators with the coefficient change comes from the compatibility of
the coefficient comparisons with pullback (`AlgebraicGeometry.Etale.IsCompactPullbackCompatible`,
`AlgebraicGeometry.Etale.IsStalkPullbackCompatible`), which the coefficient comparisons of
`AlgebraicGeometry.Etale.AdicSystem.exists_compactSupportTower` and
`AlgebraicGeometry.Etale.AdicSystem.exists_stalkTower` satisfy.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Operators

variable (Λ : Type (u + 1)) [CommRing Λ] {X s : Scheme.{u}} {g : X ⟶ X} {h : s ⟶ s}

/-- Blueprint `definition-frobenius-operator--1` (1): the *global Frobenius operator*
`F_c(φ) = RΓ_c(X, φ) ∘ g_c^*` on `RΓ_c(X, K)` of a Weil datum `φ : Lg^* K ⟶ K`, for an
automorphism `g` of `X` over an automorphism `h` of the base, `g_c^*` being the compact-support
base change `AlgebraicGeometry.Etale.compactPullback`. The datum `φ` need not be invertible. -/
noncomputable def globalOperator [Finite Λ] {a : X ⟶ s} [QuasiCompact a]
    [HasCompactification a] (sq : IsPullback g a a h) [IsIso h]
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K ⟶
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K :=
  (compactPullback Λ sq).app K ≫ (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).map φ

/-- Blueprint `definition-frobenius-operator--1` (2): the *local Frobenius operator*
`F_x̄(φ) = φ_x̄ ∘ τ_x̄` on the geometric stalk `K_x̄` of a Weil datum `φ : Lg^* K ⟶ K`, at a point
`x̄` fixed by the pair `(g, h)`, `τ_x̄` being the stalk transport
`AlgebraicGeometry.Etale.stalkPullback`. -/
noncomputable def localOperator {x : s ⟶ X} (hx : h ≫ x = x ≫ g) [IsIso h]
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (geometricStalk Λ x).obj K ⟶ (geometricStalk Λ x).obj K :=
  (stalkPullback Λ hx).app K ≫ (geometricStalk Λ x).map φ

end Operators

/-- The inductive step of the compatibility of iterated Weil data with a change of coefficients,
stated for abstract functors so that the kernel does not unfold the derived pullbacks: if
`ψ₁ : G₁ L₁ ⟶ L₁` and `v₁ : M₁ L₁ ⟶ L₁` reduce along `t : L₁ ⟶ Res L₀` to `ψ₀` and `v₀`, then
so does `ψ₁ ∘ G₁ v₁ ∘ comp₁ : P₁ L₁ ⟶ L₁`, provided the comparisons `ι` are compatible with the
composition isomorphisms `comp : P ≅ M ⋙ G`. -/
lemma comp_comm_of_comm_aux {C₀ C₁ : Type*} [Category C₀] [Category C₁] (Res : C₀ ⥤ C₁)
    {G₀ M₀ P₀ : C₀ ⥤ C₀} {G₁ M₁ P₁ : C₁ ⥤ C₁} (comp₀ : P₀ ≅ M₀ ⋙ G₀) (comp₁ : P₁ ≅ M₁ ⋙ G₁)
    (ιg : Res ⋙ G₁ ≅ G₀ ⋙ Res) (ιm : Res ⋙ M₁ ≅ M₀ ⋙ Res) (ιp : Res ⋙ P₁ ≅ P₀ ⋙ Res)
    (hc : ∀ K, ιp.hom.app K ≫ Res.map (comp₀.hom.app K) =
      comp₁.hom.app (Res.obj K) ≫ G₁.map (ιm.hom.app K) ≫ ιg.hom.app (M₀.obj K))
    {L₀ : C₀} {L₁ : C₁} (t : L₁ ⟶ Res.obj L₀) {ψ₀ : G₀.obj L₀ ⟶ L₀} {ψ₁ : G₁.obj L₁ ⟶ L₁}
    (hψ : ψ₁ ≫ t = G₁.map t ≫ ιg.hom.app L₀ ≫ Res.map ψ₀) {v₀ : M₀.obj L₀ ⟶ L₀}
    {v₁ : M₁.obj L₁ ⟶ L₁} (hv : v₁ ≫ t = M₁.map t ≫ ιm.hom.app L₀ ≫ Res.map v₀) :
    (comp₁.hom.app L₁ ≫ G₁.map v₁ ≫ ψ₁) ≫ t =
      P₁.map t ≫ ιp.hom.app L₀ ≫ Res.map (comp₀.hom.app L₀ ≫ G₀.map v₀ ≫ ψ₀) := by
  have hnat := comp₁.hom.naturality t
  have hιg := ιg.hom.naturality v₀
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat hιg
  rw [Functor.map_comp, Functor.map_comp, reassoc_of% hc, reassoc_of% hnat, ← reassoc_of% hιg,
    ← G₁.map_comp_assoc, ← G₁.map_comp_assoc]
  rw [Category.assoc (M₁.map t), ← hv, G₁.map_comp_assoc, ← hψ]
  simp only [Category.assoc]

/-- The base case of the compatibility of iterated Weil data with a change of coefficients,
stated for abstract functors: the identity isomorphisms `id : P ≅ 𝟭` reduce to each other
provided the comparison `ι` is compatible with them. -/
lemma id_comm_of_comm_aux {C₀ C₁ : Type*} [Category C₀] [Category C₁] (Res : C₀ ⥤ C₁)
    {P₀ : C₀ ⥤ C₀} {P₁ : C₁ ⥤ C₁} (id₀ : P₀ ≅ 𝟭 C₀) (id₁ : P₁ ≅ 𝟭 C₁)
    (ιp : Res ⋙ P₁ ≅ P₀ ⋙ Res)
    (hc : ∀ K, ιp.hom.app K ≫ Res.map (id₀.hom.app K) = id₁.hom.app (Res.obj K))
    {L₀ : C₀} {L₁ : C₁} (t : L₁ ⟶ Res.obj L₀) :
    id₁.hom.app L₁ ≫ t = P₁.map t ≫ ιp.hom.app L₀ ≫ Res.map (id₀.hom.app L₀) := by
  rw [hc]
  exact (id₁.hom.naturality t).symm

/-- The compatibility of Frobenius operators with a change of coefficients, stated for abstract
functors so that the kernel does not unfold the six functors: for functors `Φ₀`, `Φ₁` (compact
cohomology or a geometric stalk at two coefficient levels) with a coefficient comparison
`α : Res ⋙ Φ₁ ≅ Φ₀ ⋙ Res'`, transports `cp : Φ ⟶ G ⋙ Φ` compatible with `α`, and Weil data
`ψ₁`, `ψ₀` reducing to each other along `t : L₁ ⟶ Res L₀`, the operators `Φ ψ ∘ cp` are
compatible with the transition `Φ₁ t ≫ α`. -/
lemma operator_comm_of_comm_aux {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀]
    [Category D₁] (Res : C₀ ⥤ C₁) (Res' : D₀ ⥤ D₁) {Φ₀ : C₀ ⥤ D₀} {Φ₁ : C₁ ⥤ D₁}
    {G₀ : C₀ ⥤ C₀} {G₁ : C₁ ⥤ C₁} (α : Res ⋙ Φ₁ ≅ Φ₀ ⋙ Res') (ι : Res ⋙ G₁ ≅ G₀ ⋙ Res)
    (cp₀ : Φ₀ ⟶ G₀ ⋙ Φ₀) (cp₁ : Φ₁ ⟶ G₁ ⋙ Φ₁)
    (hcl : ∀ K, α.hom.app K ≫ Res'.map (cp₀.app K) =
      cp₁.app (Res.obj K) ≫ Φ₁.map (ι.hom.app K) ≫ α.hom.app (G₀.obj K))
    {L₀ : C₀} {L₁ : C₁} (t : L₁ ⟶ Res.obj L₀) {ψ₀ : G₀.obj L₀ ⟶ L₀} {ψ₁ : G₁.obj L₁ ⟶ L₁}
    (hψ : ψ₁ ≫ t = G₁.map t ≫ ι.hom.app L₀ ≫ Res.map ψ₀) :
    (Φ₁.map t ≫ α.hom.app L₀) ≫ Res'.map (cp₀.app L₀ ≫ Φ₀.map ψ₀) =
      (cp₁.app L₁ ≫ Φ₁.map ψ₁) ≫ Φ₁.map t ≫ α.hom.app L₀ := by
  have hcp := cp₁.naturality t
  have hα := α.hom.naturality ψ₀
  dsimp only [Functor.comp_obj, Functor.comp_map] at hcp hα
  rw [Functor.map_comp, Category.assoc, reassoc_of% hcl, Category.assoc, ← Functor.map_comp_assoc,
    hψ, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ← hα,
    reassoc_of% hcp]

section Iterate

/-- The `m`-th iterate `g^m = g ≫ ⋯ ≫ g` of an endomorphism `g`, defined so that
`g^{m+1} = g ≫ g^m` holds by definition. It agrees with the power of `g` in `End X`
(`AlgebraicGeometry.Etale.endIterate_eq_pow`). -/
def endIterate {X : Scheme.{u}} (g : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | m + 1 => g ≫ endIterate g m

@[simp]
lemma endIterate_zero {X : Scheme.{u}} (g : X ⟶ X) : endIterate g 0 = 𝟙 X :=
  rfl

lemma endIterate_succ {X : Scheme.{u}} (g : X ⟶ X) (m : ℕ) :
    endIterate g (m + 1) = g ≫ endIterate g m :=
  rfl

lemma endIterate_eq_pow {X : Scheme.{u}} (g : X ⟶ X) (m : ℕ) :
    endIterate g m = End.asHom (End.of g ^ m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [endIterate_succ, ih, pow_succ]; rfl

instance isIso_endIterate {X : Scheme.{u}} (g : X ⟶ X) [IsIso g] (m : ℕ) :
    IsIso (endIterate g m) := by
  induction m with
  | zero => exact inferInstanceAs (IsIso (𝟙 X))
  | succ m ih => exact inferInstanceAs (IsIso (g ≫ endIterate g m))

/-- The iterates of a cartesian square `g ≫ a = a ≫ h` are cartesian. -/
lemma isPullback_endIterate {X s : Scheme.{u}} {g : X ⟶ X} {h : s ⟶ s} {a : X ⟶ s}
    (sq : IsPullback g a a h) [IsIso g] [IsIso h] (m : ℕ) :
    IsPullback (endIterate g m) a a (endIterate h m) := by
  induction m with
  | zero => exact IsPullback.of_horiz_isIso ⟨by simp⟩
  | succ m ih => exact sq.paste_horiz ih

/-- A point fixed by a pair `(g, h)` is fixed by its iterates. -/
lemma endIterate_comp_of_comp {X s : Scheme.{u}} {g : X ⟶ X} {h : s ⟶ s} {x : s ⟶ X}
    (hx : h ≫ x = x ≫ g) (m : ℕ) : endIterate h m ≫ x = x ≫ endIterate g m := by
  induction m with
  | zero => simp
  | succ m ih => rw [endIterate_succ, endIterate_succ, Category.assoc, ih, ← Category.assoc, hx,
      Category.assoc]

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}} (g : X ⟶ X)

/-- Blueprint `definition-frobenius-correspondences-their-operators` (2),
`definition-frobenius-correspondences-their-operators--4`: the
*iterates* `φ^{[m]} : L(g^m)^* K ⟶ K` of a Weil datum `φ : Lg^* K ⟶ K`, defined by
`φ^{[0]} = (L(𝟙)^* K ≅ K)` and
`φ^{[m+1]} : L(g ≫ g^m)^* K ≅ Lg^* L(g^m)^* K ──Lg^* φ^{[m]}──▶ Lg^* K ──φ──▶ K`. -/
noncomputable def iterateWeilDatum
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    ∀ m : ℕ, (L((endIterate g m)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K
  | 0 => (leftDerivedUpperStarId _ X).hom.app K
  | m + 1 => (leftDerivedUpperStarComp _ g (endIterate g m)).hom.app K ≫
      (L((g)^*[ModuleCat.{u + 1} Λ])).map (iterateWeilDatum φ m) ≫ φ

end Iterate

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} (S : AdicSystem I X)

/-- A *compatible system of Frobenius coefficient morphisms* on a normalized adic system `L_•`,
relative to an endomorphism `g` of `X`: morphisms `ψ_n : Lg^* L_n ⟶ L_n` at every level such that
`ψ_{n+1}` followed by the transition `ν_n : L_{n+1} ⟶ Res L_n` is `Lg^* ν_n` followed by the
identification `Lg^* Res L_n ≅ Res Lg^* L_n`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso`) and `Res ψ_n`; in terms of
derived base change, `ψ_{n+1} ⊗ᴸ A_n` corresponds to `ψ_n` under `ν_n`. No invertibility is
assumed. -/
structure FrobeniusSystem (g : X ⟶ X) where
  /-- The Frobenius coefficient morphism `ψ_n : Lg^* L_n ⟶ L_n`. -/
  coeff (n : ℕ) : (L((g)^*[ModuleCat.{u + 1} (R ⧸ I ^ n)])).obj (S.obj n) ⟶ S.obj n
  /-- `ψ_{n+1}` reduces to `ψ_n`. -/
  comm (n : ℕ) : coeff (n + 1) ≫ S.map n =
    (L((g)^*[ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))])).map (S.map n) ≫
      (leftDerivedUpperStarRestrictScalarsIso
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ)) g).hom.app
          (S.obj n) ≫
      (_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).map (coeff n)

namespace FrobeniusSystem

variable {S} {g : X ⟶ X} (F : S.FrobeniusSystem g)

/-- A compatible system of Frobenius coefficient morphisms is a *compatible tower of Weil pairs* if
every `ψ_n` is invertible: a strict Weil structure `Lg^* L_n ≅ L_n` at every level
(`definition-weil-structure`), compatible with the transitions. -/
def IsWeil : Prop :=
  ∀ n, IsIso (F.coeff n)

/-- The iterated system `ψ_n^{[m]} : L(g^m)^* L_n ⟶ L_n` of a compatible system of Frobenius
coefficient morphisms is again compatible: the composition isomorphisms of the derived pullback
are compatible with restriction of scalars
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_comp_hom_app`). -/
noncomputable def iterate (m : ℕ) : S.FrobeniusSystem (endIterate g m) where
  coeff n := iterateWeilDatum _ g (F.coeff n) m
  comm n := by
    induction m with
    | zero =>
      exact id_comm_of_comm_aux _ (leftDerivedUpperStarId _ X) (leftDerivedUpperStarId _ X)
        (leftDerivedUpperStarRestrictScalarsIso _ (𝟙 X))
        (leftDerivedUpperStarRestrictScalarsIso_id_hom_app _ X) (S.map n)
    | succ m ih =>
      exact comp_comm_of_comm_aux _ (leftDerivedUpperStarComp _ g (endIterate g m))
        (leftDerivedUpperStarComp _ g (endIterate g m))
        (leftDerivedUpperStarRestrictScalarsIso _ g)
        (leftDerivedUpperStarRestrictScalarsIso _ (endIterate g m))
        (leftDerivedUpperStarRestrictScalarsIso _ (g ≫ endIterate g m))
        (leftDerivedUpperStarRestrictScalarsIso_comp_hom_app _ g (endIterate g m)) (S.map n)
        (F.comm n) ih

section Geometric

variable {k : Type u} [Field k] [IsSepClosed k] {aX : X ⟶ Spec (.of k)} [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasCompactification aX] [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))] {h : Spec (.of k) ⟶ Spec (.of k)}
  [IsIso h]

/-- The global Frobenius operators `F_c(ψ_{n+1})` on the levels `RΓ_c(X, L_{n+1})` of the tower
`AlgebraicGeometry.Etale.AdicSystem.compactSupportTower`. -/
noncomputable def globalOperatorFamily (sq : IsPullback g aX aX h)
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n)) (n : ℕ) :
    (S.compactSupportTower aX α hα).obj n ⟶ (S.compactSupportTower aX α hα).obj n :=
  globalOperator _ sq (F.coeff (n + 1))

/-- The local Frobenius operators `F_x̄(ψ_{n+1})` on the levels `(L_{n+1})_x̄` of the tower
`AlgebraicGeometry.Etale.AdicSystem.stalkTower`, at a point `x̄` fixed by `(g, h)`. -/
noncomputable def localOperatorFamily {x : Spec (.of k) ⟶ X} (hx : h ≫ x = x ≫ g)
    (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n)) (n : ℕ) :
    (S.stalkTower x β hβ).obj n ⟶ (S.stalkTower x β hβ).obj n :=
  localOperator _ hx (F.coeff (n + 1))

/-- Global operators: the global Frobenius operators `F_c(ψ_n)` of a compatible system of Frobenius
coefficient morphisms form a compatible family of endomorphisms of the tower `RΓ_c(X, L_n)`, for
coefficient identifications compatible with the compact-support base change
(`AlgebraicGeometry.Etale.AdicSystem.exists_compactSupportTower`). Applied to the iterated systems
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.iterate`, this gives the statement for every
`m`. -/
theorem isCompatible_globalOperatorFamily (sq : IsPullback g aX aX h)
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n))
    (hα' : ∀ n : ℕ, IsCompactPullbackCompatible (I.powSuccFactor n) (α n) sq) :
    (S.compactSupportTower aX α hα).IsCompatible (F.globalOperatorFamily sq α hα) := fun n ↦
  operator_comm_of_comm_aux _ _ (α n) _ (compactPullback _ sq) (compactPullback _ sq) (hα' n)
    (S.map (n + 1)) (F.comm (n + 1))

omit [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))] in
/-- Local operators: at a point `x̄` fixed by `(g, h)`, the local Frobenius operators `F_x̄(ψ_n)` of
a compatible system of Frobenius coefficient morphisms form a compatible family of endomorphisms of
the tower `(L_n)_x̄`, for coefficient identifications compatible with the stalk transport
(`AlgebraicGeometry.Etale.AdicSystem.exists_stalkTower`). -/
theorem isCompatible_localOperatorFamily {x : Spec (.of k) ⟶ X} (hx : h ≫ x = x ≫ g)
    (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n))
    (hβ' : ∀ n : ℕ, IsStalkPullbackCompatible (I.powSuccFactor n) (β n) hx) :
    (S.stalkTower x β hβ).IsCompatible (F.localOperatorFamily hx β hβ) := fun n ↦
  operator_comm_of_comm_aux _ _ (β n) _ (stalkPullback _ hx) (stalkPullback _ hx) (hβ' n)
    (S.map (n + 1)) (F.comm (n + 1))

/-- Global operators, for every `m`: the global operators `F_{c,m}(ψ_n) = F_c(ψ_n^{[m]})` of the
iterated systems form compatible families of endomorphisms of the tower `RΓ_c(X, L_n)`, for
coefficient identifications compatible with the compact-support base change along every pair of
automorphisms. -/
theorem isCompatible_globalOperatorFamily_iterate [IsIso g] (sq : IsPullback g aX aX h)
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n))
    (hα' : ∀ (n : ℕ) (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (sq : IsPullback g aX aX h)
      [IsIso h], IsCompactPullbackCompatible (I.powSuccFactor n) (α n) sq) (m : ℕ) :
    (S.compactSupportTower aX α hα).IsCompatible
      ((F.iterate m).globalOperatorFamily (isPullback_endIterate sq m) α hα) :=
  (F.iterate m).isCompatible_globalOperatorFamily _ α hα fun n ↦ hα' n _ _ _

omit [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))] in
/-- Local operators, for every `m`: at a point `x̄` fixed by `(g^m, h^m)` (for `X = X₀ ×_{k₀} k` and
`g` the geometric Frobenius, a geometric point over an `𝔽_{q^m}`-point of `X₀`), the local operators
`F_{x̄,m}(ψ_n)` of the iterated systems form compatible families of endomorphisms of the tower
`(L_n)_x̄`. -/
theorem isCompatible_localOperatorFamily_iterate {x : Spec (.of k) ⟶ X} (m : ℕ)
    (hx : endIterate h m ≫ x = x ≫ endIterate g m)
    (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n))
    (hβ' : ∀ (n : ℕ) (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (hx : h ≫ x = x ≫ g)
      [IsIso h], IsStalkPullbackCompatible (I.powSuccFactor n) (β n) hx) :
    (S.stalkTower x β hβ).IsCompatible ((F.iterate m).localOperatorFamily hx β hβ) :=
  (F.iterate m).isCompatible_localOperatorFamily hx β hβ fun n ↦ hβ' n _ _ _

section Realization

variable [IsLocalRing R] [IsAdicComplete I R] {ϖ : R} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R)
  (hI : I = Ideal.span {ϖ})

include hϖ hI in
/-- Equivariance for the global operators: the global Frobenius operators of a compatible
system of Frobenius coefficient morphisms lift to an endomorphism `V` of the realization
`P_𝒪 = R lim_n RΓ_c(X, L_n)`, for which the realization isomorphisms
`P_𝒪 ⊗ᴸ_R A_{n+1} ≅ RΓ_c(X, L_{n+1})` are equivariant. -/
theorem exists_isLift_globalOperatorFamily (sq : IsPullback g aX aX h)
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n))
    (hα' : ∀ n : ℕ, IsCompactPullbackCompatible (I.powSuccFactor n) (α n) sq)
    {c : Cone (S.compactSupportTower aX α hα).restrict} (hc : IsHomotopyLimit c) :
    ∃ V : c.pt ⟶ c.pt,
      (S.compactSupportTower aX α hα).IsLift c (F.globalOperatorFamily sq α hα) V :=
  (S.compactSupportTower aX α hα).exists_isLift_of_isAdicComplete hϖ hI hc
    (F.isCompatible_globalOperatorFamily sq α hα hα')

omit [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))] in
include hϖ hI in
/-- Equivariance for the local operators: at a point `x̄` fixed by `(g, h)`, the local
Frobenius operators of a compatible system of Frobenius coefficient morphisms lift to an
endomorphism `V` of the realization `P_{x̄, 𝒪} = R lim_n (L_n)_x̄`, for which the realization
isomorphisms `P_{x̄, 𝒪} ⊗ᴸ_R A_{n+1} ≅ (L_{n+1})_x̄` are equivariant. -/
theorem exists_isLift_localOperatorFamily {x : Spec (.of k) ⟶ X} (hx : h ≫ x = x ≫ g)
    (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n))
    (hβ' : ∀ n : ℕ, IsStalkPullbackCompatible (I.powSuccFactor n) (β n) hx)
    {c : Cone (S.stalkTower x β hβ).restrict} (hc : IsHomotopyLimit c) :
    ∃ V : c.pt ⟶ c.pt, (S.stalkTower x β hβ).IsLift c (F.localOperatorFamily hx β hβ) V :=
  (S.stalkTower x β hβ).exists_isLift_of_isAdicComplete hϖ hI hc
    (F.isCompatible_localOperatorFamily hx β hβ hβ')

/-! The braiding of the derived categories is the Koszul braiding
`DerivedCategory.braidedCategory'` of the derived tensor product. The trace statements below
hold for every choice of right duals; both are available by perfectness
(`ModuleCat.NormalizedPerfectTower.hasRightDualPt`,
`ModuleCat.NormalizedPerfectTower.hasRightDualObj`). -/

attribute [local instance] DerivedCategory.braidedCategory'

include hϖ hI in
/-- Traces of the global operators: the categorical trace `tr_R(V ∣ P_𝒪)` of a lift `V` of the
global Frobenius operators is the element `(tr(F_c(ψ_{n+1}) ∣ RΓ_c(X, L_{n+1})))_n` of
`lim_n R ⧸ Iⁿ⁺¹ = R`; in particular it does not depend on the lift
(`ModuleCat.NormalizedPerfectTower.trace_eq_of_isAdicComplete`). -/
theorem exists_trace_eq_globalOperatorFamily (sq : IsPullback g aX aX h)
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n))
    (hα' : ∀ n : ℕ, IsCompactPullbackCompatible (I.powSuccFactor n) (α n) sq)
    {c : Cone (S.compactSupportTower aX α hα).restrict} (hc : IsHomotopyLimit c)
    [HasRightDual c.pt] [∀ n, HasRightDual ((S.compactSupportTower aX α hα).obj n)]
    {V : c.pt ⟶ c.pt}
    (hV : (S.compactSupportTower aX α hα).IsLift c (F.globalOperatorFamily sq α hα) V) :
    ∃ r : R,
      MonoidalCategory.trace V =
        (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)))) r).asHom ∧
      ∀ n, MonoidalCategory.trace (F.globalOperatorFamily sq α hα n) =
        (algebraMap (R ⧸ I ^ (n + 1))
          (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))))))
            (I.powSuccMk n r)).asHom :=
  (S.compactSupportTower aX α hα).exists_trace_eq_of_isAdicComplete hϖ hI hc
    (F.isCompatible_globalOperatorFamily sq α hα hα') hV

omit [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))] in
include hϖ hI in
/-- Traces of the local operators: the categorical trace `tr_R(V ∣ P_{x̄, 𝒪})` of a lift `V` of the
local Frobenius operators at a point `x̄` fixed by `(g, h)` is the element
`(tr(F_x̄(ψ_{n+1}) ∣ (L_{n+1})_x̄))_n` of `lim_n R ⧸ Iⁿ⁺¹ = R`; in particular it does not depend on
the lift. -/
theorem exists_trace_eq_localOperatorFamily {x : Spec (.of k) ⟶ X} (hx : h ≫ x = x ≫ g)
    (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n))
    (hβ' : ∀ n : ℕ, IsStalkPullbackCompatible (I.powSuccFactor n) (β n) hx)
    {c : Cone (S.stalkTower x β hβ).restrict} (hc : IsHomotopyLimit c)
    [HasRightDual c.pt] [∀ n, HasRightDual ((S.stalkTower x β hβ).obj n)]
    {V : c.pt ⟶ c.pt} (hV : (S.stalkTower x β hβ).IsLift c (F.localOperatorFamily hx β hβ) V) :
    ∃ r : R,
      MonoidalCategory.trace V =
        (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)))) r).asHom ∧
      ∀ n, MonoidalCategory.trace (F.localOperatorFamily hx β hβ n) =
        (algebraMap (R ⧸ I ^ (n + 1))
          (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))))))
            (I.powSuccMk n r)).asHom :=
  (S.stalkTower x β hβ).exists_trace_eq_of_isAdicComplete hϖ hI hc
    (F.isCompatible_localOperatorFamily hx β hβ hβ') hV

end Realization

end Geometric

end FrobeniusSystem

variable [IsLocalRing R] [IsAdicComplete I R] {ϖ : R} {k : Type u} [Field k] [IsSepClosed k]
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
  [HasCompactification aX] [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))]

/-- **Adic realization**, items (i) and (ii). Let `R` be a complete local ring with an ideal
`I = (ϖ)` generated by a nonzerodivisor in the maximal ideal (`R = 𝒪_E`), `A_n = R ⧸ Iⁿ` finite with
exponent invertible on the separably closed field `k`, `a_X : X ⟶ Spec k` separated of finite type,
and `L_•` a normalized system of complexes `L_n ∈ Dᵇctf(X, A_n)`
(`AlgebraicGeometry.Etale.AdicSystem`).

1. *(i) Realization.* The derived limit `K_R = R lim_n ν^* L_n` on the pro-étale site is derived
   complete, satisfies `K_R ⊗ᴸ_R A_n ≅ ν^* L_n` compatibly with the transitions, and lies in every
   common range of degrees of the levels.
2. *(ii) Compact cohomology.* The complexes `RΓ_c(X, L_n)` form a normalized system of perfect
   complexes (for suitable coefficient identifications `α`), whose realization
   `R lim_n RΓ_c(X, L_n)` is represented by a bounded complex of finite free `R`-modules and
   reduces to the levels. For every compatible system `ψ_•` of Frobenius coefficient morphisms
   relative to an automorphism `g` of `X` over an automorphism `h` of `Spec k` (for instance a
   compatible tower of Weil pairs for the geometric Frobenius), and every `m`, the global
   operators `F_{c,m}(ψ_n)` lift to an endomorphism of the realization for which the realization
   isomorphisms are equivariant.
3. *(ii) Geometric stalks.* Likewise for the geometric stalks `(L_n)_x̄` at every geometric point
   `x̄`, with the local operators `F_{x̄,m}(ψ_n)` at points fixed by `(g^m, h^m)`.

The coefficient identifications `α` and `β` are only asserted to exist, whereas the blueprint
uses the canonical comparisons; this is harmless, since the canonical comparisons
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsRestrictScalarsIso` and
`AlgebraicGeometry.Etale.geometricStalkRestrictScalarsIso`) satisfy the hypotheses and any two
choices give isomorphic towers, unit twists lifting level by level.

At the integral stage, compact cohomology and stalks are defined levelwise on the normalized
systems (blueprint `sk-d-setup`), so that `RΓ_c(X, K_R) = R lim_n RΓ_c(X, L_n)` and
`(K_R)_x̄ = R lim_n (L_n)_x̄`. The traces of the lifts are computed by
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_trace_eq_globalOperatorFamily` and
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_trace_eq_localOperatorFamily`.
Item (iii), rationalization and coefficient-field extension, is
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRationalHomEquiv`,
`AlgebraicGeometry.Etale.DerivedCategory.exists_iso_of_boundedConstructibleRational`,
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational_exists_eq_inv_pow_smul`,
`AlgebraicGeometry.Etale.DerivedCategory.isEquivalence_toKaroubi_boundedConstructibleRational`,
`AlgebraicGeometry.Etale.DerivedCategory.rationalization_transport` and, for the stage `ℚ̄_ℓ`,
`CategoryTheory.StageSystem.exists_stage_representation`. -/
theorem adicRealization (hϖ : ϖ ∈ nonZeroDivisors R) (hϖm : ϖ ∈ IsLocalRing.maximalIdeal R)
    (hI : I = Ideal.span {ϖ}) :
    (∀ c : Cone (S.restrict ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory),
      IsHomotopyLimit c →
      _root_.DerivedCategory.derivedComplete (Scheme.ProEt.topology X) I c.pt ∧
        (∃ e : _root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I c.pt ≅
            S.restrict ⋙ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory,
          ∀ n : ℕ, c.π.app (op n) =
            (_root_.DerivedCategory.derivedCompletionCone (Scheme.ProEt.topology X) I c.pt).π.app
              (op n) ≫ e.hom.app (op n)) ∧
        ∀ a b : ℤ, (∀ n : ℕ, (S.restrict.obj (op n)).IsGE a ∧ (S.restrict.obj (op n)).IsLE b) →
          c.pt.IsGE a ∧ c.pt.IsLE b) ∧
    (∃ (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
      (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n)),
      ∀ c : Cone (S.compactSupportTower aX α hα).restrict, IsHomotopyLimit c →
        (∃ (M : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a b : ℤ), M.IsStrictlyGE a ∧
          M.IsStrictlyLE b ∧ (∀ i, Module.Free R (M.X i) ∧ Module.Finite R (M.X i)) ∧
          Nonempty (c.pt ≅ DerivedCategory.Q.obj M)) ∧
        (∀ n, ModuleCat.IsDerivedBaseChange (f := I.powSuccMk n) (c.π.app (op n))) ∧
        ∀ (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso g] [IsIso h]
          (sq : IsPullback g aX aX h) (F : S.FrobeniusSystem g) (m : ℕ),
          ∃ V : c.pt ⟶ c.pt, (S.compactSupportTower aX α hα).IsLift c
            ((F.iterate m).globalOperatorFamily (isPullback_endIterate sq m) α hα) V) ∧
    ∀ x : Spec (.of k) ⟶ X,
      ∃ (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
          geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
        geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
        (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n)),
        ∀ c : Cone (S.stalkTower x β hβ).restrict, IsHomotopyLimit c →
          (∃ (M : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a b : ℤ), M.IsStrictlyGE a ∧
            M.IsStrictlyLE b ∧ (∀ i, Module.Free R (M.X i) ∧ Module.Finite R (M.X i)) ∧
            Nonempty (c.pt ≅ DerivedCategory.Q.obj M)) ∧
          (∀ n, ModuleCat.IsDerivedBaseChange (f := I.powSuccMk n) (c.π.app (op n))) ∧
          ∀ (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h] (F : S.FrobeniusSystem g)
            (m : ℕ) (hx : endIterate h m ≫ x = x ≫ endIterate g m),
            ∃ V : c.pt ⟶ c.pt, (S.stalkTower x β hβ).IsLift c
              ((F.iterate m).localOperatorFamily hx β hβ) V := by
  refine ⟨fun c hc ↦ S.realization hϖ hI hc, ?_, fun x ↦ ?_⟩
  · obtain ⟨α, hα, hα'⟩ := exists_compactSupportTower (I := I) aX
    refine ⟨α, hα, fun c hc ↦ ⟨(S.compactSupportTower_realization aX hϖm hI α hα hc).1,
      (S.compactSupportTower_realization aX hϖm hI α hα hc).2,
      fun g h _ _ sq F m ↦ ?_⟩⟩
    exact (F.iterate m).exists_isLift_globalOperatorFamily hϖm hI (isPullback_endIterate sq m) α hα
      (fun n ↦ hα' n _ _ _) hc
  · obtain ⟨β, hβ, hβ'⟩ := exists_stalkTower (I := I) x
    refine ⟨β, hβ, fun c hc ↦ ⟨(S.stalkTower_realization hϖm hI x β hβ hc).1,
      (S.stalkTower_realization hϖm hI x β hβ hc).2, fun g h _ F m hx ↦ ?_⟩⟩
    exact (F.iterate m).exists_isLift_localOperatorFamily hϖm hI hx β hβ (fun n ↦ hβ' n _ _ _) hc

end AdicSystem

end AlgebraicGeometry.Etale
