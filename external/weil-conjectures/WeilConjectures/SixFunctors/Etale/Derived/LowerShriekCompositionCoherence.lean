/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence
import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange
import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportCompositionProjection
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc

/-!
# Coherence of the composition law and the projection formula

Two coherence properties of the compactly supported direct image `Rf_!` on the unbounded
derived categories of the small étale sites, with finite coefficients, the corresponding
blueprint nodes of the six-functor chapters:

* the projection map `PF : Rf_!M ⊗ᴸ N ⟶ Rf_!(M ⊗ᴸ Lf^*N)` is compatible with the associativity
  of the derived tensor product
  (`AlgebraicGeometry.Etale.projectionMapAssociativity`,
  `proposition-composition-base-change-rf-shriek--1`);
* there is a composition law `Rh_! ≅ Rf_! ⋙ Rg_!` for `h = f ≫ g`
(`proposition-composition-base-change-rf-shriek--1`)
  compatible with the projection maps (`proposition-composition-base-change-rf-shriek--1`) and with
  the compactly supported base change maps `Ex_!` of pasted cartesian squares (`sk-thm-sf-package`
  (2)) (`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`).

Together with the commutation of the derived pullback along an étale morphism with the derived
internal hom (`AlgebraicGeometry.Etale.isIso_ihomComparison_leftDerivedUpperStar_of_etale`, in
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarInternalHom`), they are the inputs of the
composition and étale-locality statements for cohomologically smooth
morphisms (`lem-pur-co-smooth-composition`, `lem-pur-co-smooth-etale-locality`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product: otherwise the monoidal structures found by instance
-- search differ from the ones in these definitions, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section ProjectionAssociativityProof

open Lean Elab Tactic Meta

-- Use the same sheaf braiding as the compactification associativity theorem.
attribute [local instance 20000] Etale.sheafBraidedCategory

private theorem projectionMapOfCompactification_assoc_iso
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N N' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app M).app N ▷ N' ≫
        ((projectionMapOfCompactification A c).app (M ⊗ (L((f)^*[A])).obj N)).app N' ≫
        (Rf_!(c)[A]).map (α_ M _ _).hom =
      (α_ ((Rf_!(c)[A]).obj M) N N').hom ≫
        ((projectionMapOfCompactification A c).app M).app (N ⊗ N') ≫
        (Rf_!(c)[A]).map (M ◁ (leftDerivedUpperStarTensorIso A f N N').hom) := by
  rw [leftDerivedUpperStarTensorIso_hom]
  exact projectionMapOfCompactification_assoc A c M N N'

-- Congruence avoids unfolding the derived monoidal construction when converting its two
-- definitionally equal sheaf braidings. The resulting proof is checked by the kernel.
private theorem projectionAssociativityProofHEq
    {P Q : Prop} (p : P) (q : Q) (h : P = Q) : HEq p q := by
  cases h
  rfl

private meta partial def projectionAssociativityCongrHEq (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if ← isProp (← inferType a) then
    let hp ← projectionAssociativityCongrHEq (← inferType a) (← inferType b)
    let e ← mkAppM ``eq_of_heq #[hp]
    return ← mkAppM ``projectionAssociativityProofHEq #[a, b, e]
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    let ct ← mkHCongrWithArity a.getAppFn argsA.size
    let mut ps := #[]
    for i in [:argsA.size] do
      let mut h ← projectionAssociativityCongrHEq argsA[i]! argsB[i]!
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[argsA[i]!, argsB[i]!, h]
    let pf := mkAppN ct.proof ps
    if (← inferType pf).isHEq then return pf
    else return ← mkAppM ``heq_of_eq #[pf]
  else
    unless ← isDefEq a b do
      throwError "The projection associativity structures are not definitionally equal"
    return ← mkHEqRefl a

private theorem projectionMapAssociativity_generic (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    ProjectionMapAssociativity A f := by
  constructor
  intro M N N'
  have h := projectionMapOfCompactification_assoc_iso A
    (HasCompactification.compactification f) M N N'
  dsimp only [projectionMap, rightDerivedLowerShriek]
  run_tac withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == `h) | throwError "no h"
    let q ← projectionAssociativityCongrHEq t (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf

end ProjectionAssociativityProof

omit [Finite Λ] in
/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: Coherence of the projection
formula.

The projection map `PF : Rf_!M ⊗ᴸ N ⟶ Rf_!(M ⊗ᴸ Lf^*N)` is compatible with the associativity of
the derived tensor product: the two maps
`(Rf_!M ⊗ᴸ N) ⊗ᴸ N' ⟶ Rf_!(M ⊗ᴸ (Lf^*N ⊗ᴸ Lf^*N'))`, applying the projection map twice or once
to `N ⊗ᴸ N'` followed by the tensor comparison `Lf^*(N ⊗ᴸ N') ≅ Lf^*N ⊗ᴸ Lf^*N'`, agree. This is
the identification of "the two tensor reassociations" in the blueprint proof of the coherence of
the projection formula. -/
theorem projectionMapAssociativity {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    ProjectionMapAssociativity (ModuleCat.{u + 1} Λ) f :=
  projectionMapAssociativity_generic (ModuleCat.{u + 1} Λ) f

private noncomputable def graphCompIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification h] :
    R(h)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] := by
  subst h
  exact sfGraphCompactSupportCompIso Λ f g (HasCompactification.compactification f)
    (HasCompactification.compactification g) (HasCompactification.compactification (f ≫ g))

private theorem graphCompIso_projection
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification h] :
    Adjunction.ProjectionCompCompatible
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) g).app M).app N)
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) h).app M).app N)
      (fun N ↦ (leftDerivedUpperStarComp _ f g h w.symm).hom.app N)
      (graphCompIso Λ f g h w) := by
  subst h
  exact sfGraphCompactSupportCompIso_projection Λ f g

/-- Blueprints `proposition-composition-base-change-rf-shriek--1` and `sk-thm-sf-package` (clause
(2)): the coherence of the composition law for `Rf_!` with the projection formula and with base
change.

There is a composition isomorphism `E f g h w : Rh_! ≅ Rf_! ⋙ Rg_!` for all `f`, `g` and
`h = f ≫ g` admitting compactifications (the composition law itself is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`) such that
1. (`proposition-composition-base-change-rf-shriek--1`, the pentagon for composable `f`, `g`,
compatible with the
   composition law) the projection maps compose: for `M` on `X` and `N` on `Z`,
   ```
   Rh_!M ⊗ᴸ N ──E ▷ N──▶ Rg_!Rf_!M ⊗ᴸ N ──PF_g──▶ Rg_!(Rf_!M ⊗ᴸ Lg^*N)
          │PF_h                                         │Rg_! PF_f
          ▼                                                    ▼
   Rh_!(M ⊗ᴸ Lh^*N) ──E──▶ Rg_!Rf_!(M ⊗ᴸ Lh^*N) ≅ Rg_!Rf_!(M ⊗ᴸ Lf^*Lg^*N)
   ```
   commutes;
2. (`sk-thm-sf-package` (2), the compact-support base change is compatible with the composition
   law) for cartesian squares `a ≫ f = f' ≫ b` and `b ≫ g = g' ≫ c` with quasi-compact `f'`,
   `g'` and `f' ≫ g'`, the base change map of the pasted square is the pasting of the base
   change maps: `Ex_h ≫ E f' g' = Lc^* (E f g) ≫ Ex_g ≫ Rg'_! Ex_f`. -/
theorem exists_rightDerivedLowerShriekCompIso :
    ∃ E : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z), f ≫ g = h →
        ∀ [HasCompactification f] [HasCompactification g] [HasCompactification h],
        R(h)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ],
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
        [HasCompactification f] [HasCompactification g] [HasCompactification h],
        Adjunction.ProjectionCompCompatible
          (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
          (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) g).app M).app N)
          (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) h).app M).app N)
          (fun N ↦ (leftDerivedUpperStarComp _ f g h w.symm).hom.app N) (E f g h w)) ∧
      (∀ {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {f' : X' ⟶ Y'}
        {g' : Y' ⟶ Z'} {h' : X' ⟶ Z'} {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
        (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) (sqh : IsPullback a h' h c)
        (w : f ≫ g = h) (w' : f' ≫ g' = h') [HasCompactification f] [HasCompactification g]
        [HasCompactification h] [HasCompactification f'] [HasCompactification g']
        [HasCompactification h'] [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact h'],
        Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
          (rightDerivedLowerShriekBaseChangeMap Λ sqg) (rightDerivedLowerShriekBaseChangeMap Λ sqh)
          (E f g h w) (E f' g' h' w')) := by
  refine ⟨@graphCompIso Λ _ _, ?_, ?_⟩
  · exact graphCompIso_projection Λ
  · intro X Y Z X' Y' Z' f g h f' g' h' a b c sqf sqg sqh w w'
      cf cg ch cf' cg' ch' qf' qg' qh'
    subst h
    subst h'
    constructor
    intro M
    exact sfGraphCompactSupportCompIso_baseChange Λ sqf sqg sqh M

end Etale

end AlgebraicGeometry
