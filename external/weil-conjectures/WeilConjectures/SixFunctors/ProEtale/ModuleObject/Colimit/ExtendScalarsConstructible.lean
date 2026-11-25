/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-!
# Extension of scalars preserves constructibility

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `X` a scheme. The extension of
scalars `Λ'_X ⊗_{Λ_X} -` along `a_X : Λ_X ⟶ Λ'_X`

* preserves finitely presented module objects, being right exact and sending `Λ_X` to `Λ'_X`;
* commutes with the pullbacks of module objects (the underived (Pull),
  `ProEtale.CondensedRing.pullIso`), hence preserves pro-étale local finite presentation
  (`ProEtale.CondensedRing.IsLocallyFinitelyPresented.extendScalars`) and constructibility
  (`ProEtale.CondensedRing.IsConstructibleModuleObject.extendScalars`), along the same covers and
  stratifications.

If moreover `Λ'_X` is flat over `Λ_X`, i.e. the extension of scalars is exact, its left derived
functor is computed termwise and commutes with the cohomology sheaves, so it preserves bounded
constructible complexes (`ProEtale.CondensedRing.boundedConstructible_leftDerivedExtendScalars_obj`,
blueprint `lemma-extension-scalars-preserves-dctf--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

omit [IsCommMonObj Λ'] in
/-- The extension of scalars along `a_X : Λ_X ⟶ Λ'_X` preserves finitely presented module
objects: it is additive, right exact and sends `Λ_X` to `Λ'_X`. -/
lemma IsFinitelyPresented.extendScalars {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFinitelyPresented (condensedRingObj Λ X) M) :
    Mod.IsFinitelyPresented (condensedRingObj Λ' X)
      ((Mod.extendScalars (coefficientMap a X)).obj M) :=
  hM.map _ (Mod.extendScalarsObjRegularIso (coefficientMap a X))

/-- The extension of scalars along `a_X : Λ_X ⟶ Λ'_X` preserves pro-étale local finite
presentation: if `M|_{Uᵢ}` is finitely presented for a pro-étale cover `{Uᵢ ⟶ X}`, then so is
`(Λ'_X ⊗ M)|_{Uᵢ} ≅ Λ'_{Uᵢ} ⊗ M|_{Uᵢ}`, by the underived (Pull). -/
lemma IsLocallyFinitelyPresented.extendScalars {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ X) M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ' X)
      ((Mod.extendScalars (coefficientMap a X)).obj M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun i ↦ (isFinitelyPresented_mapMod_iff Λ' _ _).2 ?_⟩
  exact (IsFinitelyPresented.extendScalars a
    ((isFinitelyPresented_mapMod_iff Λ _ _).1 (h𝒰 i))).of_iso ((pullIso a (𝒰.f i)).app M)

/-- The extension of scalars along `a_X : Λ_X ⟶ Λ'_X` preserves constructibility: if `M` is
constructible along a stratification `X = ∐ₐ Xₐ`, so is `Λ'_X ⊗ M`, its restriction to `Xₐ`
being `Λ'_{Xₐ} ⊗ M|_{Xₐ}` by the underived (Pull). -/
theorem IsConstructibleModuleObject.extendScalars {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    IsConstructibleModuleObject (condensedRingObj Λ' X)
      ((Mod.extendScalars (coefficientMap a X)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun i ↦ (isLocallyFinitelyPresented_mapMod_iff Λ' _ _).2 ?_⟩
  exact IsLocallyFinitelyPresented.of_iso ((pullIso a (S.immersion i)).app M)
    (IsLocallyFinitelyPresented.extendScalars a
      ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS i)))

/-- Blueprint `lemma-extension-scalars-preserves-dctf--1`,
for a general flat coefficient change: if the extension of scalars along `a_X : Λ_X ⟶ Λ'_X` is
exact, its left derived functor preserves bounded constructible complexes. It is computed
termwise, so `Hⁿ(Λ'_X ⊗ᴸ K) ≅ Λ'_X ⊗ Hⁿ(K)`, which vanishes where `Hⁿ(K)` does and is
constructible when `Hⁿ(K)` is. -/
theorem boundedConstructible_leftDerivedExtendScalars_obj {X : Scheme.{u}}
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ' X)
      ((L(Mod.extendScalars (coefficientMap a X))).obj K) := by
  obtain ⟨⟨m, n, hmn⟩, hc⟩ := (mem_boundedConstructible_iff _ K).1 hK
  have e (i : ℤ) := ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorHomologyFunctorIso
    i).app K
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨m, n, fun i hi ↦ ?_⟩, fun i ↦ ?_⟩
  · exact ((Mod.extendScalars (coefficientMap a X)).map_isZero (hmn i hi)).of_iso (e i).symm
  · exact (IsConstructibleModuleObject.extendScalars a (hc i)).of_iso (e i)

end AlgebraicGeometry.ProEtale.CondensedRing
