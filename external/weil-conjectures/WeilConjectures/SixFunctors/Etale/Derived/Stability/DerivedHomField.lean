/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDual
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSurjectivePullback
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# The finite-coefficient internal Hom estimate over an arbitrary field

For a finite coefficient ring `Λ` whose exponent is invertible on a field `k`, and `X` of finite
type over `k` with `dim X ≤ d`, the internal hom of two bounded constructible complexes of Tor
amplitude `[a, b]` and `[c, e]` is bounded constructible of Tor amplitude
`[c - b - 2d, e - a + 2d]`
(`AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_derivedHom_of_field`).

Over an algebraically closed field this is `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`
and `AlgebraicGeometry.Etale.boundedConstructible_derivedHom`. In general we base change to an
algebraic closure `k̄` of `k`: the internal hom commutes with this base change
(`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_of_generic`), the base change does
not increase the dimension, and bounded constructibility and Tor amplitude descend along the
surjective morphism `X_k̄ ⟶ X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Bounded constructibility descends along a surjective morphism** of quasi-compact
quasi-separated schemes, for a finite coefficient ring: boundedness descends since `g^*` is
faithful and exact, and constructibility of the homology sheaves descends by
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff_surjective_pullback`. -/
lemma boundedConstructible_of_leftDerivedUpperStar_of_surjective {X' X : Scheme.{u}}
    [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X] [QuasiSeparatedSpace X]
    (g : X' ⟶ X) [Surjective g]
    {N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : boundedConstructible (ModuleCat.{u + 1} Λ) X'
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X N := by
  have : ((g)^*[ModuleCat.{u + 1} Λ]).Faithful :=
    Etale.faithful_upperStar_of_surjective Λ g g.surjective
  obtain ⟨hb, hc⟩ := (boundedConstructible _ X').prop_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory _ g).app N) h
  refine ⟨((g)^*[ModuleCat.{u + 1} Λ]).bounded_of_bounded_mapDerivedCategory_obj hb,
    fun n ↦ ?_⟩
  rw [← Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf,
    Scheme.isConstructibleEtaleModuleSheaf_iff_surjective_pullback g,
    Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf]
  have : IsConstructibleSheaf ((D((g)^*[ModuleCat.{u + 1} Λ]) ⋙
      _root_.DerivedCategory.homologyFunctor _ n).obj N) := hc n
  exact IsConstructibleSheaf.of_iso
    ((((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app N).symm

/-- **Internal Hom of finite-coefficient constructible complexes over an arbitrary field.**
Let `Λ` be a finite ring whose exponent is invertible on a field `k`, and `X` of finite type over
`k` with `dim X ≤ d`. If `K` and `L` are bounded constructible with Tor amplitude in `[a, b]` and
`[c, e]`, then `RHom(K, L)` is bounded constructible with Tor amplitude in
`[c - b - 2d, e - a + 2d]`. Over an algebraic closure `k̄` of `k` this is
`AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`; the internal hom commutes with the base
change `g : X_k̄ ⟶ X`
(`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_of_generic`), and both properties
descend along the surjective `g`. -/
theorem boundedConstructible_and_torAmplitudeIn_derivedHom_of_field {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {a b c e : ℤ}
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hL : boundedConstructible (ModuleCat.{u + 1} Λ) X L)
    (hLt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c e L) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj L) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj L) := by
  let t : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let g := pullback.fst aX t
  let fT := pullback.snd aX t
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  have : CompactSpace (pullback aX t : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace fT
  have : IsNoetherian (pullback aX t : Scheme.{u}) :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian fT }
  have : HasInvertibleExponent Λ (pullback aX t : Scheme.{u}) := .of_hom (g ≫ aX)
  have : Surjective t := ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) g K L) :=
    isIso_derivedHomUpperStarComparison_of_generic Λ (𝟙 _) t
      (fun _ ↦ Subsingleton.elim _ _) aX (IsPullback.of_hasPullback aX t)
      ⟨hK, a, b, hKt⟩ hL
  let ρ := asIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) g K L)
  have hd' : topologicalKrullDim (pullback aX t : Scheme.{u}) ≤ (d : WithBot ℕ∞) :=
    (topologicalKrullDim_pullback_le_of_field aX t).trans hd
  have hK' := boundedConstructible_leftDerivedUpperStar _ g hK
  have hL' := boundedConstructible_leftDerivedUpperStar _ g hL
  have hKt' := torAmplitudeIn_leftDerivedUpperStar _ g a b hKt
  have hLt' := torAmplitudeIn_leftDerivedUpperStar _ g c e hLt
  refine ⟨boundedConstructible_of_leftDerivedUpperStar_of_surjective Λ g
    ((boundedConstructible _ _).prop_of_iso ρ.symm
      (boundedConstructible_derivedHom Λ fT a b c e hK' hKt' hL' hLt')),
    torAmplitudeIn_of_leftDerivedUpperStar_of_surjective Λ g g.surjective
      ((torAmplitudeIn _ _ _ _).prop_of_iso ρ.symm
        (torAmplitudeIn_derivedHom Λ fT d hd' a b c e hK' hKt' hL' hLt'))⟩

end Etale

end AlgebraicGeometry
