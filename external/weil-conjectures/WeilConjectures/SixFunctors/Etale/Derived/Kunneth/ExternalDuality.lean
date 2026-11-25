/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethVerdier

/-!
# External duality for correspondences with finite coefficients

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, `X` a separated
`k`-scheme of finite type with projections `p₁, p₂ : X ×_k X ⟶ X`, and `K ∈ Dctf(X, Λ)`. For a
correspondence `c : C ⟶ X ×_k X` with legs `c₁ = c ≫ p₁`, `c₂ = c ≫ p₂`, the sheaf of
cohomological correspondences is identified with the exceptional inverse image of
`P_X = K ⊠ 𝔻_X K` (blueprint `lemma-external-duality-trace-morphism`):

`𝓗_c(K) = RHom(c₂^* K, Rc₁^! K) ≅ Rc^! (K ⊠ 𝔻_X K)`

(`AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedUpperShriek_externalProduct`).
It combines the composition isomorphisms for `c₁ = c ≫ p₁` and `c₂ = c ≫ p₂`, the exceptional
inverse image of an internal hom
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedHom`) and the
Künneth–Verdier isomorphism `K ⊠ 𝔻_X K ≅ RHom(p₂^* K, Rp₁^! K)`
(`AlgebraicGeometry.Etale.nonempty_iso_kunnethVerdier`).

As for the other results of this chapter at finite coefficients, the statement is the existence
of an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `lemma-external-duality-trace-morphism`, second isomorphism, with finite
coefficients: for a separated `k`-scheme of finite type `X`, `K ∈ Dctf(X, Λ)` and a
correspondence `c : C ⟶ X ×_k X` with legs `c₁ = c ≫ p₁` and `c₂ = c ≫ p₂`,

`RHom(c₂^* K, Rc₁^! K) ≅ Rc^! (K ⊠ 𝔻_X K)`. -/
theorem nonempty_iso_derivedHom_rightDerivedUpperShriek_externalProduct {X C : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification a] [HasCompactification (pullback.fst a a)]
    (c : C ⟶ pullback a a) [HasCompactification c]
    [HasCompactification (c ≫ pullback.fst a a)] [QuasiCompact (c ≫ pullback.fst a a)]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty ((RHom(C)[ModuleCat.{u + 1} Λ].obj
          (op ((L((c ≫ pullback.snd a a)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
        ((R(c ≫ pullback.fst a a)^![Λ]).obj K) ≅
      (R(c)^![Λ]).obj (externalProduct (ModuleCat.{u + 1} Λ) a a K
        ((verdierDual Λ a).obj (op K)))) := by
  obtain ⟨κ⟩ := nonempty_iso_kunnethVerdier Λ a a hK hK
  obtain ⟨χ⟩ := nonempty_iso_rightDerivedUpperShriek_derivedHom Λ c
    ((L((pullback.snd a a)^*[ModuleCat.{u + 1} Λ])).obj K)
    ((R(pullback.fst a a)^![Λ]).obj K)
  obtain ⟨σ⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ c (pullback.fst a a)
  exact ⟨((RHom(C)[ModuleCat.{u + 1} Λ]).mapIso
        ((leftDerivedUpperStarComp _ c (pullback.snd a a)).app K).symm.op).app _ ≪≫
      ((RHom(C)[ModuleCat.{u + 1} Λ]).obj _).mapIso (σ.app K) ≪≫ χ.symm ≪≫
      (R(c)^![Λ]).mapIso κ.symm⟩

end Etale

end AlgebraicGeometry
