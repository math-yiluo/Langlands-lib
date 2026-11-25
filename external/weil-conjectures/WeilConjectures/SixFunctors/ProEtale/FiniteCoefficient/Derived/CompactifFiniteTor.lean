/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AmbientAdjointClass

/-!
# Compact support along an arbitrary compactification preserves `Dctf`

Let `Λ` be a finite ring whose exponent is invertible on a finite-type `k`-scheme `Y`, and let
`c = (X ⟶[j] X̄ ⟶[p] Y)` be a compactification of `f : X ⟶ Y`. Then the pro-étale
compact-support functor `Rf_!(c) = Rp_* ∘ j_!` maps `Dctf(X, Λ)` into `Dctf(Y, Λ)`
(`AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedLowerShriekOfCompactification`,
part of blueprint `proposition-construction-independence-rf-shriek`). On `ν^* G` it is
`ν^* Rf_!^{ét}(c) G`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationWitnessIso`), and the étale
`Rf_!^{ét}(c)` preserves `Dctf`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerShriekOfCompactification`): the
extension by zero along the quasi-compact `j` does, and so does the direct image along the proper
`p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-- The étale compact-support functor `Rf_!(c) = Rp_* ∘ j_!` attached to an arbitrary
compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`, over a finite-type `k`-scheme `Y`, maps
`Dctf(X, Λ)` into `Dctf(Y, Λ)` for a finite `Λ` whose exponent is invertible on `Y`. -/
theorem Etale.constructibleFiniteTor_rightDerivedLowerShriekOfCompactification {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] {f : X ⟶ Y} (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aY)
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace (c.g ≫ aY)
  have : IsNoetherian c.Z := {}
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasInvertibleExponent Λ c.Z := .of_hom c.g
  obtain ⟨hbc, a, b, hta⟩ := hK
  have h := Etale.constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek Λ c.i a b
    ⟨⟨hbc, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta⟩, hta⟩
  exact Etale.constructibleFiniteTor_rightDerivedLowerStar_of_isProper Λ (c.g ≫ aY) aY c.g rfl
    ⟨h.1.1, a, b, h.2⟩

namespace ProEtale

/-- Part of blueprint `proposition-construction-independence-rf-shriek`: the pro-étale
compact-support functor `Rf_!(c) = Rp_* ∘ j_!` attached to an arbitrary compactification `c` of `f`,
over a finite-type `k`-scheme `Y`, maps `Dctf(X, Λ)` into `Dctf(Y, Λ)` for a finite `Λ` whose
exponent is invertible on `Y`. -/
theorem constructibleFiniteTor_rightDerivedLowerShriekOfCompactification {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] {f : X ⟶ Y} (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K) := by
  obtain ⟨⟨G, hG, ⟨e⟩⟩, a, b, hab⟩ := hK
  have hGt : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X G :=
    ⟨hG, a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b G).1
      ((DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm hab)⟩
  exact (DerivedCategory.constructibleFiniteTor _ Y).prop_of_iso
    (rightDerivedLowerShriekOfCompactificationWitnessIso _ c hG.1.1 e).symm
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_rightDerivedLowerShriekOfCompactification Λ aY c hGt))

end ProEtale

end AlgebraicGeometry
