/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension

/-!
# The projection formula on the pro-étale site at the stage `ℚ̄_ℓ`

The stage `ℚ̄_ℓ` of the `ℓ`-adic formalism is the `2`-colimit of the rational stages `E`, over the
finite extensions `E/ℚ_ℓ` inside `ℚ̄_ℓ`, along the extension of scalars functors. An object of
the stage `ℚ̄_ℓ` is represented at some finite stage `E`, and it is carried to every larger
finite stage `E' ⊇ E` by extension of scalars `𝒪_{E'} ⊗_{𝒪_E} -`. This file proves that the
projection map over `E'` at the scalar extensions of pro-étale realizations of `𝒪_E`-objects is an
isomorphism, integrally and after rationalization; so the projection map at the stage `ℚ̄_ℓ`, which
is represented at the finite stages `E'`, is an isomorphism.

## Main statements

- `AlgebraicGeometry.ProEtale.hasProjectionFormula_extendScalars_of_derivedCompleteIntegral`:
  the integral projection map over `𝒪_{E'}` at the scalar extensions of pro-étale realizations of
  bounded constructible, derived complete `𝒪_E`-complexes of finite Tor amplitude is an
  isomorphism.
- `AlgebraicGeometry.ProEtale.isIso_rationalization_map_projectionMap_extendScalars`: the same
  after rationalization, the stage `ℚ̄_ℓ` of `sk-thm-sf-pf-proetale`.

## Implementation notes

The blueprint defines `D(Y, ℚ̄_ℓ)` as the category `C_Y` of pairs `(E, K)`, with
`Hom((E, K), (E', K'))` the colimit over finite `L ⊇ E, E'` of the morphisms
`K ⊗_E L ⟶ K' ⊗_{E'} L` at the stage `L`, composition being computed at a common stage. The
projection map at `ℚ̄_ℓ` of objects represented at `E` is the class of the projection
map at any stage `E' ⊇ E` of their scalar extensions, and a morphism of `C_Y` represented by an
isomorphism at some stage is an isomorphism of `C_Y` (its inverse is represented at the same
stage). So the statement here, at every stage `E' ⊇ E`, is the `ℚ̄_ℓ` statement with the `Hom`
groups of `C_Y` unfolded. The Bhatt–Scholze model `AlgebraicGeometry.ProEtale.AdicSheaf` of the
stage `ℚ̄_ℓ` carries no derived tensor product, `Rf_!` or projection map yet.

The ring `𝒪_{E'}` is a finite free algebra over the Noetherian ring `𝒪_E`
(`PadicAlgCl.finite_integersShrinkMap`, `PadicAlgCl.free_integersShrinkMap`), so extension of
scalars carries the projection formula over `𝒪_E` to the one over `𝒪_{E'}`
(`AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_extendScalars`), and the
former is the integral stage
(`AlgebraicGeometry.ProEtale.hasProjectionFormula_of_derivedCompleteIntegral`).
-/

@[expose] public section

universe w u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section General

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  [Module.Free R S] [Nontrivial R] [IsNoetherianRing R] [IsNoetherianRing S] {X Y : Scheme.{u}}

/-- Extension of scalars along a finite free algebra `S` over a Noetherian ring `R` carries the
projection formula for `Rf_!` over `R` to the one over `S`: this is
`AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_extendScalars` for the chosen
compactification of `f`. -/
theorem hasProjectionFormula_extendScalars (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    (h : HasProjectionFormula (ModuleCat.{u + 1} R) f K L) :
    HasProjectionFormula (ModuleCat.{u + 1} S) f
      ((L(sheafExtendScalars (algebraMap R S) X)).obj K)
      ((L(sheafExtendScalars (algebraMap R S) Y)).obj L) :=
  hasProjectionFormulaOfCompactification_extendScalars _ K L h

end General

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage `E`. -/
local notation "𝐌" =>
  @ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)) CommRing.toRing

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_{E'}` of the integral stage `E'`. The ring structure is
the one underlying the commutative ring structure, as in the monoidal structure of `ModuleCat`;
this keeps the kernel from unfolding the two ring structures on `Shrink 𝒪_{E'}`. -/
local notation "𝐌'" =>
  @ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E')) CommRing.toRing

set_option hygiene false in
/-- Extension of scalars `𝒪_{E'} ⊗_{𝒪_E} -` on derived categories of pro-étale sheaves. -/
local notation "𝐍" => fun (X : Scheme.{u}) ↦ L(sheafExtendScalars
  (algebraMap (Shrink.{u + 1} (PadicAlgCl.integers l E))
    (Shrink.{u + 1} (PadicAlgCl.integers l E'))) X)

variable (l : ℕ) [Fact l.Prime] (E E' : Type w) [Field E] [Field E'] [Algebra ℚ_[l] E]
  [Algebra ℚ_[l] E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)]
  [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E'] [Algebra E E']
  [IsScalarTower E E' (PadicAlgCl l)] [Small.{u + 1} E] [Small.{u + 1} E']

/-- `𝒪_{E'}` as an `𝒪_E`-algebra. -/
noncomputable local instance : Algebra (Shrink.{u + 1} (PadicAlgCl.integers l E))
    (Shrink.{u + 1} (PadicAlgCl.integers l E')) :=
  (PadicAlgCl.integersShrinkMap.{w, u} l E E').toAlgebra

local instance : Module.Finite (Shrink.{u + 1} (PadicAlgCl.integers l E))
    (Shrink.{u + 1} (PadicAlgCl.integers l E')) :=
  PadicAlgCl.finite_integersShrinkMap.{w, u} l E E'

local instance : Module.Free (Shrink.{u + 1} (PadicAlgCl.integers l E))
    (Shrink.{u + 1} (PadicAlgCl.integers l E')) :=
  PadicAlgCl.free_integersShrinkMap.{w, u} l E E'

local instance : IsDomain (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  (PadicAlgCl.shrinkRingEquiv.{w, u} l E).symm.toMulEquiv.isDomain _

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {X Y : Scheme.{u}}

/-- Blueprints `sk-thm-sf-pf-proetale` and `thm-sf-pf-proetale`, the integral stages `𝒪_{E'}`
for scalar extensions.

Let `E ⊆ E'` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, and let `K ≅ ν^* K₀` and `L ≅ ν^* L₀` be
the pro-étale realizations of bounded constructible, derived complete complexes `K₀`, `L₀` of
étale sheaves of `𝒪_E`-modules of finite Tor amplitude, such that both sides of the étale
projection map at `K₀` and `L₀` are derived complete. Then the projection map over `𝒪_{E'}` at
the scalar extensions `𝒪_{E'} ⊗ᴸ_{𝒪_E} K` and `𝒪_{E'} ⊗ᴸ_{𝒪_E} L` is an isomorphism: it is the
scalar extension of the projection map over `𝒪_E`
(`AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_extendScalars`, `𝒪_{E'}`
being finite free over `𝒪_E`), an isomorphism by the integral stage
(`AlgebraicGeometry.ProEtale.hasProjectionFormula_of_derivedCompleteIntegral`). -/
theorem hasProjectionFormula_extendScalars_of_derivedCompleteIntegral (f : X ⟶ Y)
    [HasCompactification f]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) 𝐌)}
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) 𝐌)}
    {K₀ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌)}
    {L₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌)}
    (eK : D(ν^*(X)[𝐌]).obj K₀ ≅ K) (eL : D(ν^*(Y)[𝐌]).obj L₀ ≅ L)
    (hKc : Etale.DerivedCategory.boundedConstructible 𝐌 X K₀)
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K₀)
    (hKt : Etale.DerivedCategory.finiteTorAmplitude 𝐌 X K₀)
    (hLc : Etale.DerivedCategory.boundedConstructible 𝐌 Y L₀)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L₀)
    (hLt : Etale.DerivedCategory.finiteTorAmplitude 𝐌 Y L₀)
    (hs : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      (((Etale.derivedTensor 𝐌 Y).obj ((Etale.rightDerivedLowerShriek 𝐌 f).obj K₀)).obj L₀))
    (ht : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((Etale.rightDerivedLowerShriek 𝐌 f).obj
        (((Etale.derivedTensor 𝐌 X).obj K₀).obj ((L(Etale.upperStar 𝐌 f)).obj L₀)))) :
    HasProjectionFormula 𝐌' f ((𝐍 X).obj K) ((𝐍 Y).obj L) := by
  have h := hasProjectionFormula_of_derivedCompleteIntegral l E f eK eL hKc hK hKt hLc hL hLt
    hs ht
  exact hasProjectionFormula_extendScalars f K L h

/-- Blueprints `sk-thm-sf-pf-proetale` and `thm-sf-pf-proetale`, the stage `ℚ̄_ℓ`.

An object of the stage `ℚ̄_ℓ` is represented at a finite stage `E`, and it is carried to every
larger finite stage `E' ⊇ E` inside `ℚ̄_ℓ` by extension of scalars; the projection map at the
stage `ℚ̄_ℓ` is represented at the stages `E'`. Let `K ≅ ν^* K₀` and `L ≅ ν^* L₀` be the
pro-étale realizations of bounded constructible, derived complete complexes `K₀`, `L₀` of étale
sheaves of `𝒪_E`-modules of finite Tor amplitude. Then for every `E'`, the projection map over
`E'` at the scalar extensions of `K` and `L`, the image under the rationalization
`D(Y_proét, 𝒪_{E'}) ⥤ D(Y_proét, 𝒪_{E'})[1/ℓ]` of the projection map over `𝒪_{E'}`, is an
isomorphism
(`AlgebraicGeometry.ProEtale.hasProjectionFormula_extendScalars_of_derivedCompleteIntegral`,
blueprint `lemma-kunneth-formula-compact-supports--3`). -/
theorem isIso_rationalization_map_projectionMap_extendScalars (f : X ⟶ Y)
    [HasCompactification f]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) 𝐌)}
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) 𝐌)}
    {K₀ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌)}
    {L₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌)}
    (eK : D(ν^*(X)[𝐌]).obj K₀ ≅ K) (eL : D(ν^*(Y)[𝐌]).obj L₀ ≅ L)
    (hKc : Etale.DerivedCategory.boundedConstructible 𝐌 X K₀)
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K₀)
    (hKt : Etale.DerivedCategory.finiteTorAmplitude 𝐌 X K₀)
    (hLc : Etale.DerivedCategory.boundedConstructible 𝐌 Y L₀)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L₀)
    (hLt : Etale.DerivedCategory.finiteTorAmplitude 𝐌 Y L₀)
    (hs : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      (((Etale.derivedTensor 𝐌 Y).obj ((Etale.rightDerivedLowerShriek 𝐌 f).obj K₀)).obj L₀))
    (ht : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((Etale.rightDerivedLowerShriek 𝐌 f).obj
        (((Etale.derivedTensor 𝐌 X).obj K₀).obj ((L(Etale.upperStar 𝐌 f)).obj L₀)))) :
    IsIso ((Rationalization.Q (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E')))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) 𝐌'))).map
        (((projectionMap 𝐌' f).app ((𝐍 X).obj K)).app ((𝐍 Y).obj L))) :=
  @Functor.map_isIso _ _ _ _ _ _ _ _
    (hasProjectionFormula_extendScalars_of_derivedCompleteIntegral l E E' f eK eL
      hKc hK hKt hLc hL hLt hs ht)

end AlgebraicGeometry.ProEtale
