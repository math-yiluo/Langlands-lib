/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.AdicBaseChangeTower
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.TorsionSmoothBaseChange
public import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow

/-!
# Adic, rational and `ℚ̄_ℓ`-coefficient smooth base change on the pro-étale site

Fix a Cartesian square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` smooth and `g` quasi-compact and quasi-separated. Let `R` be a coefficient ring with an
ideal `I` containing an integer `N` invertible on `S`: the intended case is `R = 𝒪_E`,
`I = 𝔪_E` and `N = ℓ` for a finite extension `E` of `ℚ_ℓ`. For an object `K` of
`D(T_proét, R)` write `K_n = K ⊗ᴸ R/Iⁿ` for its reductions.

The completed exchange map `Lp^*_comp Rg_* K ⟶ Rh_* Le^*_comp K` is the derived limit of the
levelwise exchange maps `Ex_{K_n} : p^* Rg_* K_n ⟶ Rh_* e^* K_n`
(`AlgebraicGeometry.ProEtale.adicBaseChangeTowerMap`, see
`WeilConjectures.SixFunctors.ProEtale.BaseChange.AdicBaseChangeTower`). Each `K_n` is killed by
`Nⁿ`, so when the `K_n` are of étale origin with bounded constructible cohomology the finite
pro-étale smooth base change theorem
(`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_smooth_of_nsmul_eq_zero`) makes
every levelwise exchange map an isomorphism, and derived limits of isomorphisms of towers are
isomorphisms.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_adicBaseChangeTowerMap`: the levelwise exchange maps are
  isomorphisms.
- `AlgebraicGeometry.ProEtale.isIso_of_adic_smooth_base_change` and
  `AlgebraicGeometry.ProEtale.exists_iso_of_adic_smooth_base_change`: adic smooth base change.
- `AlgebraicGeometry.ProEtale.isIso_fromIntegral_map_of_e_coefficient_smooth_base_change`:
  `E`-coefficient smooth base change.
- `AlgebraicGeometry.ProEtale.isIso_fromIntegral_map_of_qlbar_coefficient_smooth_base_change`:
  `ℚ̄_ℓ`-coefficient smooth base change.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]


/-- The prime `ℓ` lies in the maximal ideal `𝔪_E`, read inside the universe `u + 1` copy
`Shrink 𝒪_E`. -/
lemma natCast_mem_maximalIdealShrink [Small.{u + 1} E] :
    (l : Shrink.{u + 1} (integers l E)) ∈ maximalIdealShrink.{w, u} l E := by
  rw [maximalIdealShrink, ← map_natCast (shrinkRingEquiv.{w, u} l E) l]
  exact Ideal.mem_map_of_mem _ (natCast_mem_maximalIdeal_integers l E)

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme _root_.DerivedCategory

section Integral

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R}

set_option hygiene false in
/-- The derived category `D(T_proét, R)` of pro-étale sheaves of `R`-modules. -/
local notation "𝐃(" T ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))

variable {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

variable (p) in
/-- The levelwise exchange maps of a Cartesian square with `p` smooth and `g` quasi-compact and
quasi-separated are isomorphisms at an object `K` whose reductions are of étale origin with
bounded constructible cohomology, when `I` contains an integer `N` invertible on `S`: each
reduction `K_n` is killed by `Nⁿ`, and the finite-level smooth base change applies. -/
theorem isIso_adicBaseChangeTowerMap [Smooth p] [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {N : ℕ} (hN₀ : N ≠ 0) (hNS : IsUnit (N : Γ(S, ⊤)))
    (hNI : (N : R) ∈ I) (K : 𝐃(T))
    (hK : ∀ n : ℕ, ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) T
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n))) :
    IsIso (adicBaseChangeTowerMap I sq.toCommSq K) :=
  isIso_adicBaseChangeTowerMap_of_forall sq.toCommSq K fun n ↦
    isIso_derivedBaseChangeMap_app_of_smooth_of_nsmul_eq_zero R p sq (pow_ne_zero n hN₀)
      (by rw [Nat.cast_pow]; exact hNS.pow n) _ (hK n)
      (nsmul_id_derivedCompletionDiagram_obj hNI K n)

variable (p) in
/-- Adic smooth base change.

For a Cartesian square with `p` smooth and `g` quasi-compact and quasi-separated, an ideal `I`
containing an integer `N` invertible on `S`, and an object `K` of `D(T_proét, R)` whose
reductions `K_n = K ⊗ᴸ R/Iⁿ` are of étale origin with bounded constructible cohomology (for
instance `K ∈ Dᵇc(T_proét, R)`,
`DerivedCategory.boundedConstructibleComplete.reductionsBoundedConstructible`),
the completed exchange map `R lim_n p^* Rg_* K_n ⟶ R lim_n Rh_* e^* K_n` is an isomorphism:
every morphism `u` completing the morphism of Milnor triangles induced by the levelwise
exchange maps is an isomorphism. Its target is `Rh_* Le^*_comp K`
(`AlgebraicGeometry.ProEtale.isHomotopyLimit_mapCone_rightDerivedLowerStar`), and both sides are
derived complete when `I` is principal
(`AlgebraicGeometry.ProEtale.derivedComplete_of_isHomotopyLimit_map`). -/
theorem isIso_of_adic_smooth_base_change [Smooth p] [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {N : ℕ} (hN₀ : N ≠ 0) (hNS : IsUnit (N : Γ(S, ⊤)))
    (hNI : (N : R) ∈ I) (K : 𝐃(T))
    (hK : ∀ n : ℕ, ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) T
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n)))
    {PF : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
      R((g)_*[ModuleCat.{u + 1} R]) ⋙ L((p)^*[ModuleCat.{u + 1} R])).obj (op n)}
    (hPF : IsLimit PF)
    {PG : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
      L((e)^*[ModuleCat.{u + 1} R]) ⋙ R((h)_*[ModuleCat.{u + 1} R])).obj (op n)}
    (hPG : IsLimit PG) {A B : 𝐃(X)} {cA : A ⟶ PF.pt} {δA : PF.pt ⟶ A⟦(1 : ℤ)⟧}
    {cB : B ⟶ PG.pt} {δB : PG.pt ⟶ B⟦(1 : ℤ)⟧}
    (hA : Triangle.mk cA (𝟙 _ - towerShift hPF) δA ∈ distTriang _)
    (hB : Triangle.mk cB (𝟙 _ - towerShift hPG) δB ∈ distTriang _) (u : A ⟶ B)
    (hu₁ : cA ≫ productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap I sq.toCommSq K) =
      u ≫ cB)
    (hu₃ : δA ≫ u⟦(1 : ℤ)⟧' =
      productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap I sq.toCommSq K) ≫ δB) :
    IsIso u :=
  have := isIso_adicBaseChangeTowerMap p sq hN₀ hNS hNI K hK
  isIso_of_isIso_adicBaseChangeTowerMap sq.toCommSq K hPF hPG hA hB u hu₁ hu₃

variable (p) in
/-- Adic smooth base change, as an isomorphism.

In the setting of `AlgebraicGeometry.ProEtale.isIso_of_adic_smooth_base_change`, for homotopy
limit cones `c₁` of `n ↦ p^* Rg_* K_n` (computing `Lp^*_comp Rg_* K`) and `c₂` of
`n ↦ e^* K_n` (computing `Le^*_comp K`), there is an isomorphism
`Lp^*_comp Rg_* K ≅ Rh_* Le^*_comp K` compatible with the levelwise exchange maps. -/
theorem exists_iso_of_adic_smooth_base_change [Smooth p] [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {N : ℕ} (hN₀ : N ≠ 0) (hNS : IsUnit (N : Γ(S, ⊤)))
    (hNI : (N : R) ∈ I) (K : 𝐃(T))
    (hK : ∀ n : ℕ, ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) T
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n)))
    {c₁ : Cone (derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
      R((g)_*[ModuleCat.{u + 1} R]) ⋙ L((p)^*[ModuleCat.{u + 1} R]))}
    (hc₁ : IsHomotopyLimit c₁)
    {c₂ : Cone (derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
      L((e)^*[ModuleCat.{u + 1} R]))} (hc₂ : IsHomotopyLimit c₂) :
    ∃ φ : c₁.pt ≅ R((h)_*[ModuleCat.{u + 1} R]).obj c₂.pt, ∀ n : ℕ,
      φ.hom ≫ R((h)_*[ModuleCat.{u + 1} R]).map (c₂.π.app (op n)) =
        c₁.π.app (op n) ≫ (adicBaseChangeTowerMap I sq.toCommSq K).app (op n) :=
  have := isIso_adicBaseChangeTowerMap p sq hN₀ hNS hNI K hK
  exists_iso_of_isIso_adicBaseChangeTowerMap sq.toCommSq K hc₁ hc₂

end Integral

section ECoefficient

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E]

set_option hygiene false in
/-- The derived category `D(T_proét, 𝒪_E)` of pro-étale sheaves of `𝒪_E`-modules. -/
local notation "𝐃(" T ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))))

set_option hygiene false in
/-- The coefficient category `Mod(𝒪_E)`. -/
local notation "𝐌" => ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))

set_option hygiene false in
/-- The maximal ideal `𝔪_E` of `𝒪_E`. -/
local notation "𝔪" => PadicAlgCl.maximalIdealShrink.{w, u} l E

variable {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

variable (p) in
/-- `E`-coefficient smooth base change.

For a Cartesian square with `p` smooth, `g` quasi-compact and quasi-separated and `ℓ` invertible
on `S`, and an object `K_E` of `D_comp(T, E)` with a finite-level étale admissible integral
lattice `Λ` (`AlgebraicGeometry.ProEtale.IntegralLattice`; the hypothesis `hΛ` is
`Λ.IsFiniteLevelEtaleAdmissible`, stated explicitly; every lattice is finite-level étale
admissible, `AlgebraicGeometry.ProEtale.IntegralLattice.isFiniteLevelEtaleAdmissible`), the
completed exchange map `u : R lim_n p^* Rg_* L_n ⟶ R lim_n Rh_* e^* L_n` of the lattice
`L = Λ.obj` becomes an isomorphism in `D_comp(X, E)`: by the adic theorem it is an isomorphism in
`D_comp(X, 𝒪_E)`, and the central localization inverting `ℓ` preserves isomorphisms. -/
theorem isIso_fromIntegral_map_of_e_coefficient_smooth_base_change [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p) (hlS : IsUnit (l : Γ(S, ⊤)))
    {K : DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology T) l E}
    (Λ : IntegralLattice l E K)
    (hΛ : ∀ n : ℕ, ProEtale.DerivedCategory.boundedConstructible 𝐌 T
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj).obj (op n)))
    {PF : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj ⋙
      R((g)_*[𝐌]) ⋙ L((p)^*[𝐌])).obj (op n)}
    (hPF : IsLimit PF)
    {PG : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj ⋙
      L((e)^*[𝐌]) ⋙ R((h)_*[𝐌])).obj (op n)}
    (hPG : IsLimit PG) {A B : 𝐃(X)} {cA : A ⟶ PF.pt} {δA : PF.pt ⟶ A⟦(1 : ℤ)⟧}
    {cB : B ⟶ PG.pt} {δB : PG.pt ⟶ B⟦(1 : ℤ)⟧}
    (hA : Triangle.mk cA (𝟙 _ - towerShift hPF) δA ∈ distTriang _)
    (hB : Triangle.mk cB (𝟙 _ - towerShift hPG) δB ∈ distTriang _) (u : A ⟶ B)
    (hu₁ : cA ≫
        productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap 𝔪 sq.toCommSq Λ.obj) =
      u ≫ cB)
    (hu₃ : δA ≫ u⟦(1 : ℤ)⟧' =
      productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap 𝔪 sq.toCommSq Λ.obj) ≫ δB) :
    IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E).map
      (ObjectProperty.homMk (P := derivedCompleteIntegral (Scheme.ProEt.topology X) l E)
        (X := ⟨A, derivedCompleteIntegral_adicSource l E g p Λ.obj hPF hA⟩)
        (Y := ⟨B, derivedCompleteIntegral_adicTarget l E e h Λ.obj hPG hB⟩) u)) :=
  have := isIso_adicBaseChangeTowerMap p sq (Fact.out : l.Prime).ne_zero hlS
    (PadicAlgCl.natCast_mem_maximalIdealShrink l E) Λ.obj hΛ
  isIso_fromIntegral_map_of_isIso_adicBaseChangeTowerMap l E sq.toCommSq Λ.obj hPF hPG hA hB u
    hu₁ hu₃

end ECoefficient

section QlbarCoefficient

variable (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

set_option hygiene false in
/-- The derived category `D(T_proét, 𝒪_E)` of pro-étale sheaves of `𝒪_E`-modules. -/
local notation "𝐃(" T ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))))

set_option hygiene false in
/-- The coefficient category `Mod(𝒪_E)`. -/
local notation "𝐌" => ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))

set_option hygiene false in
/-- The maximal ideal `𝔪_E` of `𝒪_E`. -/
local notation "𝔪" => PadicAlgCl.maximalIdealShrink.{0, u} l E

variable {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

variable (p) in
/-- `ℚ̄_ℓ`-coefficient smooth base change.

An object of `D_comp(T, ℚ̄_ℓ)` represented at a finite stage is an object `K_E` of
`D_comp(T, E)` for a finite subextension `E` of `ℚ̄_ℓ = PadicAlgCl l` over `ℚ_ℓ`, and the
`ℚ̄_ℓ`-coefficient exchange map is the one of the stage. For every such stage and every
integral lattice of `K_E`, the finite-stage exchange map is an isomorphism in `D_comp(X, E)`;
this is
`AlgebraicGeometry.ProEtale.isIso_fromIntegral_map_of_e_coefficient_smooth_base_change` applied
to the stage `E`, whose hypotheses hold at every finite stage. -/
theorem isIso_fromIntegral_map_of_qlbar_coefficient_smooth_base_change [Smooth p]
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p) (hlS : IsUnit (l : Γ(S, ⊤)))
    {K : DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology T) l E}
    (Λ : IntegralLattice l E K)
    (hΛ : ∀ n : ℕ, ProEtale.DerivedCategory.boundedConstructible 𝐌 T
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj).obj (op n)))
    {PF : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj ⋙
      R((g)_*[𝐌]) ⋙ L((p)^*[𝐌])).obj (op n)}
    (hPF : IsLimit PF)
    {PG : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj ⋙
      L((e)^*[𝐌]) ⋙ R((h)_*[𝐌])).obj (op n)}
    (hPG : IsLimit PG) {A B : 𝐃(X)} {cA : A ⟶ PF.pt} {δA : PF.pt ⟶ A⟦(1 : ℤ)⟧}
    {cB : B ⟶ PG.pt} {δB : PG.pt ⟶ B⟦(1 : ℤ)⟧}
    (hA : Triangle.mk cA (𝟙 _ - towerShift hPF) δA ∈ distTriang _)
    (hB : Triangle.mk cB (𝟙 _ - towerShift hPG) δB ∈ distTriang _) (u : A ⟶ B)
    (hu₁ : cA ≫
        productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap 𝔪 sq.toCommSq Λ.obj) =
      u ≫ cB)
    (hu₃ : δA ≫ u⟦(1 : ℤ)⟧' =
      productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap 𝔪 sq.toCommSq Λ.obj) ≫ δB) :
    IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E).map
      (ObjectProperty.homMk (P := derivedCompleteIntegral (Scheme.ProEt.topology X) l E)
        (X := ⟨A, derivedCompleteIntegral_adicSource l E g p Λ.obj hPF hA⟩)
        (Y := ⟨B, derivedCompleteIntegral_adicTarget l E e h Λ.obj hPG hB⟩) u)) :=
  isIso_fromIntegral_map_of_e_coefficient_smooth_base_change l E p sq hlS Λ hΛ hPF hPG hA hB u
    hu₁ hu₃

end QlbarCoefficient

end AlgebraicGeometry.ProEtale
