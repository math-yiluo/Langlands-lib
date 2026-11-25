/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# The completed exchange map of a square of schemes on the pro-étale site

Fix a commutative square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

and a coefficient ring `R` with an ideal `I`. For an object `K` of `D(T_proét, R)` write
`K_n = K ⊗ᴸ R/Iⁿ` for its reductions (`DerivedCategory.derivedCompletionDiagram`).

The completed exchange map
`Lp^*_comp Rg_* K ⟶ Rh_* Le^*_comp K` is, up to the canonical identifications of the completed
operations with the derived limits of their finite levels, the derived limit
`R lim_n Ex_{K_n} : R lim_n p^* Rg_* K_n ⟶ R lim_n Rh_* e^* K_n` of the levelwise exchange maps
`Ex_{K_n} : p^* Rg_* K_n ⟶ Rh_* e^* K_n`. The levelwise exchange maps form the morphism of towers
`AlgebraicGeometry.ProEtale.adicBaseChangeTowerMap`. In a triangulated category the derived limit
of a morphism of towers is only defined up to a choice: it is any morphism `u` completing the
morphism of Milnor triangles `R lim ⟶ ∏ ⟶ ∏ ⟶ R lim⟦1⟧` induced by the morphism of towers. The
target `R lim_n Rh_* e^* K_n` is `Rh_*` of the derived limit of the `e^* K_n`, that is
`Rh_* Le^*_comp K` (`AlgebraicGeometry.ProEtale.isHomotopyLimit_mapCone_rightDerivedLowerStar`).

This file records the formal consequences of the levelwise exchange maps being isomorphisms:
every completed exchange map is then an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_of_isIso_adicBaseChangeTowerMap`), the two sides are
isomorphic compatibly with the levelwise exchange maps
(`AlgebraicGeometry.ProEtale.exists_iso_of_isIso_adicBaseChangeTowerMap`), and both sides are
derived complete when `I = (ϖ)`. The input, that the levelwise exchange maps are isomorphisms for
a smooth `p`, is the finite-level smooth base change, used in
`WeilConjectures.SixFunctors.ProEtale.BaseChange.AdicSmoothBaseChange`.

## Main definitions

- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleComplete`: the integral
  category `Dᵇc(T_proét, R)`.
- `AlgebraicGeometry.ProEtale.adicBaseChangeTowerMap`: the levelwise exchange maps.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

/-- A whiskering `F ◫ α` is an isomorphism as soon as `α` is one at every object `F.obj X`.
Stated for abstract functors: for concrete derived functors `G`, the kernel can take very long
to match `(F ⋙ G).obj X` against `G.obj (F.obj X)`. -/
lemma isIso_whiskerLeft_of_isIso_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [∀ X, IsIso (α.app (F.obj X))] :
    IsIso (Functor.whiskerLeft F α) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  rw [Functor.whiskerLeft_app]
  infer_instance

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme _root_.DerivedCategory

section Integral

variable {R : Type (u + 1)} [CommRing R] (I : Ideal R)

set_option hygiene false in
/-- The derived category `D(T_proét, R)` of pro-étale sheaves of `R`-modules. -/
local notation "𝐃(" T ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))

/-- The integral category `Dᵇc(T_proét, R)`, for `R = 𝒪_E` and `I = 𝔪_E`, as an object
property of `D(T_proét, R)`: the derived complete objects `K` whose reduction tower
`K_n = K ⊗ᴸ R/Iⁿ` is uniformly bounded constructible with étale origins, that is, every `K_n` is
of étale origin with bounded constructible cohomology
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`), with cohomology in one
common interval `[a, b]`. -/
def DerivedCategory.boundedConstructibleComplete (T : Scheme.{u}) : ObjectProperty 𝐃(T) :=
  fun K ↦ derivedComplete (Scheme.ProEt.topology T) I K ∧ ∃ a b : ℤ, ∀ n : ℕ,
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) T
        ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n)) ∧
      TStructure.t.IsGE ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n)) a ∧
      TStructure.t.IsLE ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n)) b

/-- The reductions `K_n = K ⊗ᴸ R/Iⁿ` of `K` are of étale origin with bounded constructible
cohomology. -/
def DerivedCategory.ReductionsBoundedConstructible (T : Scheme.{u}) (K : 𝐃(T)) : Prop :=
  ∀ n : ℕ, ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) T
    ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n))

/-- The reductions of an object of `Dᵇc(T_proét, R)` are of étale origin with bounded
constructible cohomology. -/
lemma DerivedCategory.boundedConstructibleComplete.reductionsBoundedConstructible
    {T : Scheme.{u}} {K : 𝐃(T)} (hK : DerivedCategory.boundedConstructibleComplete I T K) :
    DerivedCategory.ReductionsBoundedConstructible I T K := by
  obtain ⟨-, a, b, hab⟩ := hK
  exact fun n ↦ (hab n).1

variable {I}

/-- An integer `N` lying in `I` acts by zero on the `n`-th reduction `K ⊗ᴸ R/Iⁿ` through its
`n`-th power. -/
lemma nsmul_id_derivedCompletionDiagram_obj {T : Scheme.{u}} {N : ℕ} (hNI : (N : R) ∈ I)
    (K : 𝐃(T)) (n : ℕ) :
    N ^ n • 𝟙 ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n)) = 0 := by
  rw [← Nat.cast_smul_eq_nsmul R, Nat.cast_pow]
  exact smul_id_derivedCompletionDiagram_obj _ hNI K n

/-- An element `ϖ ∈ I` acts by zero on the image `Φ (K ⊗ᴸ R/Iⁿ)` of the `n`-th reduction under
an `R`-linear functor `Φ`, through its `n`-th power. -/
lemma smul_id_map_derivedCompletionDiagram_obj {T T' : Scheme.{u}} {ϖ : R} (hϖ : ϖ ∈ I)
    (K : 𝐃(T)) (Φ : 𝐃(T) ⥤ 𝐃(T')) [Φ.Linear R] (n : ℕ) :
    ϖ ^ n • 𝟙 (Φ.obj ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n))) =
      0 := by
  rw [← Φ.map_id, ← Functor.map_smul, smul_id_derivedCompletionDiagram_obj _ hϖ K n,
    ← zero_smul R (0 : (derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n) ⟶ _),
    Functor.map_smul, zero_smul]

/-- The point of a homotopy limit of a tower of `D(T_proét, R)` whose terms are killed by powers
of `ϖ` is derived complete for `I = (ϖ)`: it receives no nonzero map from an object on which `ϖ`
acts invertibly. -/
lemma derivedComplete_of_isHomotopyLimit_of_smul {T : Scheme.{u}} {ϖ : R}
    (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ}) {F : ℕᵒᵖ ⥤ 𝐃(T)}
    (hF : ∀ n : ℕ, ∃ m : ℕ, ϖ ^ m • 𝟙 (F.obj (op n)) = 0) {c : Cone F}
    (hc : IsHomotopyLimit c) : derivedComplete (Scheme.ProEt.topology T) I c.pt := by
  rw [derivedComplete_iff_rightOrthogonal hϖ hI]
  intro Z f hZ
  exact hc.hom_ext_zero
    (fun n g ↦ by obtain ⟨m, hm⟩ := hF n; exact smulInvertible.hom_eq_zero hZ hm g)
    (fun n g ↦ by
      obtain ⟨m, hm⟩ := hF n
      exact (ObjectProperty.le_shift _ 1 Z hZ).hom_eq_zero hm g) f

/-- The point of a homotopy limit of a tower of `D(T_proét, R)` whose terms are killed by powers
of an integer `N` is derived complete for `I = (ϖ)`, provided a power of `ϖ` is a multiple of
`N`: it receives no nonzero map from an object on which `ϖ` acts invertibly. -/
lemma derivedComplete_of_isHomotopyLimit {T : Scheme.{u}} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R)
    (hI : I = Ideal.span {ϖ}) {N : ℕ} {k : ℕ} {s : R} (hk : ϖ ^ k = s * N)
    {F : ℕᵒᵖ ⥤ 𝐃(T)} (hF : ∀ n : ℕ, ∃ m : ℕ, N ^ m • 𝟙 (F.obj (op n)) = 0) {c : Cone F}
    (hc : IsHomotopyLimit c) : derivedComplete (Scheme.ProEt.topology T) I c.pt := by
  refine derivedComplete_of_isHomotopyLimit_of_smul hϖ hI (fun n ↦ ?_) hc
  obtain ⟨m, hm⟩ := hF n
  refine ⟨k * m, ?_⟩
  rw [pow_mul, hk, mul_pow, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hm, smul_zero]

/-- The image of the reduction tower `K ⊗ᴸ R/Iⁿ` under an `R`-linear functor has derived
complete homotopy limits, for `I = (ϖ)`: its terms are killed by the powers of `ϖ`. -/
lemma derivedComplete_of_isHomotopyLimit_map {T T' : Scheme.{u}} {ϖ : R}
    (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ}) (K : 𝐃(T)) (Φ : 𝐃(T) ⥤ 𝐃(T'))
    [Φ.Linear R] {c : Cone (derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙ Φ)}
    (hc : IsHomotopyLimit c) : derivedComplete (Scheme.ProEt.topology T') I c.pt :=
  derivedComplete_of_isHomotopyLimit_of_smul hϖ hI (fun n ↦ ⟨n,
    smul_id_map_derivedCompletionDiagram_obj (hI ▸ Ideal.mem_span_singleton_self ϖ) K Φ n⟩) hc

variable {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

variable (I) in
/-- The levelwise exchange maps `Ex_{K_n} : p^* Rg_* K_n ⟶ Rh_* e^* K_n` of a commutative square,
for the reductions `K_n = K ⊗ᴸ R/Iⁿ` of `K`, as a morphism of towers. -/
noncomputable def adicBaseChangeTowerMap (sq : CommSq e h g p) (K : 𝐃(T)) :
    derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
        R((g)_*[ModuleCat.{u + 1} R]) ⋙ L((p)^*[ModuleCat.{u + 1} R]) ⟶
      derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
        L((e)^*[ModuleCat.{u + 1} R]) ⋙ R((h)_*[ModuleCat.{u + 1} R]) :=
  Functor.whiskerLeft _ (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} R) sq)

/-- The whiskering of the exchange map `Ex` by the reduction tower is an isomorphism of towers as
soon as every `Ex_{K_n}` is an isomorphism. -/
lemma isIso_whiskerLeft_derivedBaseChangeMap (sq : CommSq e h g p) (K : 𝐃(T))
    (hK : ∀ n : ℕ, IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} R) sq).app
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n)))) :
    IsIso (Functor.whiskerLeft (derivedCompletionDiagram (Scheme.ProEt.topology T) I K)
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} R) sq)) := by
  have (X : ℕᵒᵖ) : IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} R) sq).app
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj X)) := by
    -- `hK X.unop` would make the kernel match `op X.unop` against `X` inside the derived
    -- functors, which unfolds them
    cases X; exact hK _
  exact Functor.isIso_whiskerLeft_of_isIso_app _ _

/-- The levelwise exchange maps form an isomorphism of towers as soon as every `Ex_{K_n}` is an
isomorphism. -/
lemma isIso_adicBaseChangeTowerMap_of_forall (sq : CommSq e h g p) (K : 𝐃(T))
    (hK : ∀ n : ℕ, IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} R) sq).app
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj (op n)))) :
    IsIso (adicBaseChangeTowerMap I sq K) :=
  -- stated separately: proving it directly makes the kernel unfold the derived functors
  isIso_whiskerLeft_derivedBaseChangeMap sq K hK

/-- The derived direct image `Rh_*` commutes with derived limits: it sends a homotopy limit cone
of a tower to a homotopy limit cone of its image. It is a triangulated right adjoint, so it
preserves the Milnor triangle. -/
lemma isHomotopyLimit_mapCone_rightDerivedLowerStar (h : Y ⟶ X) {F : ℕᵒᵖ ⥤ 𝐃(Y)} {c : Cone F}
    (hc : IsHomotopyLimit c) : IsHomotopyLimit (R((h)_*[ModuleCat.{u + 1} R]).mapCone c) :=
  have := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) h).rightAdjoint_preservesLimits
  hc.map _

section IsIso

variable (sq : CommSq e h g p) (K : 𝐃(T)) [IsIso (adicBaseChangeTowerMap I sq K)]

/-- If the levelwise exchange maps `Ex_{K_n}` are isomorphisms, every completed exchange map
`R lim_n p^* Rg_* K_n ⟶ R lim_n Rh_* e^* K_n` is an isomorphism: this is any morphism `u` between
the homotopy limits completing the morphism of Milnor triangles induced by the levelwise exchange
maps. -/
theorem isIso_of_isIso_adicBaseChangeTowerMap
    {PF : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
      R((g)_*[ModuleCat.{u + 1} R]) ⋙ L((p)^*[ModuleCat.{u + 1} R])).obj (op n)}
    (hPF : IsLimit PF)
    {PG : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
      L((e)^*[ModuleCat.{u + 1} R]) ⋙ R((h)_*[ModuleCat.{u + 1} R])).obj (op n)}
    (hPG : IsLimit PG) {A B : 𝐃(X)} {cA : A ⟶ PF.pt} {δA : PF.pt ⟶ A⟦(1 : ℤ)⟧}
    {cB : B ⟶ PG.pt} {δB : PG.pt ⟶ B⟦(1 : ℤ)⟧}
    (hA : Triangle.mk cA (𝟙 _ - towerShift hPF) δA ∈ distTriang _)
    (hB : Triangle.mk cB (𝟙 _ - towerShift hPG) δB ∈ distTriang _) (u : A ⟶ B)
    (hu₁ : cA ≫ productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap I sq K) = u ≫ cB)
    (hu₃ : δA ≫ u⟦(1 : ℤ)⟧' =
      productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap I sq K) ≫ δB) :
    IsIso u :=
  isIso_of_isIso_app hPF hPG hA hB _ u hu₁ hu₃

/-- If the levelwise exchange maps `Ex_{K_n}` are isomorphisms, then for homotopy limit cones
`c₁` of `n ↦ p^* Rg_* K_n` (computing `Lp^*_comp Rg_* K`) and `c₂` of `n ↦ e^* K_n` (computing
`Le^*_comp K`), there is an isomorphism `Lp^*_comp Rg_* K ≅ Rh_* Le^*_comp K` compatible with the
levelwise exchange maps. -/
theorem exists_iso_of_isIso_adicBaseChangeTowerMap
    {c₁ : Cone (derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
      R((g)_*[ModuleCat.{u + 1} R]) ⋙ L((p)^*[ModuleCat.{u + 1} R]))} (hc₁ : IsHomotopyLimit c₁)
    {c₂ : Cone (derivedCompletionDiagram (Scheme.ProEt.topology T) I K ⋙
      L((e)^*[ModuleCat.{u + 1} R]))} (hc₂ : IsHomotopyLimit c₂) :
    ∃ φ : c₁.pt ≅ R((h)_*[ModuleCat.{u + 1} R]).obj c₂.pt, ∀ n : ℕ,
      φ.hom ≫ R((h)_*[ModuleCat.{u + 1} R]).map (c₂.π.app (op n)) =
        c₁.π.app (op n) ≫ (adicBaseChangeTowerMap I sq K).app (op n) :=
  hc₁.exists_iso_of_iso (asIso (adicBaseChangeTowerMap I sq K))
    (c' := R((h)_*[ModuleCat.{u + 1} R]).mapCone c₂)
    (isHomotopyLimit_mapCone_rightDerivedLowerStar h hc₂)

end IsIso

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

/-- The image of the reduction tower `K ⊗ᴸ 𝒪_E/𝔪_Eⁿ` under an `𝒪_E`-linear functor has derived
complete homotopy limits: its terms are killed by the powers of a uniformizer. -/
lemma derivedCompleteIntegral_of_isHomotopyLimit_map {T T' : Scheme.{u}} (K : 𝐃(T))
    (Φ : 𝐃(T) ⥤ 𝐃(T')) [Φ.Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))]
    {c : Cone (derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 K ⋙ Φ)}
    (hc : IsHomotopyLimit c) : derivedCompleteIntegral (Scheme.ProEt.topology T') l E c.pt := by
  obtain ⟨ϖ, hϖ, hI⟩ := PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  exact derivedComplete_of_isHomotopyLimit_map hϖ hI K Φ hc

variable {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The point `R lim_n p^* Rg_* K_n` of a Milnor triangle of the tower `n ↦ p^* Rg_* K_n` lies in
`D_comp(X, 𝒪_E)`. -/
lemma derivedCompleteIntegral_adicSource (g : T ⟶ S) (p : X ⟶ S) (K : 𝐃(T))
    {PF : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 K ⋙
      R((g)_*[𝐌]) ⋙ L((p)^*[𝐌])).obj (op n)}
    (hPF : IsLimit PF) {A : 𝐃(X)} {cA : A ⟶ PF.pt} {δA : PF.pt ⟶ A⟦(1 : ℤ)⟧}
    (hA : Triangle.mk cA (𝟙 _ - towerShift hPF) δA ∈ distTriang _) :
    derivedCompleteIntegral (Scheme.ProEt.topology X) l E A :=
  derivedCompleteIntegral_of_isHomotopyLimit_map l E K (R((g)_*[𝐌]) ⋙ L((p)^*[𝐌]))
    (isHomotopyLimit_coneOfComp hPF hA)

/-- The point `R lim_n Rh_* e^* K_n` of a Milnor triangle of the tower `n ↦ Rh_* e^* K_n` lies in
`D_comp(X, 𝒪_E)`. -/
lemma derivedCompleteIntegral_adicTarget (e : Y ⟶ T) (h : Y ⟶ X) (K : 𝐃(T))
    {PG : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 K ⋙
      L((e)^*[𝐌]) ⋙ R((h)_*[𝐌])).obj (op n)}
    (hPG : IsLimit PG) {B : 𝐃(X)} {cB : B ⟶ PG.pt} {δB : PG.pt ⟶ B⟦(1 : ℤ)⟧}
    (hB : Triangle.mk cB (𝟙 _ - towerShift hPG) δB ∈ distTriang _) :
    derivedCompleteIntegral (Scheme.ProEt.topology X) l E B :=
  derivedCompleteIntegral_of_isHomotopyLimit_map l E K (L((e)^*[𝐌]) ⋙ R((h)_*[𝐌]))
    (isHomotopyLimit_coneOfComp hPG hB)

/-- If the levelwise exchange maps `Ex_{K_n}` of an object `K` of `D(T_proét, 𝒪_E)` are
isomorphisms, every completed exchange map `u : R lim_n p^* Rg_* K_n ⟶ R lim_n Rh_* e^* K_n`
becomes an isomorphism in `D_comp(X, E)`, being one in `D_comp(X, 𝒪_E)`. -/
theorem isIso_fromIntegral_map_of_isIso_adicBaseChangeTowerMap (sq : CommSq e h g p) (K : 𝐃(T))
    [IsIso (adicBaseChangeTowerMap 𝔪 sq K)]
    {PF : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 K ⋙
      R((g)_*[𝐌]) ⋙ L((p)^*[𝐌])).obj (op n)}
    (hPF : IsLimit PF)
    {PG : Fan fun n : ℕ ↦ (derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 K ⋙
      L((e)^*[𝐌]) ⋙ R((h)_*[𝐌])).obj (op n)}
    (hPG : IsLimit PG) {A B : 𝐃(X)} {cA : A ⟶ PF.pt} {δA : PF.pt ⟶ A⟦(1 : ℤ)⟧}
    {cB : B ⟶ PG.pt} {δB : PG.pt ⟶ B⟦(1 : ℤ)⟧}
    (hA : Triangle.mk cA (𝟙 _ - towerShift hPF) δA ∈ distTriang _)
    (hB : Triangle.mk cB (𝟙 _ - towerShift hPG) δB ∈ distTriang _) (u : A ⟶ B)
    (hu₁ : cA ≫ productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap 𝔪 sq K) = u ≫ cB)
    (hu₃ : δA ≫ u⟦(1 : ℤ)⟧' =
      productTowerMap (PF := PF) hPG (adicBaseChangeTowerMap 𝔪 sq K) ≫ δB) :
    IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E).map
      (ObjectProperty.homMk (P := derivedCompleteIntegral (Scheme.ProEt.topology X) l E)
        (X := ⟨A, derivedCompleteIntegral_adicSource l E g p K hPF hA⟩)
        (Y := ⟨B, derivedCompleteIntegral_adicTarget l E e h K hPG hB⟩) u)) := by
  have : IsIso u := isIso_of_isIso_adicBaseChangeTowerMap sq K hPF hPG hA hB u hu₁ hu₃
  have : IsIso ((derivedCompleteIntegral (Scheme.ProEt.topology X) l E).ι.map
      (ObjectProperty.homMk (P := derivedCompleteIntegral (Scheme.ProEt.topology X) l E)
        (X := ⟨A, derivedCompleteIntegral_adicSource l E g p K hPF hA⟩)
        (Y := ⟨B, derivedCompleteIntegral_adicTarget l E e h K hPG hB⟩) u)) := this
  have : IsIso (ObjectProperty.homMk (P := derivedCompleteIntegral (Scheme.ProEt.topology X) l E)
      (X := ⟨A, derivedCompleteIntegral_adicSource l E g p K hPF hA⟩)
      (Y := ⟨B, derivedCompleteIntegral_adicTarget l E e h K hPG hB⟩) u) :=
    isIso_of_reflects_iso _ (derivedCompleteIntegral (Scheme.ProEt.topology X) l E).ι
  exact Functor.map_isIso _ _

/-- The objects of `D(T_proét, 𝒪_E)` of étale origin with bounded constructible cohomology in
the interval `[a, b]`. -/
def DerivedCategory.boundedConstructibleIn (T : Scheme.{u}) (a b : ℤ) : ObjectProperty 𝐃(T) :=
  fun M ↦ ProEtale.DerivedCategory.boundedConstructible 𝐌 T M ∧ TStructure.t.IsGE M a ∧
    TStructure.t.IsLE M b

/-- An *integral lattice* for an object `K` of `D_comp(T, E)` is an object `L` of
`Dᵇc(T_proét, 𝒪_E)` (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleComplete`)
together with an isomorphism `L[1/ϖ] ≅ K`.

The blueprint asks for this isomorphism in `Dᵇc(T, E)`, the rationalization of
`Dᵇc(T_proét, 𝒪_E)`; this is a full subcategory of `D_comp(T, E)` (the rationalization of a fully
faithful triangulated functor is fully faithful, `CategoryTheory.Rationalization.full_map` and
`CategoryTheory.Rationalization.faithful_map`), so that an isomorphism in `Dᵇc(T, E)` is the same
as one in `D_comp(T, E)`, and the objects of `D_comp(T, E)` admitting a lattice are those of
`Dᵇc(T, E)`. -/
structure IntegralLattice {T : Scheme.{u}}
    (K : DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology T) l E) where
  /-- The lattice `L ∈ Dᵇc(T_proét, 𝒪_E)`. -/
  obj : 𝐃(T)
  /-- The lattice lies in `Dᵇc(T_proét, 𝒪_E)`. -/
  mem : DerivedCategory.boundedConstructibleComplete 𝔪 T obj
  /-- The isomorphism `L[1/ϖ] ≅ K` in `D_comp(T, E)`. -/
  iso : (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology T) l E).obj
    ⟨obj, mem.1⟩ ≅ K

namespace IntegralLattice

variable {l E} {K : DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology T) l E}

/-- A lattice is *finite-level étale admissible* if each reduction `L_n = L ⊗ᴸ 𝒪_E/𝔪_Eⁿ` is of
étale origin with bounded constructible cohomology. -/
def IsFiniteLevelEtaleAdmissible (Λ : IntegralLattice l E K) : Prop :=
  DerivedCategory.ReductionsBoundedConstructible 𝔪 T Λ.obj

/-- Every integral lattice is finite-level étale admissible: in this formalisation the étale
origin of the reductions is part of the definition of `Dᵇc(T_proét, 𝒪_E)`, as it is in the
blueprint. -/
lemma isFiniteLevelEtaleAdmissible (Λ : IntegralLattice l E K) :
    Λ.IsFiniteLevelEtaleAdmissible :=
  Λ.mem.reductionsBoundedConstructible

/-- A lattice is *square-constructibly admissible* for a commutative square `sq` if the four
finite-level systems `Rg_* L_n`, `Lp^* Rg_* L_n`, `Le^* L_n` and `Rh_* Le^* L_n` are of étale
origin with bounded constructible cohomology in one common finite interval `[a, b]` (it is
finite-level étale admissible by
`AlgebraicGeometry.ProEtale.IntegralLattice.isFiniteLevelEtaleAdmissible`). -/
def IsSquareConstructiblyAdmissible (Λ : IntegralLattice l E K) (_ : CommSq e h g p) : Prop :=
  ∃ a b : ℤ, ∀ n : ℕ,
    DerivedCategory.boundedConstructibleIn l E S a b (R((g)_*[𝐌]).obj
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj).obj (op n))) ∧
    DerivedCategory.boundedConstructibleIn l E X a b (L((p)^*[𝐌]).obj (R((g)_*[𝐌]).obj
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj).obj (op n)))) ∧
    DerivedCategory.boundedConstructibleIn l E Y a b (L((e)^*[𝐌]).obj
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj).obj (op n))) ∧
    DerivedCategory.boundedConstructibleIn l E X a b (R((h)_*[𝐌]).obj (L((e)^*[𝐌]).obj
      ((derivedCompletionDiagram (Scheme.ProEt.topology T) 𝔪 Λ.obj).obj (op n))))

end IntegralLattice

end ECoefficient

end AlgebraicGeometry.ProEtale
